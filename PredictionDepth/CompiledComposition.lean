import PredictionDepth.FastComposition
import PredictionDepth.Circuit
import Mathlib.Data.Fin.Basic

/-!
# Compiling fast composition to bounded-fan-in Boolean circuits

`BinaryCircuit` is a concrete circuit syntax: its only computational primitive
is a binary Boolean gate. Wires, constants, fan-out, sequential composition,
and parallel outputs are explicit. Sequential composition connects a subcircuit
once, so a repeated square shares its accumulator rather than duplicating it.

An `Implementation` supplies actual finite-width circuits for the representation
operations. The compiler proves semantic correctness and additive size/depth
bounds; it does not merely attach resource labels to arbitrary functions.
-/

namespace PredictionDepth.FastComposition

abbrev Bits (n : ℕ) := Fin n → Bool

def joinBits {m n : ℕ} (x : Bits m) (y : Bits n) : Bits (m + n) :=
  Fin.addCases x y

@[simp] theorem joinBits_left {m n : ℕ} (x : Bits m) (y : Bits n) (i : Fin m) :
    joinBits x y (Fin.castAdd n i) = x i := by simp [joinBits]

@[simp] theorem joinBits_right {m n : ℕ} (x : Bits m) (y : Bits n) (i : Fin n) :
    joinBits x y (Fin.natAdd m i) = y i := by simp [joinBits]

/-- Compositional Boolean DAGs, with free constants/wires and binary gates.
The `parallel` constructor shares its input wires, while `seq` uses each
subcircuit once. Thus the gate count is that of a DAG, not its formula unfolding. -/
inductive BinaryCircuit : ℕ → ℕ → Type
  | wire {n m : ℕ} (w : Fin m → Sum Bool (Fin n)) : BinaryCircuit n m
  | gate (op : Bool → Bool → Bool) : BinaryCircuit 2 1
  | seq {n m k : ℕ} (first : BinaryCircuit n m) (second : BinaryCircuit m k) :
      BinaryCircuit n k
  | parallel {n m k : ℕ} (left : BinaryCircuit n m) (right : BinaryCircuit n k) :
      BinaryCircuit n (m + k)

namespace BinaryCircuit

def eval {n m : ℕ} : BinaryCircuit n m → Bits n → Bits m
  | .wire w, x => fun i => match w i with | .inl b => b | .inr j => x j
  | .gate op, x => fun _ => op (x 0) (x 1)
  | .seq a b, x => b.eval (a.eval x)
  | .parallel a b, x => joinBits (a.eval x) (b.eval x)

def depth {n m : ℕ} : BinaryCircuit n m → ℕ
  | .wire _ => 0
  | .gate _ => 1
  | .seq a b => a.depth + b.depth
  | .parallel a b => max a.depth b.depth

def gateCount {n m : ℕ} : BinaryCircuit n m → ℕ
  | .wire _ => 0
  | .gate _ => 1
  | .seq a b => a.gateCount + b.gateCount
  | .parallel a b => a.gateCount + b.gateCount

/-- Number of syntax and wiring entries. Unlike `gateCount`, this also charges
for constants, wiring tables, and composition nodes. Wire indices themselves
use logarithmic space in the relevant port width. -/
def descriptionSize {n m : ℕ} : BinaryCircuit n m → ℕ
  | @wire _ m _ => 1 + m
  | .gate _ => 1
  | .seq a b => 1 + a.descriptionSize + b.descriptionSize
  | .parallel a b => 1 + a.descriptionSize + b.descriptionSize

/-- Select and duplicate any input wires without adding a gate. -/
def select {n m : ℕ} (f : Fin m → Fin n) : BinaryCircuit n m := .wire (.inr ∘ f)

@[simp] theorem select_eval {n m : ℕ} (f : Fin m → Fin n) (x : Bits n) :
    (select f).eval x = x ∘ f := rfl

/-- Hardwired finite constants; construction uniformity is a separate family property. -/
def constant {n m : ℕ} (x : Bits m) : BinaryCircuit n m := .wire (.inl ∘ x)

@[simp] theorem constant_eval {n m : ℕ} (x : Bits m) (y : Bits n) :
    (constant x).eval y = x := rfl

/-- Pad a formula with binary projection gates. This is used only when
unfolding; it does not change the DAG resource bounds above. -/
def pad {n d : ℕ} (c : BoundedCircuit 2 n d) :
    (k : ℕ) → BoundedCircuit 2 n (d + k)
  | 0 => c
  | k + 1 => .gate (fun v => v 0) (fun _ => pad c k)

@[simp] theorem pad_eval {n d : ℕ} (c : BoundedCircuit 2 n d) (k : ℕ)
    (x : Bits n) : (pad c k).eval x = c.eval x := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem eval_cast {n d e : ℕ} (h : d = e) (c : BoundedCircuit 2 n d) (x : Bits n) :
    (cast (congrArg (BoundedCircuit 2 n) h) c).eval x = c.eval x := by
  subst e
  rfl

def weaken {n d e : ℕ} (c : BoundedCircuit 2 n d) (h : d ≤ e) :
    BoundedCircuit 2 n e :=
  cast (congrArg (BoundedCircuit 2 n) (Nat.add_sub_of_le h)) (pad c (e - d))

@[simp] theorem weaken_eval {n d e : ℕ} (c : BoundedCircuit 2 n d) (h : d ≤ e)
    (x : Bits n) : (weaken c h).eval x = c.eval x := by
  exact (eval_cast (Nat.add_sub_of_le h) (pad c (e - d)) x).trans (pad_eval c (e - d) x)

/-- Substitution expands sharing only in the proof model, with additive depth. -/
def substitute {m n e : ℕ} : {d : ℕ} → BoundedCircuit 2 m d →
    (Fin m → BoundedCircuit 2 n e) → BoundedCircuit 2 n (e + d)
  | d, .input i, args => pad (args i) d
  | _, .constant v, _ => .constant v
  | _, .gate op cs, args => .gate op (fun i => substitute (cs i) args)

@[simp] theorem substitute_eval {m n d e : ℕ} (c : BoundedCircuit 2 m d)
    (args : Fin m → BoundedCircuit 2 n e) (x : Bits n) :
    (substitute c args).eval x = c.eval (fun i => (args i).eval x) := by
  induction c with
  | input i => exact pad_eval _ _ _
  | constant v => rfl
  | gate op cs ih =>
      change op (fun i => (substitute (cs i) args).eval x) =
        op (fun i => (cs i).eval (fun j => (args j).eval x))
      congr 1
      funext i
      exact ih i

/-- Unfold one output of a compositional DAG to the fan-in-two model used
for the dependency lower bound. Depth is preserved; size need not be. -/
def unfoldOutput {n m : ℕ} (c : BinaryCircuit n m) :
    Fin m → BoundedCircuit 2 n c.depth :=
  match c with
  | .wire w => fun i => match w i with | .inl v => .constant v | .inr j => .input j
  | .gate op => fun _ => .gate (fun v => op (v 0) (v 1)) (fun i => .input i)
  | .seq a b => fun i => substitute (unfoldOutput b i) (unfoldOutput a)
  | .parallel a b =>
      Fin.addCases (fun i => weaken (unfoldOutput a i) (Nat.le_max_left _ _))
        (fun i => weaken (unfoldOutput b i) (Nat.le_max_right _ _))

theorem unfoldOutput_eval {n m : ℕ} (c : BinaryCircuit n m) (i : Fin m)
    (x : Bits n) : (c.unfoldOutput i).eval x = c.eval x i := by
  induction c with
  | wire w => simp only [unfoldOutput, eval]; cases w i <;> rfl
  | gate op => rfl
  | seq a b ia ib =>
      simp only [unfoldOutput, depth, eval, substitute_eval]
      have ha : (fun j => (a.unfoldOutput j).eval x) = a.eval x := by
        funext j
        exact ia j x
      rw [ha]
      exact ib i (a.eval x)
  | parallel a b ia ib =>
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [unfoldOutput, depth, eval, Fin.addCases_left, weaken_eval, joinBits_left] using ia j x
      · intro j
        simpa only [unfoldOutput, depth, eval, Fin.addCases_right, weaken_eval, joinBits_right] using ib j x

/-- Theorem C also applies to every output of the Boolean DAG model in A. -/
theorem essential_depth_lower_bound {n m : ℕ} (c : BinaryCircuit n m) (i : Fin m) :
    Nat.clog 2 (essentialInputs (fun x => c.eval x i)).card ≤ c.depth := by
  have h := (c.unfoldOutput i).essential_depth_lower_bound (by decide)
  have he : (c.unfoldOutput i).eval = fun x => c.eval x i := by
    funext x
    exact c.unfoldOutput_eval i x
  simpa only [he] using h

end BinaryCircuit

/-- The three register blocks: immutable seed, accumulator, original input. -/
abbrev Registers (L n : ℕ) := Bits (L + (L + n))

def registers {L n : ℕ} (seed acc : Bits L) (x : Bits n) : Registers L n :=
  joinBits seed (joinBits acc x)

def seedIndex {L n : ℕ} (i : Fin L) : Fin (L + (L + n)) := Fin.castAdd (L + n) i
def accIndex {L n : ℕ} (i : Fin L) : Fin (L + (L + n)) :=
  Fin.natAdd L (Fin.castAdd n i)
def inputIndex {L n : ℕ} (i : Fin n) : Fin (L + (L + n)) :=
  Fin.natAdd L (Fin.natAdd L i)

@[simp] theorem registers_seed {L n : ℕ} (seed acc : Bits L) (x : Bits n) (i : Fin L) :
    registers seed acc x (seedIndex i) = seed i := by simp [registers, seedIndex]
@[simp] theorem registers_acc {L n : ℕ} (seed acc : Bits L) (x : Bits n) (i : Fin L) :
    registers seed acc x (accIndex i) = acc i := by simp [registers, accIndex]
@[simp] theorem registers_input {L n : ℕ} (seed acc : Bits L) (x : Bits n) (i : Fin n) :
    registers seed acc x (inputIndex i) = x i := by simp [registers, inputIndex]

/-- Actual primitive implementations for a fixed input length and representation width.
Finite-width closure is built into `encode` and `compose_correct`; no run-time
intermediate representation is allowed to grow beyond `L` bits.

The initialization circuit includes all costs of preparing seed and identity
while retaining the original input. -/
structure Implementation {n : ℕ} {R : Type*} {F : Bits n → Bits n}
    (r : Realization (Bits n) R F) (observe : Bits n → Bool) (L : ℕ) where
  encode : R → Bits L
  initialization : BinaryCircuit n (L + (L + n))
  initialization_correct : ∀ x, initialization.eval x = registers (encode r.seed) (encode r.identity) x
  composition : BinaryCircuit (L + L) L
  composition_correct : ∀ a b,
    composition.eval (joinBits (encode a) (encode b)) = encode (r.compose a b)
  observation : BinaryCircuit (L + n) 1
  observation_correct : ∀ a x,
    observation.eval (joinBits (encode a) x) 0 = observe (r.denote a x)

namespace Implementation

variable {n L : ℕ} {R : Type*} {F : Bits n → Bits n}
  {r : Realization (Bits n) R F} {observe : Bits n → Bool}

/-- Wiring for a composition call. Squaring duplicates accumulator wires;
seed multiplication selects seed and accumulator. -/
def argumentWires (useSeed : Bool) : BinaryCircuit (L + (L + n)) (L + L) :=
  BinaryCircuit.select (Fin.addCases (if useSeed then seedIndex else accIndex) accIndex)

theorem argumentWires_eval (useSeed : Bool) (seed acc : Bits L) (x : Bits n) :
    (argumentWires useSeed).eval (registers seed acc x) =
      joinBits (if useSeed then seed else acc) acc := by
  funext i
  refine Fin.addCases (m := L) (n := L) ?_ ?_ i
  · intro j
    cases useSeed <;> simp [argumentWires, BinaryCircuit.select, BinaryCircuit.eval,
      Function.comp_def, joinBits]
  · intro j
    change registers seed acc x
      (Fin.addCases (if useSeed then seedIndex else accIndex) accIndex (Fin.natAdd L j)) =
      joinBits (if useSeed then seed else acc) acc (Fin.natAdd L j)
    rw [Fin.addCases_right, joinBits_right, registers_acc]

def stage (I : Implementation r observe L) (useSeed : Bool) :
    BinaryCircuit (L + (L + n)) (L + (L + n)) :=
  .parallel (BinaryCircuit.select seedIndex)
    (.parallel (.seq (argumentWires useSeed) I.composition) (BinaryCircuit.select inputIndex))

theorem stage_eval (I : Implementation r observe L) (useSeed : Bool) (a : R) (x : Bits n) :
    (I.stage useSeed).eval (registers (I.encode r.seed) (I.encode a) x) =
      registers (I.encode r.seed)
        (I.encode (r.compose (if useSeed then r.seed else a) a)) x := by
  simp only [stage, BinaryCircuit.eval, argumentWires_eval]
  have hs : (fun i => registers (I.encode r.seed) (I.encode a) x (seedIndex i)) =
      I.encode r.seed := by funext i; simp
  have hx : (fun i => registers (I.encode r.seed) (I.encode a) x (inputIndex i)) = x := by
    funext i; simp
  change joinBits _ (joinBits _ _) = _
  simp only [BinaryCircuit.select_eval, Function.comp_def, hs, hx]
  cases useSeed <;> simp only [Bool.false_eq_true, ↓reduceIte, I.composition_correct,
    registers]

@[simp] theorem stage_depth (I : Implementation r observe L) (useSeed : Bool) :
    (I.stage useSeed).depth = I.composition.depth := by
  simp [stage, argumentWires, BinaryCircuit.select, BinaryCircuit.depth]

@[simp] theorem stage_gateCount (I : Implementation r observe L) (useSeed : Bool) :
    (I.stage useSeed).gateCount = I.composition.gateCount := by
  simp [stage, argumentWires, BinaryCircuit.select, BinaryCircuit.gateCount]

@[simp] theorem stage_descriptionSize (I : Implementation r observe L) (useSeed : Bool) :
    (I.stage useSeed).descriptionSize = I.composition.descriptionSize + 3 * L + n + 6 := by
  simp only [stage, argumentWires, BinaryCircuit.select, BinaryCircuit.descriptionSize]
  omega

/-- Compile the shared-register program. The recursive prefix occurs once. -/
def compileProgram (I : Implementation r observe L) : Program → BinaryCircuit n (L + (L + n))
  | .identity => I.initialization
  | .square p => .seq (I.compileProgram p) (I.stage false)
  | .multiplySeed p => .seq (I.compileProgram p) (I.stage true)

theorem compileProgram_eval (I : Implementation r observe L) (p : Program) (x : Bits n) :
    (I.compileProgram p).eval x = registers (I.encode r.seed) (I.encode (p.run r)) x := by
  induction p with
  | identity => exact I.initialization_correct x
  | square p ih =>
    simp only [compileProgram, BinaryCircuit.eval, ih, stage_eval, Bool.false_eq_true,
      ↓reduceIte, Program.run]
  | multiplySeed p ih =>
    simp only [compileProgram, BinaryCircuit.eval, ih, stage_eval,
      ↓reduceIte, Program.run]

theorem compileProgram_depth (I : Implementation r observe L) (p : Program) :
    (I.compileProgram p).depth = I.initialization.depth + p.operations * I.composition.depth := by
  induction p with
  | identity => simp [compileProgram, Program.operations]
  | square p ih => simp [compileProgram, BinaryCircuit.depth, ih, Program.operations,
      Nat.add_mul, Nat.add_assoc]
  | multiplySeed p ih => simp [compileProgram, BinaryCircuit.depth, ih, Program.operations,
      Nat.add_mul, Nat.add_assoc]

theorem compileProgram_gateCount (I : Implementation r observe L) (p : Program) :
    (I.compileProgram p).gateCount =
      I.initialization.gateCount + p.operations * I.composition.gateCount := by
  induction p with
  | identity => simp [compileProgram, Program.operations]
  | square p ih => simp [compileProgram, BinaryCircuit.gateCount, ih, Program.operations,
      Nat.add_mul, Nat.add_assoc]
  | multiplySeed p ih => simp [compileProgram, BinaryCircuit.gateCount, ih, Program.operations,
      Nat.add_mul, Nat.add_assoc]

theorem compileProgram_descriptionSize (I : Implementation r observe L) (p : Program) :
    (I.compileProgram p).descriptionSize = I.initialization.descriptionSize +
      p.operations * (I.composition.descriptionSize + 3 * L + n + 7) := by
  induction p with
  | identity => simp [compileProgram, Program.operations]
  | square p ih =>
      simp only [compileProgram, BinaryCircuit.descriptionSize, ih, stage_descriptionSize,
        Program.operations, Nat.add_mul, Nat.one_mul]
      omega
  | multiplySeed p ih =>
      simp only [compileProgram, BinaryCircuit.descriptionSize, ih, stage_descriptionSize,
        Program.operations, Nat.add_mul, Nat.one_mul]
      omega

def observationWires : BinaryCircuit (L + (L + n)) (L + n) :=
  BinaryCircuit.select (Fin.addCases accIndex inputIndex)

theorem observationWires_eval (seed acc : Bits L) (x : Bits n) :
    observationWires.eval (registers seed acc x) = joinBits acc x := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [observationWires, BinaryCircuit.select, BinaryCircuit.eval, joinBits]
  · intro j; simp [observationWires, BinaryCircuit.select, BinaryCircuit.eval, joinBits]

/-- The final binary Boolean circuit for time `T`. -/
def predictor (I : Implementation r observe L) (T : ℕ) : BinaryCircuit n 1 :=
  .seq (I.compileProgram (compile T)) (.seq observationWires I.observation)

/-- Theorem A: the constructed bounded-fan-in circuit predicts exactly. -/
theorem predictor_correct (I : Implementation r observe L) (T : ℕ) (x : Bits n) :
    (I.predictor T).eval x 0 = observe (F^[T] x) := by
  simp only [predictor, BinaryCircuit.eval, I.compileProgram_eval, observationWires_eval,
    I.observation_correct]
  exact fast_prediction_correct r observe T x

/-- Theorem A: actual Boolean depth, including preparation and observation. -/
theorem predictor_depth_le (I : Implementation r observe L) (T : ℕ) :
    (I.predictor T).depth ≤ I.initialization.depth +
      2 * Nat.clog 2 (T + 1) * I.composition.depth + I.observation.depth := by
  simp only [predictor, BinaryCircuit.depth, compileProgram_depth,
    observationWires, BinaryCircuit.select]
  simp only [Nat.zero_add]
  have h := Nat.mul_le_mul_right I.composition.depth (compile_operations T)
  rw [bitLength_eq_clog] at h
  omega

/-- Theorem A: additive circuit size. Shared squaring does not duplicate the prefix. -/
theorem predictor_gateCount_le (I : Implementation r observe L) (T : ℕ) :
    (I.predictor T).gateCount ≤ I.initialization.gateCount +
      2 * Nat.clog 2 (T + 1) * I.composition.gateCount + I.observation.gateCount := by
  simp only [predictor, BinaryCircuit.gateCount, compileProgram_gateCount,
    observationWires, BinaryCircuit.select]
  simp only [Nat.zero_add]
  have h := Nat.mul_le_mul_right I.composition.gateCount (compile_operations T)
  rw [bitLength_eq_clog] at h
  omega

/-- Wiring tables and composition syntax also remain small. Together with
polynomial representation width and primitive descriptions, this bounds the
complete generated description, not just its computational gates. -/
theorem predictor_descriptionSize_le (I : Implementation r observe L) (T : ℕ) :
    (I.predictor T).descriptionSize ≤ I.initialization.descriptionSize +
      2 * Nat.clog 2 (T + 1) * (I.composition.descriptionSize + 3 * L + n + 7) +
      I.observation.descriptionSize + L + n + 3 := by
  simp only [predictor, BinaryCircuit.descriptionSize, compileProgram_descriptionSize,
    observationWires, BinaryCircuit.select]
  have h := Nat.mul_le_mul_right (I.composition.descriptionSize + 3 * L + n + 7)
    (compile_operations T)
  rw [bitLength_eq_clog] at h
  omega

/-- The constructed predictor also inhabits the common fan-in-two, depth-indexed
circuit model. The efficient size bound is retained on the shared DAG itself;
this formula unfolding is used solely to connect the two semantic models. -/
theorem exists_prediction_circuit (I : Implementation r observe L) (T : ℕ) :
    ∃ c : BoundedCircuit 2 n (I.initialization.depth +
        2 * Nat.clog 2 (T + 1) * I.composition.depth + I.observation.depth),
      c.eval = fun x => observe (F^[T] x) := by
  refine ⟨BinaryCircuit.weaken ((I.predictor T).unfoldOutput 0)
    (I.predictor_depth_le T), ?_⟩
  funext x
  rw [BinaryCircuit.weaken_eval, BinaryCircuit.unfoldOutput_eval]
  exact I.predictor_correct T x

end Implementation
end PredictionDepth.FastComposition
