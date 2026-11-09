import PredictionDepth.FrozenPascal.Resources
import PredictionDepth.Complexity.UniformCompositionSemantics
import CslibFrontier.Computability.Circuit.Boolean.Substitution

/-!
# A bounded path witness for the frozen-control rule

An exponent is encoded by a one-hot tag only in the selected time window.
Squaring and multiplying by the seed move its active wire to twice its position
and one position to the right, respectively. The decoder uses the active tag
to select the exponent's binomial-parity coefficients.
-/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open StandardComplexity.UniformComposition

def realization {Q : Type*} (stay hop : Q → Bool) :
    Realization (Config Q) ℕ (step stay hop) where
  identity := 0
  seed := 1
  compose := Nat.add
  denote := fun u => (step stay hop)^[u]
  identity_correct := rfl
  seed_correct := Function.iterate_one _
  compose_correct := fun u v => Function.iterate_add _ u v

@[simp] theorem run_realization (stay hop : Q → Bool) (p : Program) :
    p.run (realization stay hop) = p.exponent := by
  induction p with
  | identity => rfl
  | square p ih => simpa [Program.run, Program.exponent, realization] using congrArg (fun u : ℕ => u + u) ih
  | multiplySeed p ih =>
    change 1 + p.run (realization stay hop) = p.exponent + 1
    rw [ih, Nat.add_comm]

def initialRoute (m : ℕ) : Fin (RegisterWidth m) → Fin (InputWidth m) ⊕ Bool :=
  Fin.addCases (fun j : Fin m => .inr (decide (j.val = 0))) Sum.inl

def squareSource (j : Fin m) : Option (Fin m) :=
  if j.val % 2 = 0 then some ⟨j.val / 2, (Nat.div_le_self _ _).trans_lt j.isLt⟩
  else none

def incrementSource (j : Fin m) : Option (Fin m) :=
  if j.val = 0 then none else some ⟨j.val - 1, by omega⟩

def route (source : Fin m → Option (Fin m)) :
    Fin (RegisterWidth m) → Fin (RegisterWidth m) ⊕ Bool :=
  Fin.addCases (fun j => (source j).elim (.inr false) (fun i => .inl (timeWire i)))
    (fun j => .inl (trackWire j))

def initCircuit (m : ℕ) : Gates (InputWidth m) (RegisterWidth m) :=
  substituteCircuit (initialRoute m)

def square (m : ℕ) : Gates (RegisterWidth m) (RegisterWidth m) :=
  substituteCircuit (route (squareSource (m := m)))

def increment (m : ℕ) : Gates (RegisterWidth m) (RegisterWidth m) :=
  substituteCircuit (route (incrementSource (m := m)))

theorem initialize_eval (m : ℕ) (x : Bits (InputWidth m)) :
    (initCircuit m).eval interpretation x = register m 0 x := by
  rw [initCircuit, eval_substituteCircuit]
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [initialRoute, substitute, register, joinBits, timeTag]
  · simp [initialRoute, substitute, register, joinBits]

theorem square_eval (m u : ℕ) (x : Bits (InputWidth m)) :
    (square m).eval interpretation (register m u x) = register m (u + u) x := by
  rw [square, eval_substituteCircuit]
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · change substitute (route squareSource) (register m u x) (timeWire i) =
        register m (u + u) x (timeWire i)
    rw [register_time]
    have hr : route squareSource (timeWire i) =
        (squareSource i).elim (.inr false) (fun j => .inl (timeWire j)) := by
      simp [route, timeWire]
    rw [substitute, hr]
    unfold squareSource
    split_ifs with h
    · simp only [Option.elim_some, Sum.elim_inl, register_time]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
    · simp only [Option.elim_none, Sum.elim_inr]
      symm
      exact decide_eq_false (by omega)
  · simp [route, substitute, trackWire, register, joinBits]

theorem increment_eval (m u : ℕ) (x : Bits (InputWidth m)) :
    (increment m).eval interpretation (register m u x) = register m (u + 1) x := by
  rw [increment, eval_substituteCircuit]
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · change substitute (route incrementSource) (register m u x) (timeWire i) =
        register m (u + 1) x (timeWire i)
    rw [register_time]
    have hr : route incrementSource (timeWire i) =
        (incrementSource i).elim (.inr false) (fun j => .inl (timeWire j)) := by
      simp [route, timeWire]
    rw [substitute, hr]
    unfold incrementSource
    split_ifs with h
    · simp [h]
    · simp only [Option.elim_some, Sum.elim_inl, register_time]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
  · simp [route, substitute, trackWire, register, joinBits]

theorem valid_path (m : ℕ) (p : Program) (ops : List Instruction) :
    RegisterValidFor (realization Prod.fst Prod.snd) (register m)
      (square m) (increment m) p ops := by
  induction ops generalizing p with
  | nil => trivial
  | cons op ops ih =>
    refine ⟨?_, ih (op.advance p)⟩
    intro x
    cases op with
    | square => simpa [circuitFor, Instruction.advance, Program.exponent] using square_eval m p.exponent x
    | multiplySeed =>
      simpa [circuitFor, Instruction.advance, Program.exponent] using increment_eval m p.exponent x
    | keep => rfl

def observe (x : Config (Bool × Bool)) : Bool := ofBoolRing (x.2 0)

/-- The original path criterion instantiated for the full frozen-control rule. -/
def witness (m T : ℕ) (hT : T < m) :
    RegisterWitness (W := RegisterWidth m) (realization Prod.fst Prod.snd)
      (initial (m := m)) observe (binaryDigits T) where
  register := register m
  initialization := initCircuit m
  square := square m
  multiplySeed := increment m
  observation := decoder m
  initialization_correct := initialize_eval m
  path_correct := valid_path m .identity _
  observation_correct := by
    intro x
    have ht : (compileBits (binaryDigits T)).run (realization Prod.fst Prod.snd) = T := by
      rw [run_realization, compileBits_exponent, binaryDigits_value]
    rw [ht]
    apply bit_injective
    change bit ((decoder m).eval interpretation (register m T x) 0) =
      bit (ofBoolRing (((step Prod.fst Prod.snd)^[T] (initial x)).2 0))
    rw [bit_ofBoolRing]
    exact decoder_eval x ⟨T, hT⟩

def predictionCircuit (T : ℕ) : Gates (InputWidth (T + 1)) 1 :=
  (witness (T + 1) T (Nat.lt_succ_self T)).circuit

theorem predictionCircuit_correct (T : ℕ) (x : Bits (InputWidth (T + 1))) :
    (predictionCircuit T).eval interpretation x 0 =
      observe ((step Prod.fst Prod.snd)^[T] (initial x)) :=
  (witness (T + 1) T (Nat.lt_succ_self T)).circuit_at_time_correct x

theorem predictionCircuit_depth (T : ℕ) :
    (predictionCircuit T).depth ≤ 7 + 33 * Nat.clog 2 (T + 2) := by
  let m := T + 1
  have h := predictor_logarithmic_depth (initCircuit m) (square m) (increment m) (decoder m) T
  have hi : (initCircuit m).depth ≤ 1 := depth_substituteCircuit_le _
  have hs : (square m).depth ≤ 1 := depth_substituteCircuit_le _
  have hm : (increment m).depth ≤ 1 := depth_substituteCircuit_le _
  have hmax : max (square m).depth (increment m).depth + 1 ≤ 2 := by
    have := max_le hs hm
    omega
  have hstage := Nat.mul_le_mul_left (2 * Nat.clog 2 (T + 1)) hmax
  have ho := decoder_depth m
  have hlog := Nat.clog_mono_right 2 (show T + 1 ≤ T + 2 by omega)
  change (predictionCircuit T).depth ≤ _ at h
  change (decoder m).depth ≤ 5 + 29 * Nat.clog 2 (T + 2) at ho
  omega

theorem predictionCircuit_size (T : ℕ) :
    (predictionCircuit T).size ≤ 113 * (T + 2) ^ 4 := by
  let m := T + 1
  let b := T + 2
  have h := predictor_size_le (initCircuit m) (square m) (increment m) (decoder m)
    (binaryDigits T)
  have ho : (decoder m).size ≤ 87 * b ^ 4 := decoder_size m
  have hl := clog_le_self (T + 1)
  have hstage : 2 * Nat.clog 2 (T + 1) * (2 + RegisterWidth m) ≤ 12 * b ^ 2 := by
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hl)
      (show 2 + RegisterWidth m ≤ 6 * b by dsimp only [RegisterWidth, InputWidth, m, b]; omega)
    calc
      _ ≤ 2 * (T + 1) * (6 * b) := hm
      _ ≤ 2 * b * (6 * b) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by omega))
      _ = _ := by ring
  have hb : 1 ≤ b := by omega
  have hb₂ : b ≤ b ^ 2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb (by decide : 1 ≤ 2)
  have hb₄ : b ^ 2 ≤ b ^ 4 := Nat.pow_le_pow_right hb (by decide : 2 ≤ 4)
  have hu : 1 ≤ b ^ 4 := Nat.one_le_pow _ _ hb
  simp only [initCircuit, square, increment, size_substituteCircuit, max_self] at h
  rw [← bitLength, bitLength_eq_clog] at h
  have hbreg : RegisterWidth m ≤ 4 * b := by dsimp only [RegisterWidth, InputWidth, m, b]; omega
  change (predictionCircuit T).size ≤ _ at h
  change (predictionCircuit T).size ≤ 113 * b ^ 4
  nlinarith

end PredictionDepth.FrozenPascal
