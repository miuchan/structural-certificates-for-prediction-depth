import PredictionDepth.CompiledComposition

/-!
# Fast composition with correctness only along the executed path

The source criterion only bounds representations encountered by repeated
squaring. `PathImplementation` therefore imposes composition equations only
for those instructions, and observation correctness only at the final
representation. Encoding values outside that path has no correctness
requirement. The generated objects are actual bounded-fan-in Boolean DAGs.

For a family indexed by input length and time, `L` and these primitive circuits
may vary with both indices. Polynomial width/description bounds and a uniform
generator are separate family obligations, not inferred from finite-instance
correctness.
-/

namespace PredictionDepth.FastComposition

/-- The finite circuit data, before any semantic proof obligations are imposed. -/
structure CircuitPrimitives (n L : ℕ) (R : Type*) where
  encode : R → Bits L
  initialization : BinaryCircuit n (L + (L + n))
  composition : BinaryCircuit (L + L) L
  observation : BinaryCircuit (L + n) 1

namespace CircuitPrimitives
variable {n L : ℕ} {X R : Type*} {F : X → X}

/-- Check exactly the composition calls in a shared-register program. There
is no equation for arbitrary unvisited representations or arbitrary pairs. -/
def ValidFor (r : Realization X R F) (I : CircuitPrimitives n L R) : Program → Prop
  | .identity => True
  | .square p => ValidFor r I p ∧
      I.composition.eval (joinBits (I.encode (p.run r)) (I.encode (p.run r))) =
        I.encode ((Program.square p).run r)
  | .multiplySeed p => ValidFor r I p ∧
      I.composition.eval (joinBits (I.encode r.seed) (I.encode (p.run r))) =
        I.encode ((Program.multiplySeed p).run r)

def stage (I : CircuitPrimitives n L R) (useSeed : Bool) :
    BinaryCircuit (L + (L + n)) (L + (L + n)) :=
  .parallel (BinaryCircuit.select seedIndex)
    (.parallel (.seq (Implementation.argumentWires useSeed) I.composition)
      (BinaryCircuit.select inputIndex))

theorem stage_eval_of (r : Realization X R F) (I : CircuitPrimitives n L R)
    (useSeed : Bool) (a b : R)
    (h : I.composition.eval
      (joinBits (I.encode (if useSeed then r.seed else a)) (I.encode a)) = I.encode b)
    (x : Bits n) :
    (I.stage useSeed).eval (registers (I.encode r.seed) (I.encode a) x) =
      registers (I.encode r.seed) (I.encode b) x := by
  simp only [stage, BinaryCircuit.eval, Implementation.argumentWires_eval]
  have hs : (fun i => registers (I.encode r.seed) (I.encode a) x (seedIndex i)) =
      I.encode r.seed := by funext i; simp
  have hx : (fun i => registers (I.encode r.seed) (I.encode a) x (inputIndex i)) = x := by
    funext i; simp
  change joinBits _ (joinBits _ _) = _
  simp only [BinaryCircuit.select_eval, Function.comp_def, hs, hx]
  cases useSeed <;> simpa only [Bool.false_eq_true, ↓reduceIte, registers] using
    congrArg (fun acc => registers (I.encode r.seed) acc x) h

@[simp] theorem stage_depth (I : CircuitPrimitives n L R) (useSeed : Bool) :
    (I.stage useSeed).depth = I.composition.depth := by
  simp [stage, Implementation.argumentWires, BinaryCircuit.select, BinaryCircuit.depth]

@[simp] theorem stage_gateCount (I : CircuitPrimitives n L R) (useSeed : Bool) :
    (I.stage useSeed).gateCount = I.composition.gateCount := by
  simp [stage, Implementation.argumentWires, BinaryCircuit.select, BinaryCircuit.gateCount]

@[simp] theorem stage_descriptionSize (I : CircuitPrimitives n L R) (useSeed : Bool) :
    (I.stage useSeed).descriptionSize = I.composition.descriptionSize + 3 * L + n + 6 := by
  simp only [stage, Implementation.argumentWires, BinaryCircuit.select,
    BinaryCircuit.descriptionSize]
  omega

/-- The compiled prefix is used once, preserving its shared intermediate wires. -/
def compileProgram (I : CircuitPrimitives n L R) : Program → BinaryCircuit n (L + (L + n))
  | .identity => I.initialization
  | .square p => .seq (I.compileProgram p) (I.stage false)
  | .multiplySeed p => .seq (I.compileProgram p) (I.stage true)

theorem compileProgram_eval (r : Realization X R F) (I : CircuitPrimitives n L R)
    (hinit : ∀ x, I.initialization.eval x = registers (I.encode r.seed) (I.encode r.identity) x)
    (p : Program) (hp : I.ValidFor r p) (x : Bits n) :
    (I.compileProgram p).eval x = registers (I.encode r.seed) (I.encode (p.run r)) x := by
  induction p with
  | identity => exact hinit x
  | square p ih =>
      simp only [compileProgram, BinaryCircuit.eval, ih hp.1]
      exact I.stage_eval_of r false (p.run r) ((Program.square p).run r) hp.2 x
  | multiplySeed p ih =>
      simp only [compileProgram, BinaryCircuit.eval, ih hp.1]
      exact I.stage_eval_of r true (p.run r) ((Program.multiplySeed p).run r) hp.2 x

theorem compileProgram_depth (I : CircuitPrimitives n L R) (p : Program) :
    (I.compileProgram p).depth = I.initialization.depth + p.operations * I.composition.depth := by
  induction p with
  | identity => simp [compileProgram, Program.operations]
  | square p ih | multiplySeed p ih =>
      simp [compileProgram, BinaryCircuit.depth, ih, Program.operations, Nat.add_mul, Nat.add_assoc]

theorem compileProgram_gateCount (I : CircuitPrimitives n L R) (p : Program) :
    (I.compileProgram p).gateCount =
      I.initialization.gateCount + p.operations * I.composition.gateCount := by
  induction p with
  | identity => simp [compileProgram, Program.operations]
  | square p ih | multiplySeed p ih =>
      simp [compileProgram, BinaryCircuit.gateCount, ih, Program.operations, Nat.add_mul, Nat.add_assoc]

theorem compileProgram_descriptionSize (I : CircuitPrimitives n L R) (p : Program) :
    (I.compileProgram p).descriptionSize = I.initialization.descriptionSize +
      p.operations * (I.composition.descriptionSize + 3 * L + n + 7) := by
  induction p with
  | identity => simp [compileProgram, Program.operations]
  | square p ih | multiplySeed p ih =>
      simp only [compileProgram, BinaryCircuit.descriptionSize, ih, stage_descriptionSize,
        Program.operations, Nat.add_mul, Nat.one_mul]
      omega

def predictor (I : CircuitPrimitives n L R) (p : Program) : BinaryCircuit n 1 :=
  .seq (I.compileProgram p) (.seq Implementation.observationWires I.observation)

theorem predictor_depth (I : CircuitPrimitives n L R) (p : Program) :
    (I.predictor p).depth =
      I.initialization.depth + p.operations * I.composition.depth + I.observation.depth := by
  simp [predictor, BinaryCircuit.depth, compileProgram_depth, Implementation.observationWires,
    BinaryCircuit.select, Nat.add_assoc]

theorem predictor_gateCount (I : CircuitPrimitives n L R) (p : Program) :
    (I.predictor p).gateCount =
      I.initialization.gateCount + p.operations * I.composition.gateCount + I.observation.gateCount := by
  simp [predictor, BinaryCircuit.gateCount, compileProgram_gateCount, Implementation.observationWires,
    BinaryCircuit.select, Nat.add_assoc]

theorem predictor_descriptionSize (I : CircuitPrimitives n L R) (p : Program) :
    (I.predictor p).descriptionSize = I.initialization.descriptionSize +
      p.operations * (I.composition.descriptionSize + 3 * L + n + 7) +
      I.observation.descriptionSize + L + n + 3 := by
  simp only [predictor, BinaryCircuit.descriptionSize, compileProgram_descriptionSize,
    Implementation.observationWires, BinaryCircuit.select]
  omega

end CircuitPrimitives

/-- The representation width and primitive circuits only need to work on this
particular execution path. Observation correctness is required only at its end. -/
structure PathImplementation {n : ℕ} {R : Type*} {F : Bits n → Bits n}
    (r : Realization (Bits n) R F) (observe : Bits n → Bool) (L : ℕ) (p : Program)
    extends CircuitPrimitives n L R where
  initialization_correct : ∀ x,
    initialization.eval x = registers (encode r.seed) (encode r.identity) x
  program_correct : toCircuitPrimitives.ValidFor r p
  observation_correct : ∀ x, observation.eval (joinBits (encode (p.run r)) x) 0 =
    observe (r.denote (p.run r) x)

namespace PathImplementation
variable {n L : ℕ} {R : Type*} {F : Bits n → Bits n}
  {r : Realization (Bits n) R F} {observe : Bits n → Bool} {p : Program}

def predictor (I : PathImplementation r observe L p) : BinaryCircuit n 1 :=
  I.toCircuitPrimitives.predictor p

theorem predictor_correct (I : PathImplementation r observe L p) (x : Bits n) :
    I.predictor.eval x 0 = observe (F^[p.exponent] x) := by
  simp only [predictor, CircuitPrimitives.predictor, BinaryCircuit.eval,
    I.toCircuitPrimitives.compileProgram_eval r I.initialization_correct p I.program_correct,
    Implementation.observationWires_eval]
  rw [I.observation_correct, Program.run_correct]

theorem compiled_predictor_correct {T : ℕ} (I : PathImplementation r observe L (compile T))
    (x : Bits n) : I.predictor.eval x 0 = observe (F^[T] x) := by
  simpa only [compile_exponent] using I.predictor_correct x

/-- Original Theorem A's depth bound, requiring only encountered-pair correctness. -/
theorem predictor_depth_le {T : ℕ} (I : PathImplementation r observe L (compile T)) :
    I.predictor.depth ≤ I.initialization.depth +
      2 * Nat.clog 2 (T + 1) * I.composition.depth + I.observation.depth := by
  rw [predictor, CircuitPrimitives.predictor_depth]
  have h := Nat.mul_le_mul_right I.composition.depth (compile_operations T)
  rw [bitLength_eq_clog] at h
  omega

theorem predictor_gateCount_le {T : ℕ} (I : PathImplementation r observe L (compile T)) :
    I.predictor.gateCount ≤ I.initialization.gateCount +
      2 * Nat.clog 2 (T + 1) * I.composition.gateCount + I.observation.gateCount := by
  rw [predictor, CircuitPrimitives.predictor_gateCount]
  have h := Nat.mul_le_mul_right I.composition.gateCount (compile_operations T)
  rw [bitLength_eq_clog] at h
  omega

theorem predictor_descriptionSize_le {T : ℕ} (I : PathImplementation r observe L (compile T)) :
    I.predictor.descriptionSize ≤ I.initialization.descriptionSize +
      2 * Nat.clog 2 (T + 1) * (I.composition.descriptionSize + 3 * L + n + 7) +
      I.observation.descriptionSize + L + n + 3 := by
  rw [predictor, CircuitPrimitives.predictor_descriptionSize]
  have h := Nat.mul_le_mul_right (I.composition.descriptionSize + 3 * L + n + 7)
    (compile_operations T)
  rw [bitLength_eq_clog] at h
  omega

end PathImplementation

namespace Implementation
variable {n L : ℕ} {R : Type*} {F : Bits n → Bits n}
  {r : Realization (Bits n) R F} {observe : Bits n → Bool}

/-- The former globally correct implementation is a special case of the
path-only criterion, for every execution path. -/
def toPathImplementation (I : Implementation r observe L) (p : Program) :
    PathImplementation r observe L p where
  encode := I.encode
  initialization := I.initialization
  composition := I.composition
  observation := I.observation
  initialization_correct := I.initialization_correct
  program_correct := by
    induction p with
    | identity => trivial
    | square p ih => exact ⟨ih, I.composition_correct _ _⟩
    | multiplySeed p ih => exact ⟨ih, I.composition_correct _ _⟩
  observation_correct := I.observation_correct (p.run r)

end Implementation

namespace PathCriterionExample

/-- A two-element representation of identity and one-bit negation. -/
def realization : Realization (Bits 1) Bool (fun x i => !x i) where
  identity := false
  seed := true
  compose := Bool.xor
  denote := fun b x i => Bool.xor b (x i)
  identity_correct := by
    funext x i
    change Bool.xor false (x i) = x i
    cases x i <;> rfl
  seed_correct := by funext x i; cases x i <;> rfl
  compose_correct := by
    intro a b
    funext x i
    change Bool.xor (Bool.xor a b) (x i) = Bool.xor a (Bool.xor b (x i))
    cases a <;> cases b <;> cases x i <;> rfl

/-- No representation bit is needed on the time-zero path: the decoder merely
copies the initial state. The unused composition circuit has no obligations. -/
def zeroTimePath : PathImplementation realization (fun x => x 0) 0 .identity where
  encode := fun _ => Fin.elim0
  initialization := BinaryCircuit.select id
  composition := BinaryCircuit.constant Fin.elim0
  observation := BinaryCircuit.select id
  initialization_correct := by
    intro x
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  program_correct := trivial
  observation_correct := by
    intro x
    change x 0 = Bool.xor false (x 0)
    cases x 0 <;> rfl

/-- The same zero-width data cannot correctly decode every representation:
identity and negation must give different answers on the false input. This
shows that the path-only criterion is strictly less restrictive. -/
theorem no_global_zero_width :
    ¬ Nonempty (Implementation realization (fun x => x 0) 0) := by
  rintro ⟨I⟩
  have he : I.encode false = I.encode true := by funext i; exact Fin.elim0 i
  have hf := I.observation_correct false (fun _ => false)
  have ht := I.observation_correct true (fun _ => false)
  change I.observation.eval (joinBits (I.encode false) (fun _ => false)) 0 = false at hf
  change I.observation.eval (joinBits (I.encode true) (fun _ => false)) 0 = true at ht
  rw [he] at hf
  exact Bool.false_ne_true (hf.symm.trans ht)

end PathCriterionExample
end PredictionDepth.FastComposition
