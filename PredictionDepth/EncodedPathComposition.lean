import PredictionDepth.PathComposition

/-!
# Finite input encoding for arbitrary global state spaces

Only the input window and representation are finite bit strings. The dynamical
state `X` can be infinite, such as configurations on the entire integer lattice.
Correctness of the primitive circuits is required only along the executed path.
-/
namespace PredictionDepth.FastComposition

structure EncodedPathImplementation {n : ℕ} {X R : Type*} {F : X → X}
    (r : Realization X R F) (input : Bits n → X) (observe : X → Bool)
    (L : ℕ) (p : Program) extends CircuitPrimitives n L R where
  initialization_correct : ∀ x,
    initialization.eval x = registers (encode r.seed) (encode r.identity) x
  program_correct : toCircuitPrimitives.ValidFor r p
  observation_correct : ∀ x, observation.eval (joinBits (encode (p.run r)) x) 0 =
    observe (r.denote (p.run r) (input x))

namespace EncodedPathImplementation
variable {n L : ℕ} {X R : Type*} {F : X → X} {r : Realization X R F}
  {input : Bits n → X} {observe : X → Bool} {p : Program}

def predictor (I : EncodedPathImplementation r input observe L p) : BinaryCircuit n 1 :=
  I.toCircuitPrimitives.predictor p

theorem predictor_correct (I : EncodedPathImplementation r input observe L p) (x : Bits n) :
    I.predictor.eval x 0 = observe (F^[p.exponent] (input x)) := by
  simp only [predictor, CircuitPrimitives.predictor, BinaryCircuit.eval,
    I.toCircuitPrimitives.compileProgram_eval r I.initialization_correct p I.program_correct,
    Implementation.observationWires_eval]
  rw [I.observation_correct, Program.run_correct]

theorem compiled_predictor_correct {T : ℕ}
    (I : EncodedPathImplementation r input observe L (compile T)) (x : Bits n) :
    I.predictor.eval x 0 = observe (F^[T] (input x)) := by
  simpa only [compile_exponent] using I.predictor_correct x

theorem predictor_depth_le {T : ℕ}
    (I : EncodedPathImplementation r input observe L (compile T)) :
    I.predictor.depth ≤ I.initialization.depth +
      2 * Nat.clog 2 (T + 1) * I.composition.depth + I.observation.depth := by
  rw [predictor, CircuitPrimitives.predictor_depth]
  have h := Nat.mul_le_mul_right I.composition.depth (compile_operations T)
  rw [bitLength_eq_clog] at h
  omega

theorem predictor_gateCount_le {T : ℕ}
    (I : EncodedPathImplementation r input observe L (compile T)) :
    I.predictor.gateCount ≤ I.initialization.gateCount +
      2 * Nat.clog 2 (T + 1) * I.composition.gateCount + I.observation.gateCount := by
  rw [predictor, CircuitPrimitives.predictor_gateCount]
  have h := Nat.mul_le_mul_right I.composition.gateCount (compile_operations T)
  rw [bitLength_eq_clog] at h
  omega

theorem predictor_descriptionSize_le {T : ℕ}
    (I : EncodedPathImplementation r input observe L (compile T)) :
    I.predictor.descriptionSize ≤ I.initialization.descriptionSize +
      2 * Nat.clog 2 (T + 1) * (I.composition.descriptionSize + 3 * L + n + 7) +
      I.observation.descriptionSize + L + n + 3 := by
  rw [predictor, CircuitPrimitives.predictor_descriptionSize]
  have h := Nat.mul_le_mul_right (I.composition.descriptionSize + 3 * L + n + 7)
    (compile_operations T)
  rw [bitLength_eq_clog] at h
  omega

end EncodedPathImplementation

def PathImplementation.toEncoded {n L : ℕ} {R : Type*} {F : Bits n → Bits n}
    {r : Realization (Bits n) R F} {observe : Bits n → Bool} {p : Program}
    (I : PathImplementation r observe L p) : EncodedPathImplementation r id observe L p where
  toCircuitPrimitives := I.toCircuitPrimitives
  initialization_correct := I.initialization_correct
  program_correct := I.program_correct
  observation_correct := I.observation_correct

end PredictionDepth.FastComposition
