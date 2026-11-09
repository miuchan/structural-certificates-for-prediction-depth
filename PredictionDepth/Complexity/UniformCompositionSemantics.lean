import PredictionDepth.Complexity.UniformComposition.Schedule
import PredictionDepth.Complexity.UniformComposition.TypedChain

/-!
# Uniform repeated-squaring semantics on an arbitrary state space

Only input words and working registers have finite width. The dynamical state
space can be infinite. Primitive equations are required solely on the actual
executed register path; no finite global state-space assumption is introduced.
-/

namespace PredictionDepth.StandardComplexity.UniformComposition
open Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition

/-- The concrete predictor whose code generator is supplied in the uniform
composition module. Output normalization is semantic identity. -/
def predictor {n W : ℕ} (initialization : Circuit signature n W)
    (square multiplySeed : Circuit signature W W) (observation : Circuit signature W 1)
    (bits : List Bool) : Circuit signature n 1 :=
  observation.comp (normalizedChain initialization (stages square multiplySeed bits))

/-- Local primitive correctness along one finite sequence of instructions. -/
def RegisterValidFor {n W : ℕ} {X R : Type*} {F : X → X}
    (r : Realization X R F) (register : R → Bits n → Bits W)
    (square multiplySeed : Circuit signature W W) : Program → List Instruction → Prop
  | _, [] => True
  | p, op :: ops =>
      (∀ x, (circuitFor square multiplySeed op).eval interpretation (register (p.run r) x) =
        register ((op.advance p).run r) x) ∧
      RegisterValidFor r register square multiplySeed (op.advance p) ops

theorem circuitChain_registers {n W : ℕ} {X R : Type*} {F : X → X}
    (r : Realization X R F) (register : R → Bits n → Bits W)
    (square multiplySeed : Circuit signature W W) (ops : List Instruction)
    (p : Program) (initialization : Circuit signature n W)
    (hi : ∀ x, initialization.eval interpretation x = register (p.run r) x)
    (hv : RegisterValidFor r register square multiplySeed p ops) (x : Bits n) :
    (circuitChain initialization (ops.map (circuitFor square multiplySeed))).eval interpretation x =
      register ((executeProgram ops p).run r) x := by
  induction ops generalizing p initialization with
  | nil => exact hi x
  | cons op ops ih =>
      have hnext : ∀ x,
          ((circuitFor square multiplySeed op).comp initialization).eval interpretation x =
            register ((op.advance p).run r) x := by
        intro y
        rw [Circuit.eval_comp, hi]
        exact hv.1 y
      exact ih (op.advance p) ((circuitFor square multiplySeed op).comp initialization) hnext hv.2

/-- A finite register implementation with proof obligations only on the binary
schedule that will actually run. All costs refer to explicit Boolean circuits. -/
structure RegisterWitness {n W : ℕ} {X R : Type*} {F : X → X}
    (r : Realization X R F) (input : Bits n → X) (observe : X → Bool) (bits : List Bool) where
  register : R → Bits n → Bits W
  initialization : Circuit signature n W
  square : Circuit signature W W
  multiplySeed : Circuit signature W W
  observation : Circuit signature W 1
  initialization_correct : ∀ x, initialization.eval interpretation x = register r.identity x
  path_correct : RegisterValidFor r register square multiplySeed .identity (bitSteps bits)
  observation_correct : ∀ x,
    observation.eval interpretation (register ((compileBits bits).run r) x) 0 =
      observe (r.denote ((compileBits bits).run r) (input x))

namespace RegisterWitness
variable {n W : ℕ} {X R : Type*} {F : X → X} {r : Realization X R F}
  {input : Bits n → X} {observe : X → Bool} {bits : List Bool}

def circuit (w : RegisterWitness (W := W) r input observe bits) : Circuit signature n 1 :=
  predictor w.initialization w.square w.multiplySeed w.observation bits

theorem circuit_correct (w : RegisterWitness (W := W) r input observe bits) (x : Bits n) :
    w.circuit.eval interpretation x 0 = observe (F^[binaryValue bits] (input x)) := by
  rw [circuit, predictor, Circuit.eval_comp, normalizedChain_eval]
  change w.observation.eval interpretation
    ((circuitChain w.initialization ((bitSteps bits).map
      (circuitFor w.square w.multiplySeed))).eval interpretation x) 0 = _
  rw [circuitChain_registers r w.register w.square w.multiplySeed (bitSteps bits) .identity
    w.initialization w.initialization_correct w.path_correct x]
  rw [executeProgram_bitSteps, w.observation_correct, Program.run_correct, compileBits_exponent]

theorem circuit_at_time_correct {T : ℕ}
    (w : RegisterWitness (W := W) r input observe (binaryDigits T)) (x : Bits n) :
    w.circuit.eval interpretation x 0 = observe (F^[T] (input x)) := by
  simpa only [binaryDigits_value] using w.circuit_correct x

end RegisterWitness

theorem predictor_size_le {n W : ℕ} (initialization : Circuit signature n W)
    (square multiplySeed : Circuit signature W W) (observation : Circuit signature W 1)
    (bits : List Bool) :
    (predictor initialization square multiplySeed observation bits).size ≤
      initialization.size + W + 2 * bits.length * (max square.size multiplySeed.size + W) +
        observation.size := by
  rw [predictor, Circuit.size_comp, normalizedChain_size]
  have hs := sum_map_le (fun c : Circuit signature W W => c.size + W)
    (stages square multiplySeed bits) (max square.size multiplySeed.size + W) (by
      intro c hc
      obtain ⟨op, _, rfl⟩ := List.mem_map.mp hc
      exact Nat.add_le_add_right (circuitFor_size_le square multiplySeed op) W)
  rw [stages_length] at hs
  omega

theorem predictor_depth_le {n W : ℕ} (initialization : Circuit signature n W)
    (square multiplySeed : Circuit signature W W) (observation : Circuit signature W 1)
    (bits : List Bool) :
    (predictor initialization square multiplySeed observation bits).depth ≤
      initialization.depth + 1 + 2 * bits.length * (max square.depth multiplySeed.depth + 1) +
        observation.depth := by
  have hs := sum_map_le (fun c : Circuit signature W W => c.depth + 1)
    (stages square multiplySeed bits) (max square.depth multiplySeed.depth + 1) (by
      intro c hc
      obtain ⟨op, _, rfl⟩ := List.mem_map.mp hc
      exact Nat.add_le_add_right (circuitFor_depth_le square multiplySeed op) 1)
  rw [stages_length] at hs
  have hn := normalizedChain_depth initialization (stages square multiplySeed bits)
  have h := Circuit.depth_comp_le observation
    (normalizedChain initialization (stages square multiplySeed bits))
  change (predictor initialization square multiplySeed observation bits).depth ≤ _ at h
  omega

theorem predictor_logarithmic_depth {n W : ℕ} (initialization : Circuit signature n W)
    (square multiplySeed : Circuit signature W W) (observation : Circuit signature W 1)
    (T : ℕ) :
    (predictor initialization square multiplySeed observation (binaryDigits T)).depth ≤
      initialization.depth + 1 +
        2 * Nat.clog 2 (T + 1) * (max square.depth multiplySeed.depth + 1) + observation.depth := by
  have h := predictor_depth_le initialization square multiplySeed observation (binaryDigits T)
  change (predictor initialization square multiplySeed observation (binaryDigits T)).depth ≤
    initialization.depth + 1 + 2 * bitLength T * (max square.depth multiplySeed.depth + 1) +
      observation.depth at h
  simpa only [bitLength_eq_clog] using h

end PredictionDepth.StandardComplexity.UniformComposition
