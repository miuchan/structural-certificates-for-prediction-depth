import PredictionDepth.SparseCorrections.Certificate
import PredictionDepth.SparseCorrections.CollisionVerifier
import PredictionDepth.SparseCorrections.StreamingCircuit

/-! A concrete, uniform sparse predictor for the reversible collision rule. -/

namespace PredictionDepth.SparseCorrections.Collision

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity Turing.MultiTapeTM

def observation (T : ℕ) : Fin (Cone.stateCount 3 1 T) :=
  Cone.stateIndex 3 1 T ⟨Fin.last T, Cone.encodeBit 3 1 T T 0 (by
    simp [Cone.InWindow, Cone.radius]) 0⟩

private theorem observation_val (T : ℕ) : (observation T).val = Cone.offset 3 1 T T := by
  unfold observation
  rw [Cone.stateIndex_val]
  simp [Cone.encodeBit, Cone.siteIndex, Cone.radius, finProdFinEquiv]

/-- The same typed circuits have local semantics, the stated depth bounds,
and complete serializers under the repository's logspace machine model. -/
def layout : UniformLayout 3 1 where
  events := Cone.eventCount 3 1
  states := Cone.stateCount 3 1
  response := Streaming.circuit
  check := check
  observe := observation
  eventsUniform := Cone.eventCount_logspace 3 1
  statesUniform := Cone.stateCount_logspace 3 1
  responseUniform := Streaming.circuit_code_logspace
  checkUniform := check_code_logspace
  observeUniform := ((Cone.offset_logspace 3 1).comp
    (ComputableInLogSpace.id.pair ComputableInLogSpace.id)).congr_fun observation_val
  eventCoefficient := 7
  eventDegree := 2
  eventBound := Cone.eventCount_polynomial 3 1
  responseConstant := 3
  responseFactor := 4
  responseDepth := fun T => by
    have hd := Streaming.circuit_depth T
    rw [FrozenPascal.xorGate_depth] at hd
    simpa only [Nat.mul_comm] using hd
  checkDepth := 7
  checkBound := check_depth

def layoutCorrect : layout.Correct bitStep bitStream where
  event T := (Cone.eventIndex 3 1 T).symm
  state T := (Cone.stateIndex 3 1 T).symm
  response T u e := by
    funext t b
    exact Streaming.circuit_correct T u e t b
  check := check_correct

theorem value_eq_observation (T : ℕ) (x : Cone.Config 3) :
    layoutCorrect.value T (Cone.restrict 1 T 0 x) = ((bitStep^[T]) x) 0 0 := by
  let b : StateBit (coneWidth 3 1 T) T :=
    ⟨Fin.last T, Cone.encodeBit 3 1 T T 0 (by simp [Cone.InWindow, Cone.radius]) 0⟩
  have hobs : layoutCorrect.state T (layout.observe T) = b :=
    (Cone.stateIndex 3 1 T).symm_apply_apply b
  let read (c : StateBit (coneWidth 3 1 T) T) :=
    actualTrajectory (Cone.transition 1 T bitStep) (Cone.restrict 1 T 0 x) c.1 c.2
  calc
    layoutCorrect.value T (Cone.restrict 1 T 0 x) = read b := congrArg read hobs
    _ = ((bitStep^[T]) x) 0 0 := by
      change actualTrajectory (Cone.transition 1 T bitStep) (Cone.restrict 1 T 0 x)
        (Fin.last T) (Cone.encodeBit 3 1 T T 0 _ 0) = _
      rw [Cone.finiteTrajectory_eq_restrict_iterate bitStep_local _ x rfl]
      exact Cone.restrict_encodeBit ((bitStep^[T]) x) 0
        (by simp [Cone.InWindow, Cone.radius]) 0

theorem sparsePrediction_mem_uniformNC_one (k : ℕ) :
    UniformLayout.coneLanguage (fun T u =>
      Sparse (UniformLayout.residual (R := 1) bitStep bitStream T u) k) ∈ UniformNCLevel 1 ∧
    UniformLayout.coneLanguage (fun T u =>
      Sparse (UniformLayout.residual (R := 1) bitStep bitStream T u) k ∧
      layoutCorrect.value T u = true) ∈ UniformNCLevel 1 :=
  layoutCorrect.unknown_mem_uniformNC_one (by decide) (by decide) k

/-- A whole family of interacting inputs passes both output checks with
exactly three correction bits. -/
theorem example_accepts_and_predicts {ell : ℕ} (hell : 0 < ell) :
    let y := (layout.unknownPredictor 3 (2 * ell)).eval interpretation (exampleInput ell)
    y 0 = true ∧ y 1 = true := by
  have h := layoutCorrect.unknown 3 (2 * ell) (exampleInput ell)
  have ha := h.1.mpr (Nat.le_of_eq (exampleResidual_card hell))
  refine ⟨ha, ?_⟩
  rw [h.2, ha, Bool.true_and]
  rw [exampleInput, value_eq_observation, bitStep_iterate]
  exact returning_observation hell

end PredictionDepth.SparseCorrections.Collision
