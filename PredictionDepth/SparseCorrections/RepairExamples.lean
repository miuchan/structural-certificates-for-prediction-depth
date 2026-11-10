import PredictionDepth.SparseCorrections.CollisionCertificate
import PredictionDepth.SparseCorrections.RepairUniform

/-! Concrete bit and layer repair predictors for the reversible collision rule. -/

namespace PredictionDepth.SparseCorrections.Collision

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity Turing.MultiTapeTM

def bitRepairPredictor (k T : ℕ) : Gates (inputWidth 3 1 T) 2 :=
  RepairCircuit.compileBits (layout.response T) (layout.check T) (layout.observe T) k

def layerRepairPredictor (k T : ℕ) : Gates (inputWidth 3 1 T) 2 :=
  RepairCircuit.compile (layout.response T) (layout.check T) (LayerChecks.failFlags 3 1 T)
    (LayerChecks.eventBlock 3 1 T) (layout.observe T) k

theorem bitRepairPredictor_correct (k T : ℕ) (u : Layer (coneWidth 3 1 T) 0) :
    let out := (bitRepairPredictor k T).eval interpretation u
    (out 0 = true ↔ Sparse (UniformLayout.residual (R := 1) bitStep bitStream T u) k) ∧
      out 1 = (out 0 && layoutCorrect.value T u) :=
  RepairCircuit.compileBits_correct (Cone.transition 1 T bitStep) (Cone.transition 1 T bitStream)
    (layoutCorrect.event T) (layoutCorrect.state T) (layout.response T) (layout.check T)
    (layoutCorrect.response T) (layoutCorrect.check T) (Cone.eventIndex_chronological 3 1 T)
    (layout.observe T) u k

theorem layerRepairPredictor_correct (k T : ℕ) (u : Layer (coneWidth 3 1 T) 0) :
    let out := (layerRepairPredictor k T).eval interpretation u
    (out 0 = true ↔ (layerSupport (UniformLayout.residual (R := 1) bitStep bitStream T u)).card ≤ k) ∧
      out 1 = (out 0 && layoutCorrect.value T u) :=
  RepairCircuit.compileLayers_correct (Cone.transition 1 T bitStep) (Cone.transition 1 T bitStream)
    (layoutCorrect.event T) (layoutCorrect.state T) (layout.response T) (layout.check T)
    (layoutCorrect.response T) (layoutCorrect.check T) (LayerChecks.failFlags 3 1 T)
    (LayerChecks.failFlags_true_iff 3 1 T) (layout.observe T) u k

theorem exampleLayerSupport_card {ell : ℕ} (hell : 0 < ell) :
    (layerSupport (exampleResidual ell)).card = 2 := by
  have he : layerSupport (exampleResidual ell) = (support (exampleResidual ell)).image Sigma.fst := by
    ext t
    rw [mem_layerSupport, Finset.mem_image]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨⟨t, i⟩, (mem_support _ _).mpr hi, rfl⟩
    · rintro ⟨⟨s, i⟩, hi, rfl⟩
      exact ⟨i, (mem_support _ _).mp hi⟩
  rw [he, exampleResidual_support hell, Finset.image_insert, Finset.image_insert,
    Finset.image_singleton]
  have hfirst : (firstA hell).1 = (firstB hell).1 := rfl
  have hne : (firstB hell).1 ≠ (secondA hell).1 := fun h => by
    have hval := congrArg Fin.val h
    change 0 = ell at hval
    omega
  rw [hfirst, Finset.insert_idem, Finset.card_insert_of_notMem (by simpa using hne)]
  rfl

private theorem example_value {ell : ℕ} (hell : 0 < ell) :
    layoutCorrect.value (2 * ell) (exampleInput ell) = true := by
  rw [exampleInput, value_eq_observation, bitStep_iterate]
  exact returning_observation hell

/-- The two linked collisions need three bit rounds and only two layer rounds.
The thresholds hold at every positive reflector separation. -/
theorem example_repair_thresholds {ell : ℕ} (hell : 0 < ell) (k : ℕ) :
    let b := (bitRepairPredictor k (2 * ell)).eval interpretation (exampleInput ell)
    let l := (layerRepairPredictor k (2 * ell)).eval interpretation (exampleInput ell)
    (b 0 = true ↔ 3 ≤ k) ∧ (l 0 = true ↔ 2 ≤ k) ∧ b 1 = b 0 ∧ l 1 = l 0 := by
  obtain ⟨hb, hvb⟩ := bitRepairPredictor_correct k (2 * ell) (exampleInput ell)
  obtain ⟨hl, hvl⟩ := layerRepairPredictor_correct k (2 * ell) (exampleInput ell)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hb.trans
    change (support (exampleResidual ell)).card ≤ k ↔ _
    rw [exampleResidual_card hell]
  · apply hl.trans
    change (layerSupport (exampleResidual ell)).card ≤ k ↔ _
    rw [exampleLayerSupport_card hell]
  · simpa only [example_value hell, Bool.and_true] using hvb
  · simpa only [example_value hell, Bool.and_true] using hvl

private theorem repairLanguages_mem {d : ℕ}
    (P : ∀ T, Gates (inputWidth 3 1 T) 2)
    (A : ∀ T, (Fin (inputWidth 3 1 T) → Bool) → Prop)
    (hcorrect : ∀ T u,
      let out := (P T).eval interpretation u
      (out 0 = true ↔ A T u) ∧ out 1 = (out 0 && layoutCorrect.value T u))
    (hNC : ∀ lane, lengthLanguage P lane ∈ UniformNCLevel d) :
    UniformLayout.coneLanguage A ∈ UniformNCLevel d ∧
      UniformLayout.coneLanguage (fun T u => A T u ∧ layoutCorrect.value T u = true)
        ∈ UniformNCLevel d := by
  constructor
  · rw [← UniformLayout.lengthLanguage_eq_coneLanguage (by decide) (by decide) P 0 _
      (fun T u => (hcorrect T u).1)]
    exact hNC 0
  · rw [← UniformLayout.lengthLanguage_eq_coneLanguage (by decide) (by decide) P 1 _
      (fun T u => by rw [(hcorrect T u).2, Bool.and_eq_true, (hcorrect T u).1])]
    exact hNC 1

/-- Recognition and gated prediction with logarithmically many bit rounds. -/
theorem bitRepair_mem_uniformNC_two (budget : ℕ → ℕ)
    (hcode : ComputableInLogSpace budget encUnary encUnary) (C K : ℕ)
    (hbudget : ∀ T, budget T ≤ C + K * Nat.clog 2 (T + 1)) :
    UniformLayout.coneLanguage (fun T u =>
      Sparse (UniformLayout.residual (R := 1) bitStep bitStream T u) (budget T)) ∈
      UniformNCLevel 2 ∧
    UniformLayout.coneLanguage (fun T u =>
      Sparse (UniformLayout.residual (R := 1) bitStep bitStream T u) (budget T) ∧
      layoutCorrect.value T u = true) ∈ UniformNCLevel 2 := by
  apply repairLanguages_mem
    (RepairUniform.predictor layout (RepairUniform.UniformBlocks.bits layout) budget)
  · exact fun T u => bitRepairPredictor_correct (budget T) T u
  · exact RepairUniform.logLanguage_mem_uniformNC_two _ _ budget hcode C K hbudget

/-- The analogous two languages with a budget on nonzero update layers. -/
theorem layerRepair_mem_uniformNC_two (budget : ℕ → ℕ)
    (hcode : ComputableInLogSpace budget encUnary encUnary) (C K : ℕ)
    (hbudget : ∀ T, budget T ≤ C + K * Nat.clog 2 (T + 1)) :
    UniformLayout.coneLanguage (fun T u =>
      (layerSupport (UniformLayout.residual (R := 1) bitStep bitStream T u)).card ≤ budget T) ∈
      UniformNCLevel 2 ∧
    UniformLayout.coneLanguage (fun T u =>
      (layerSupport (UniformLayout.residual (R := 1) bitStep bitStream T u)).card ≤ budget T ∧
      layoutCorrect.value T u = true) ∈ UniformNCLevel 2 := by
  apply repairLanguages_mem
    (RepairUniform.predictor layout (RepairUniform.UniformBlocks.layers 3 1) budget)
  · exact fun T u => layerRepairPredictor_correct (budget T) T u
  · exact RepairUniform.logLanguage_mem_uniformNC_two _ _ budget hcode C K hbudget

end PredictionDepth.SparseCorrections.Collision
