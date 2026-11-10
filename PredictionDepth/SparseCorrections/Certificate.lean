import PredictionDepth.SparseCorrections.Uniform

/-! Connect generated circuit families to the residual predicates on raw words. -/

namespace PredictionDepth.SparseCorrections

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity

variable {q R : ℕ}

namespace UniformLayout

/-- The local-rule and forced-response contracts for the same circuits that
the layout serializes. The coordinate bijections cover every bit of the cone. -/
structure Correct (A : UniformLayout q R) (F L : Cone.Config q → Cone.Config q) where
  event : ∀ T, Fin (A.events T) ≃ Event (coneWidth q R T) T
  state : ∀ T, Fin (A.states T) ≃ StateBit (coneWidth q R T) T
  response : ∀ T (u : Layer (coneWidth q R T) 0) (e : Fin (A.events T) → Bool),
    decodeTrajectory (state T) ((A.response T).eval interpretation (Fin.append e u)) =
      forcedTrajectory (Cone.transition R T L) u (e ∘ (event T).symm)
  check : ∀ T y i, (A.check T i).eval interpretation y 0 = true ↔
    let v := event T i
    let z := decodeTrajectory (state T) y
    z v.1.succ v.2 = Cone.transition R T F v.1 (z v.1.castSucc) v.2

variable {A : UniformLayout q R} {F L : Cone.Config q → Cone.Config q}

def residual (F L : Cone.Config q → Cone.Config q) (T : ℕ) (u : Fin (inputWidth q R T) → Bool) :
    Residual (coneWidth q R T) T :=
  actualResidual (Cone.transition R T F) (Cone.transition R T L) u

def Correct.value (h : A.Correct F L) (T : ℕ) (u : Fin (inputWidth q R T) → Bool) : Bool :=
  let b := h.state T (A.observe T)
  actualTrajectory (Cone.transition R T F) u b.1 b.2

theorem Correct.compile (h : A.Correct F L) (T : ℕ)
    (candidates : Fin N → Fin (A.events T) → Bool) (u : Fin (inputWidth q R T) → Bool)
    (P : Prop) (hP : (∃ j, candidates j = residual (R := R) F L T u ∘ h.event T) ↔ P) :
    let out := (compile (A.response T) (A.check T) (A.observe T) candidates).eval interpretation u
    (out 0 = true ↔ P) ∧ out 1 = (out 0 && h.value T u) := by
  obtain ⟨ha, hv⟩ := compile_semantics (Cone.transition R T F) (Cone.transition R T L)
    (h.event T) (h.state T) (A.response T) (A.check T) (h.response T) (h.check T)
    (A.observe T) candidates u
  exact ⟨ha.trans hP, hv⟩

theorem Correct.unknown (h : A.Correct F L) (k T : ℕ) (u : Fin (inputWidth q R T) → Bool) :
    let out := (A.unknownPredictor k T).eval interpretation u
    (out 0 = true ↔ Sparse (residual (R := R) F L T u) k) ∧
      out 1 = (out 0 && h.value T u) := by
  apply h.compile
  rw [exists_unknownCandidate_iff, encodedSupport_card]
  rfl

def Correct.allowed (h : A.Correct F L) (J : Schedule A) (T : ℕ) :
    Finset (Event (coneWidth q R T) T) :=
  Finset.univ.image (h.event T ∘ J.slot T)

theorem Correct.scheduled (h : A.Correct F L) (J : Schedule A) (T : ℕ)
    (u : Fin (inputWidth q R T) → Bool) :
    let out := (A.scheduledPredictor J T).eval interpretation u
    (out 0 = true ↔ Supported (residual (R := R) F L T u) (h.allowed J T)) ∧
      out 1 = (out 0 && h.value T u) := by
  apply h.compile
  rw [exists_scheduledCandidate_iff]
  constructor
  · intro hs v hv
    obtain ⟨j, hj⟩ := hs ((h.event T).symm v) (by simpa using (mem_support _ _).mp hv)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, by simp [hj]⟩
  · intro hs i hi
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp
      (hs ((mem_support _ _).mpr hi) : h.event T i ∈ h.allowed J T)
    exact ⟨j, (h.event T).injective hj⟩

/-- Legal raw words, decoded at their unique horizon, with the stated
predicate. This definition assigns false to all illegal lengths. -/
def coneLanguage (P : ∀ T, (Fin (inputWidth q R T) → Bool) → Prop) : Set (List Bool) :=
  {x | ∃ T, x.length = inputWidth q R T ∧ P T (BitString.ofList (inputWidth q R T) x)}

theorem lengthLanguage_eq_coneLanguage (hq : 0 < q) (hR : 0 < R)
    (C : ∀ T, Gates (inputWidth q R T) 2) (lane : Fin 2)
    (P : ∀ T, (Fin (inputWidth q R T) → Bool) → Prop)
    (hP : ∀ T u, (C T).eval interpretation u lane = true ↔ P T u) :
    lengthLanguage C lane = coneLanguage P := by
  ext x
  change evaluateFamily (lengthFamily C lane) x = true ↔ _
  constructor
  · intro hx
    by_cases h : LegalLength q R x.length
    · let T := timeOfLength q R x.length
      have hw : x.length = inputWidth q R T := h.symm
      refine ⟨T, hw, (hP _ _).mp ?_⟩
      unfold evaluateFamily at hx
      rw [hw, lengthFamily_eval_at_time hq hR] at hx
      exact hx
    · unfold evaluateFamily at hx
      rw [lengthFamily_eval, dite_eq_right h] at hx
      cases hx
  · rintro ⟨T, hw, hp⟩
    unfold evaluateFamily
    rw [hw, lengthFamily_eval_at_time hq hR]
    exact (hP _ _).mpr hp

/-- The fixed unknown budget yields both applicability and gated prediction
languages in the standard logspace-uniform NC¹ class. -/
theorem Correct.unknown_mem_uniformNC_one (h : A.Correct F L) (hq : 0 < q) (hR : 0 < R) (k : ℕ) :
    coneLanguage (fun T u => Sparse (residual (R := R) F L T u) k) ∈ UniformNCLevel 1 ∧
    coneLanguage (fun T u => Sparse (residual (R := R) F L T u) k ∧ h.value T u = true) ∈
      UniformNCLevel 1 := by
  constructor
  · rw [← lengthLanguage_eq_coneLanguage hq hR (A.unknownPredictor k) 0 _
      (fun T u => (h.unknown k T u).1)]
    exact A.unknownLanguage_mem_uniformNC_one k 0
  · rw [← lengthLanguage_eq_coneLanguage hq hR (A.unknownPredictor k) 1 _ (fun T u => by
      rw [(h.unknown k T u).2, Bool.and_eq_true, (h.unknown k T u).1])]
    exact A.unknownLanguage_mem_uniformNC_one k 1

/-- The logarithmic schedule yields the two corresponding standard
logspace-uniform NC¹ languages. -/
theorem Correct.scheduled_mem_uniformNC_one (h : A.Correct F L) (hq : 0 < q) (hR : 0 < R)
    (J : Schedule A) :
    coneLanguage (fun T u => Supported (residual (R := R) F L T u) (h.allowed J T)) ∈
      UniformNCLevel 1 ∧
    coneLanguage (fun T u => Supported (residual (R := R) F L T u) (h.allowed J T) ∧
      h.value T u = true) ∈ UniformNCLevel 1 := by
  constructor
  · rw [← lengthLanguage_eq_coneLanguage hq hR (A.scheduledPredictor J) 0 _
      (fun T u => (h.scheduled J T u).1)]
    exact A.scheduledLanguage_mem_uniformNC_one J 0
  · rw [← lengthLanguage_eq_coneLanguage hq hR (A.scheduledPredictor J) 1 _ (fun T u => by
      rw [(h.scheduled J T u).2, Bool.and_eq_true, (h.scheduled J T u).1])]
    exact A.scheduledLanguage_mem_uniformNC_one J 1

end UniformLayout
end PredictionDepth.SparseCorrections
