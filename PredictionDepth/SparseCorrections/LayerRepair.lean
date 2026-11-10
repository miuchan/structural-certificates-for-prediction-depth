import PredictionDepth.SparseCorrections.Repair

/-! Chronological repair with a budget on the number of nonzero update layers. -/

namespace PredictionDepth.SparseCorrections

variable {w : ℕ → ℕ} {T : ℕ}

theorem passes_before_layer_iff (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) (b : ℕ) :
    (∀ v, v.1.val < b → Passes F L u e v) ↔
      (∀ v, v.1.val < b → e v = actualResidual F L u v) := by
  constructor
  · intro h v hv
    induction ht : v.1.val using Nat.strongRecOn generalizing v with
    | ind t ih =>
      apply (passes_iff_eq_of_past F L u e v ?_).mp (h v hv)
      intro z hz
      exact ih z.1.val (by omega) z (by omega) rfl
  · intro h v hv
    apply (passes_iff_eq_of_past F L u e v ?_).mpr (h v hv)
    intro z hz
    exact h z (hz.trans hv)

/-- Select every failing bit at the earliest update time with a failure. -/
def FirstLayerFailure (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) (v : Event w T) : Prop :=
  ¬ Passes F L u e v ∧ ∀ z, z.1.val < v.1.val → Passes F L u e z

instance (F L : Transition w) (u : Layer w 0) (e : Residual w T)
    (v : Event w T) : Decidable (FirstLayerFailure F L u e v) :=
  inferInstanceAs (Decidable (_ ∧ ∀ z : Event w T, _ → Passes F L u e z))

theorem firstLayerFailure_iff (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) (v : Event w T) :
    FirstLayerFailure F L u e v ↔
      e v ≠ actualResidual F L u v ∧
        ∀ z, z.1.val < v.1.val → e z = actualResidual F L u z := by
  unfold FirstLayerFailure
  rw [passes_before_layer_iff]
  constructor <;> rintro ⟨hne, hp⟩ <;> refine ⟨?_, hp⟩
  · exact fun he => hne ((passes_iff_eq_of_past F L u e v hp).mpr he)
  · exact fun he => hne ((passes_iff_eq_of_past F L u e v hp).mp he)

/-- The correction bits flipped by one whole-layer repair round. -/
def repairLayer (F L : Transition w) (u : Layer w 0) (e : Residual w T) : Residual w T :=
  fun v => if FirstLayerFailure F L u e v then !e v else e v

/-- Update times where the two correction vectors differ in at least one bit. -/
def layerDifferences (e f : Residual w T) : Finset (Fin T) :=
  Finset.univ.filter fun t => ∃ i : Fin (w (t.val + 1)), e ⟨t, i⟩ ≠ f ⟨t, i⟩

@[simp] theorem mem_layerDifferences {e f : Residual w T} {t : Fin T} :
    t ∈ layerDifferences e f ↔ ∃ i : Fin (w (t.val + 1)), e ⟨t, i⟩ ≠ f ⟨t, i⟩ := by
  simp [layerDifferences]

theorem layerDifferences_eq_empty_iff {e f : Residual w T} :
    layerDifferences e f = ∅ ↔ e = f := by
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [mem_layerDifferences, not_exists, not_not]
  exact ⟨fun h => funext fun v => h v.1 v.2, fun h t i => congrFun h ⟨t, i⟩⟩

/-- Update times whose correction vector has a nonzero bit. -/
def layerSupport (e : Residual w T) : Finset (Fin T) :=
  layerDifferences (fun _ => false) e

@[simp] theorem mem_layerSupport {e : Residual w T} {t : Fin T} :
    t ∈ layerSupport e ↔ ∃ i : Fin (w (t.val + 1)), e ⟨t, i⟩ = true := by
  rw [layerSupport, mem_layerDifferences]
  apply exists_congr
  intro i
  cases e ⟨t, i⟩ <;> decide

private theorem firstLayerFailure_exists (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) (he : e ≠ actualResidual F L u) :
    ∃ v, FirstLayerFailure F L u e v := by
  classical
  have hex : ∃ v, e v ≠ actualResidual F L u v := by simpa [funext_iff] using he
  have ht : ∃ t, ∃ v, v.1.val = t ∧ e v ≠ actualResidual F L u v := by
    obtain ⟨v, hv⟩ := hex
    exact ⟨v.1.val, v, rfl, hv⟩
  obtain ⟨v, hv, hvne⟩ := Nat.find_spec ht
  refine ⟨v, (firstLayerFailure_iff F L u e v).mpr ⟨hvne, ?_⟩⟩
  intro z hz
  by_contra hne
  have hmin := Nat.find_min' ht ⟨z, rfl, hne⟩
  omega

private theorem firstLayerFailure_time_unique {F L : Transition w} {u : Layer w 0}
    {e : Residual w T} {v z : Event w T}
    (hv : FirstLayerFailure F L u e v) (hz : FirstLayerFailure F L u e z) : v.1 = z.1 := by
  apply Fin.ext
  rcases lt_trichotomy v.1.val z.1.val with h | h | h
  · exact False.elim (hv.1 (hz.2 v h))
  · exact h
  · exact False.elim (hz.1 (hv.2 z h))

private theorem repairLayer_bit_eq_of_earlier_correct (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) (v : Event w T)
    (hp : ∀ z, z.1.val < v.1.val → e z = actualResidual F L u z) :
    repairLayer F L u e v = actualResidual F L u v := by
  by_cases he : e v = actualResidual F L u v
  · have hn : ¬ FirstLayerFailure F L u e v := fun h =>
      ((firstLayerFailure_iff F L u e v).mp h).1 he
    simp [repairLayer, hn, he]
  · have hf := (firstLayerFailure_iff F L u e v).mpr ⟨he, hp⟩
    unfold repairLayer
    rw [ite_eq_left hf]
    cases hv : e v <;> cases ha : actualResidual F L u v <;> simp_all

/-- One round removes exactly one differing layer when any difference remains. -/
theorem repairLayer_distance (F L : Transition w) (u : Layer w 0) (e : Residual w T) :
    (layerDifferences (repairLayer F L u e) (actualResidual F L u)).card =
      (layerDifferences e (actualResidual F L u)).card - 1 := by
  by_cases he : e = actualResidual F L u
  · have hrepair : repairLayer F L u e = e := by
      funext v
      exact (repairLayer_bit_eq_of_earlier_correct F L u e v (fun z _ => congrFun he z)).trans
        (congrFun he v).symm
    rw [hrepair, layerDifferences_eq_empty_iff.mpr he]
    rfl
  · obtain ⟨v, hv⟩ := firstLayerFailure_exists F L u e he
    obtain ⟨hvne, hp⟩ := (firstLayerFailure_iff F L u e v).mp hv
    have hdiff : layerDifferences (repairLayer F L u e) (actualResidual F L u) =
        (layerDifferences e (actualResidual F L u)).erase v.1 := by
      ext t
      by_cases ht : t = v.1
      · subst t
        have heq (i : Fin (w (v.1.val + 1))) :
            repairLayer F L u e ⟨v.1, i⟩ = actualResidual F L u ⟨v.1, i⟩ :=
          repairLayer_bit_eq_of_earlier_correct F L u e ⟨v.1, i⟩ hp
        simp [heq]
      · have hsame (i : Fin (w (t.val + 1))) : repairLayer F L u e ⟨t, i⟩ = e ⟨t, i⟩ := by
          have hn : ¬ FirstLayerFailure F L u e ⟨t, i⟩ := fun h =>
            ht (firstLayerFailure_time_unique h hv)
          simp [repairLayer, hn]
        simp [hsame, ht]
    rw [hdiff, Finset.card_erase_of_mem (mem_layerDifferences.mpr ⟨v.2, hvne⟩)]

theorem iterate_repairLayer_distance (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) (k : ℕ) :
    (layerDifferences ((repairLayer F L u)^[k] e) (actualResidual F L u)).card =
      (layerDifferences e (actualResidual F L u)).card - k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', repairLayer_distance, ih]
    omega

/-- Starting with zero, a budget of k rounds succeeds precisely when at
most k update layers contain a nonzero correction bit. -/
theorem repairLayer_accept_iff (F L : Transition w) (u : Layer w 0) (k : ℕ) :
    Valid F (forcedTrajectory L u ((repairLayer (T := T) F L u)^[k] (fun _ => false))) ↔
      (layerSupport (actualResidual F L u : Residual w T)).card ≤ k := by
  rw [valid_iff_eq_actualResidual, ← layerDifferences_eq_empty_iff, ← Finset.card_eq_zero,
    iterate_repairLayer_distance, Nat.sub_eq_zero_iff_le]
  rfl

end PredictionDepth.SparseCorrections
