import PredictionDepth.SparseCorrections.Semantics

/-!
# Chronological repair

A mismatch in an output bit can be repaired as soon as all earlier updates
are correct. The first failed local check therefore identifies the first
missing residual bit. Repeating this operation avoids enumerating supports.
-/

namespace PredictionDepth.SparseCorrections

variable {w : ℕ → ℕ} {T : ℕ}

/-- Forced trajectories with equal past corrections have equal current states. -/
theorem forcedLayer_congr_past (L : Transition w) (u : Layer w 0)
    {e f : Residual w T} (t : ℕ) (ht : t ≤ T)
    (h : ∀ v : Event w T, v.1.val < t → e v = f v) :
    forcedLayer L u e t ht = forcedLayer L u f t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := ih (by omega) (fun v hv => h v (by omega))
    funext i
    simp only [forcedLayer, hp, h ⟨⟨t, by omega⟩, i⟩ (by simp)]

/-- A rank can order the bits within a layer arbitrarily, but all earlier
layers must precede every bit in a later layer. -/
structure EventOrder (w : ℕ → ℕ) (T : ℕ) where
  rank : Event w T → ℕ
  injective : Function.Injective rank
  chronological : ∀ v z : Event w T, v.1.val < z.1.val → rank v < rank z

def Passes (F L : Transition w) (u : Layer w 0) (e : Residual w T)
    (v : Event w T) : Prop :=
  forcedTrajectory L u e v.1.succ v.2 = F v.1 (forcedTrajectory L u e v.1.castSucc) v.2

theorem passes_iff_eq_of_past (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) (v : Event w T)
    (h : ∀ z : Event w T, z.1.val < v.1.val → e z = actualResidual F L u z) :
    Passes F L u e v ↔ e v = actualResidual F L u v := by
  have he := forcedLayer_congr_past L u v.1.val v.1.isLt.le h
  have hy : forcedTrajectory L u e v.1.castSucc = actualTrajectory F u v.1.castSucc := by
    rw [← reconstruct_actualResidual (T := T) F L u]
    exact he
  unfold Passes
  rw [forcedTrajectory_succ, hy]
  obtain ⟨t, i⟩ := v
  -- The local reference and actual output are the same bits on both sides.
  simp only [actualTrajectory, Fin.val_castSucc, actualResidual, actualLayer]
  cases e ⟨t, i⟩ <;> cases L t (actualLayer F u t) i <;>
    cases F t (actualLayer F u t) i <;> decide

theorem passes_prefix_iff (o : EventOrder w T) (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) (b : ℕ) :
    (∀ v, o.rank v < b → Passes F L u e v) ↔
      (∀ v, o.rank v < b → e v = actualResidual F L u v) := by
  constructor
  · intro h v hv
    induction hr : o.rank v using Nat.strongRecOn generalizing v with
    | ind r ih =>
      apply (passes_iff_eq_of_past F L u e v ?_).mp (h v hv)
      intro z hz
      have hlt := o.chronological z v hz
      exact ih (o.rank z) (by omega) z (by omega) rfl
  · intro h v hv
    apply (passes_iff_eq_of_past F L u e v ?_).mpr (h v hv)
    intro z hz
    exact h z ((o.chronological z v hz).trans hv)

def FirstFailure (o : EventOrder w T) (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) (v : Event w T) : Prop :=
  ¬ Passes F L u e v ∧ ∀ z, o.rank z < o.rank v → Passes F L u e z

theorem firstFailure_iff (o : EventOrder w T) (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) (v : Event w T) :
    FirstFailure o F L u e v ↔
      e v ≠ actualResidual F L u v ∧
        ∀ z, o.rank z < o.rank v → e z = actualResidual F L u z := by
  unfold FirstFailure
  rw [passes_prefix_iff]
  constructor <;> rintro ⟨hne, hp⟩ <;> refine ⟨?_, hp⟩
  · exact fun he => hne ((passes_iff_eq_of_past F L u e v
      (fun z hz => hp z (o.chronological z v hz))).mpr he)
  · exact fun he => hne ((passes_iff_eq_of_past F L u e v
      (fun z hz => hp z (o.chronological z v hz))).mp he)

instance (F L : Transition w) (u : Layer w 0) (e : Residual w T) (v : Event w T) :
    Decidable (Passes F L u e v) :=
  inferInstanceAs (Decidable (_ = _))

instance (o : EventOrder w T) (F L : Transition w) (u : Layer w 0) (e : Residual w T)
    (v : Event w T) : Decidable (FirstFailure o F L u e v) :=
  inferInstanceAs (Decidable (_ ∧ ∀ z : Event w T, _ → Passes F L u e z))

/-- Toggle only the first failed bit. Each decision is a local mismatch
combined with a prefix conjunction, so all toggles can be computed in parallel. -/
def repair (o : EventOrder w T) (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) : Residual w T :=
  fun v => if FirstFailure o F L u e v then !e v else e v

def differences (e f : Residual w T) : Finset (Event w T) :=
  Finset.univ.filter fun v => e v ≠ f v

@[simp] theorem mem_differences {e f : Residual w T} {v : Event w T} :
    v ∈ differences e f ↔ e v ≠ f v := by simp [differences]

theorem differences_eq_empty_iff {e f : Residual w T} :
    differences e f = ∅ ↔ e = f := by
  simp [Finset.eq_empty_iff_forall_notMem, funext_iff]

private theorem firstFailure_exists (o : EventOrder w T) (F L : Transition w)
    (u : Layer w 0) (e : Residual w T) (h : e ≠ actualResidual F L u) :
    ∃ v, FirstFailure o F L u e v := by
  classical
  have hex : ∃ v, e v ≠ actualResidual F L u v := by simpa [funext_iff] using h
  have hexRank : ∃ r, ∃ v, o.rank v = r ∧ e v ≠ actualResidual F L u v := by
    obtain ⟨v, hv⟩ := hex
    exact ⟨o.rank v, v, rfl, hv⟩
  obtain ⟨v, hv, hvne⟩ := Nat.find_spec hexRank
  refine ⟨v, (firstFailure_iff o F L u e v).mpr ⟨hvne, ?_⟩⟩
  intro z hz
  by_contra hne
  have hmin := Nat.find_min' hexRank ⟨z, rfl, hne⟩
  omega

private theorem firstFailure_unique (o : EventOrder w T) (F L : Transition w)
    (u : Layer w 0) (e : Residual w T) {v z : Event w T}
    (hv : FirstFailure o F L u e v) (hz : FirstFailure o F L u e z) : v = z := by
  apply o.injective
  rcases lt_trichotomy (o.rank v) (o.rank z) with h | h | h
  · exact False.elim (hv.1 (hz.2 v h))
  · exact h
  · exact False.elim (hz.1 (hv.2 z h))

theorem repair_distance (o : EventOrder w T) (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) :
    (differences (repair o F L u e) (actualResidual F L u)).card =
      (differences e (actualResidual F L u)).card - 1 := by
  by_cases he : e = actualResidual F L u
  · have hrepair : repair o F L u e = e := by
      funext v
      have hn : ¬ FirstFailure o F L u e v := by
        rw [firstFailure_iff, he]
        simp
      simp [repair, hn]
    rw [hrepair, differences_eq_empty_iff.mpr he]
    rfl
  · obtain ⟨v, hv⟩ := firstFailure_exists o F L u e he
    have hvne := ((firstFailure_iff o F L u e v).mp hv).1
    have hvflip : (!e v) = actualResidual F L u v := by
      cases hv₁ : e v <;> cases hv₂ : actualResidual F L u v <;> simp_all
    have hdiff : differences (repair o F L u e) (actualResidual F L u) =
        (differences e (actualResidual F L u)).erase v := by
      ext z
      by_cases hz : z = v
      · subst z
        simp [repair, hv, hvflip]
      · have hnf : ¬ FirstFailure o F L u e z := fun h =>
          hz (firstFailure_unique o F L u e h hv)
        simp [repair, hnf, hz]
    rw [hdiff, Finset.card_erase_of_mem (mem_differences.mpr hvne)]

theorem iterate_repair_distance (o : EventOrder w T) (F L : Transition w) (u : Layer w 0)
    (e : Residual w T) (k : ℕ) :
    (differences ((repair o F L u)^[k] e) (actualResidual F L u)).card =
      (differences e (actualResidual F L u)).card - k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', repair_distance, ih]
    omega

/-- Starting with zero, precisely the residuals of weight at most `k`
are completely repaired by round `k`. The final full verifier decides
applicability even on trajectories that exceed the budget. -/
theorem repair_accept_iff (o : EventOrder w T) (F L : Transition w)
    (u : Layer w 0) (k : ℕ) :
    Valid F (forcedTrajectory L u ((repair o F L u)^[k] (fun _ => false))) ↔
      Sparse (actualResidual F L u : Residual w T) k := by
  rw [valid_iff_eq_actualResidual, ← differences_eq_empty_iff, ← Finset.card_eq_zero,
    iterate_repair_distance]
  have hzero : differences (fun _ => false) (actualResidual F L u : Residual w T) =
      support (actualResidual F L u) := by
    ext v
    cases h : actualResidual F L u v <;> simp [h]
  rw [hzero, Nat.sub_eq_zero_iff_le]
  rfl

end PredictionDepth.SparseCorrections
