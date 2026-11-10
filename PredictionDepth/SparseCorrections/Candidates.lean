import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Card

/-! Explicit candidate indices for unknown and scheduled correction positions. -/

namespace PredictionDepth.SparseCorrections

def encodedSupport (e : Fin M → Bool) : Finset (Fin M) :=
  Finset.univ.filter fun i => e i = true

@[simp] theorem mem_encodedSupport (e : Fin M → Bool) (i : Fin M) :
    i ∈ encodedSupport e ↔ e i = true := by simp [encodedSupport]

/-- The digit zero is padding. The nonzero digit `i + 1` names event `i`. -/
def unknownBit (M k j i : ℕ) : Bool :=
  (List.range k).any fun p => j / (M + 1) ^ p % (M + 1) == i + 1

def unknownCandidates (M k : ℕ) (j : Fin ((M + 1) ^ k)) (i : Fin M) : Bool :=
  unknownBit M k j.val i.val

theorem unknownCandidates_true_iff (j : Fin ((M + 1) ^ k)) (i : Fin M) :
    unknownCandidates M k j i = true ↔
      ∃ p : Fin k, finFunctionFinEquiv.symm j p = i.succ := by
  simp only [unknownCandidates, unknownBit, List.any_eq_true, List.mem_range, beq_iff_eq,
    Fin.ext_iff, finFunctionFinEquiv_symm_apply_val, Fin.val_succ]
  exact ⟨fun ⟨p, hp, hi⟩ => ⟨⟨p, hp⟩, hi⟩, fun ⟨p, hp⟩ => ⟨p.val, p.isLt, hp⟩⟩

theorem unknownCandidates_card_le (j : Fin ((M + 1) ^ k)) :
    (encodedSupport (unknownCandidates M k j)).card ≤ k := by
  classical
  let s := encodedSupport (unknownCandidates M k j)
  have h : s.image Fin.succ ⊆ (Finset.univ : Finset (Fin k)).image (finFunctionFinEquiv.symm j) := by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨p, hp⟩ := (unknownCandidates_true_iff j a).mp ((mem_encodedSupport _ _).mp ha)
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp⟩
  calc
    s.card = (s.image Fin.succ).card := (Finset.card_image_of_injective _ (Fin.succ_injective M)).symm
    _ ≤ ((Finset.univ : Finset (Fin k)).image (finFunctionFinEquiv.symm j)).card :=
      Finset.card_le_card h
    _ ≤ k := by
      exact Finset.card_image_le.trans (by simp)

theorem exists_unknownCandidate_iff (e : Fin M → Bool) :
    (∃ j, unknownCandidates M k j = e) ↔ (encodedSupport e).card ≤ k := by
  constructor
  · rintro ⟨j, rfl⟩
    exact unknownCandidates_card_le j
  · intro h
    classical
    let s := encodedSupport e
    let index : s ≃ Fin s.card := Fintype.equivFinOfCardEq (by simp)
    let digits (p : Fin k) : Fin (M + 1) :=
      if hp : p.val < s.card then (index.symm ⟨p.val, hp⟩).val.succ else 0
    refine ⟨finFunctionFinEquiv digits, funext (fun i => Bool.eq_iff_iff.mpr ?_)⟩
    rw [unknownCandidates_true_iff, finFunctionFinEquiv.symm_apply_apply]
    constructor
    · rintro ⟨p, hp⟩
      unfold digits at hp
      split at hp
      · have he := Fin.succ_injective M hp
        rw [← he]
        exact (mem_encodedSupport _ _).mp (Subtype.property (index.symm _))
      · have he := congrArg Fin.val hp
        simp at he
    · intro hi
      let p := index ⟨i, (mem_encodedSupport _ _).mpr hi⟩
      refine ⟨⟨p.val, p.isLt.trans_le h⟩, ?_⟩
      unfold digits
      rw [dite_eq_left p.isLt, Fin.eta]
      simp

/-- The padded tuple enumeration can repeat a vector. The number of distinct
vectors of weight at most `k` is at most the number of tuples. -/
theorem sparseCandidates_card_le (M k : ℕ) :
    (Finset.univ.filter (fun e : Fin M → Bool => (encodedSupport e).card ≤ k)).card ≤
      (M + 1) ^ k := by
  classical
  have h : Finset.univ.filter (fun e : Fin M → Bool => (encodedSupport e).card ≤ k) =
      Finset.univ.image (unknownCandidates M k) := by
    ext e
    simp [exists_unknownCandidate_iff]
  rw [h]
  exact Finset.card_image_le.trans (by simp)

/-- Every schedule position gets one assignment bit. A repeated event address
is allowed and interpreted as the OR of its assigned bits. -/
def scheduledCandidates (slot : Fin K → Fin M) (j : Fin (2 ^ K)) (i : Fin M) : Bool :=
  decide (∃ p : Fin K, slot p = i ∧ j.val.testBit p.val = true)

theorem exists_scheduledCandidate_iff (slot : Fin K → Fin M) (e : Fin M → Bool) :
    (∃ j, scheduledCandidates slot j = e) ↔
      ∀ i, e i = true → ∃ p, slot p = i := by
  constructor
  · rintro ⟨j, rfl⟩ i hi
    obtain ⟨p, hp, _⟩ := of_decide_eq_true hi
    exact ⟨p, hp⟩
  · intro hs
    let digits (p : Fin K) : Fin 2 := if e (slot p) then 1 else 0
    refine ⟨finFunctionFinEquiv digits, funext (fun i => Bool.eq_iff_iff.mpr ?_)⟩
    have hbit (p : Fin K) : (finFunctionFinEquiv digits).val.testBit p.val = e (slot p) := by
      rw [Nat.testBit_eq_decide_div_mod_eq, ← finFunctionFinEquiv_symm_apply_val,
        finFunctionFinEquiv.symm_apply_apply]
      cases h : e (slot p) <;> simp [digits, h]
    simp only [scheduledCandidates, decide_eq_true_eq, hbit]
    constructor
    · rintro ⟨p, rfl, hp⟩
      exact hp
    · intro hi
      obtain ⟨p, rfl⟩ := hs i hi
      exact ⟨p, rfl, hi⟩

theorem scheduledCandidates_injective {slot : Fin K → Fin M} (hslot : Function.Injective slot) :
    Function.Injective (scheduledCandidates slot) := by
  intro j l h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < K
  · let i : Fin K := ⟨p, hp⟩
    have hbit (z : Fin (2 ^ K)) :
        scheduledCandidates slot z (slot i) = z.val.testBit p := by
      apply Bool.eq_iff_iff.mpr
      simp [scheduledCandidates, hslot.eq_iff, i]
    rw [← hbit j, ← hbit l, h]
  · have hb := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hp)
    rw [Nat.testBit_lt_two_pow (j.isLt.trans_le hb), Nat.testBit_lt_two_pow (l.isLt.trans_le hb)]

theorem scheduledCandidates_card {slot : Fin K → Fin M} (hslot : Function.Injective slot) :
    (Finset.univ.image (scheduledCandidates slot)).card = 2 ^ K := by
  rw [Finset.card_image_of_injective _ (scheduledCandidates_injective hslot)]
  simp

end PredictionDepth.SparseCorrections
