import PredictionDepth.SparseCorrections.Length
import Mathlib.Algebra.BigOperators.Fin

/-! Dense, chronological addresses for the shrinking cone. -/

namespace PredictionDepth.SparseCorrections.Cone

open Cslib Turing.MultiTapeTM StandardComplexity

/-- Number of bits in the layers strictly before `t`, for `t ≤ T+1`. -/
def offset (q R T t : ℕ) : ℕ := q * t * (R * (2 * T + 1 - t) + 1)

theorem offset_succ (q R T t : ℕ) (ht : t ≤ T) :
    offset q R T (t + 1) = offset q R T t + coneWidth q R T t := by
  have h₁ : 2 * T + 1 - (t + 1) = 2 * (T - t) + t := by omega
  have h₂ : 2 * T + 1 - t = 2 * (T - t) + t + 1 := by omega
  simp only [offset, coneWidth, h₁, h₂]
  ring

theorem offset_eq_sum (q R T t : ℕ) (ht : t ≤ T + 1) :
    offset q R T t = ∑ i : Fin t, coneWidth q R T i.val := by
  induction t with
  | zero => simp [offset]
  | succ t ih =>
    rw [offset_succ q R T t (by omega), ih (by omega), Fin.sum_univ_castSucc]
    rfl

def stateCount (q R T : ℕ) : ℕ := offset q R T (T + 1)

def eventCount (q R T : ℕ) : ℕ := offset q R (T - 1) T

theorem stateCount_eq (q R T : ℕ) : stateCount q R T = q * (T + 1) * (R * T + 1) := by
  simp [stateCount, offset, show 2 * T + 1 - (T + 1) = T by omega]

theorem eventCount_eq (q R T : ℕ) : eventCount q R T = q * T * (R * (T - 1) + 1) := by
  cases T with
  | zero => simp [eventCount, offset]
  | succ T =>
    simp only [eventCount, offset, show 2 * (T.succ - 1) + 1 - T.succ = T.succ - 1 by omega]

def stateIndex (q R T : ℕ) :
    ((t : Fin (T + 1)) × Fin (coneWidth q R T t.val)) ≃ Fin (stateCount q R T) :=
  finSigmaFinEquiv.trans (finCongr (offset_eq_sum q R T (T + 1) le_rfl).symm)

theorem stateIndex_val (q R T : ℕ) (t : Fin (T + 1)) (i : Fin (coneWidth q R T t.val)) :
    (stateIndex q R T ⟨t, i⟩).val = offset q R T t.val + i.val := by
  change (finSigmaFinEquiv (n := fun s : Fin (T + 1) => coneWidth q R T s.val) ⟨t, i⟩ : ℕ) = _
  rw [finSigmaFinEquiv_apply, offset_eq_sum q R T t.val (by omega)]
  rfl

private theorem event_width (q R T : ℕ) (t : Fin T) :
    coneWidth q R T (t.val + 1) = coneWidth q R (T - 1) t.val := by
  simp only [coneWidth, show T - (t.val + 1) = T - 1 - t.val by omega]

def eventIndex (q R T : ℕ) : Event (coneWidth q R T) T ≃ Fin (eventCount q R T) :=
  (Equiv.sigmaCongrRight (fun t => finCongr (event_width q R T t))).trans
    (finSigmaFinEquiv.trans (finCongr (offset_eq_sum q R (T - 1) T (by omega)).symm))

theorem eventIndex_val (q R T : ℕ) (t : Fin T) (i : Fin (coneWidth q R T (t.val + 1))) :
    (eventIndex q R T ⟨t, i⟩).val = offset q R (T - 1) t.val + i.val := by
  change (finSigmaFinEquiv (n := fun s : Fin T => coneWidth q R (T - 1) s.val)
    ⟨t, Fin.cast (event_width q R T t) i⟩ : ℕ) = _
  rw [finSigmaFinEquiv_apply, offset_eq_sum q R (T - 1) t.val (by omega)]
  rfl

theorem offset_logspace (q R : ℕ) :
    ComputableInLogSpace (fun p : ℕ × ℕ => offset q R p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have ht := ComputableInLogSpace.snd encUnary encUnary
  have hspan := ((hT.unaryMulConst 2).unaryAdd (ComputableInLogSpace.const 1)).unarySub ht
  have hw := (hspan.unaryMulConst R).unaryAdd (ComputableInLogSpace.const 1)
  exact ((ht.unaryMulConst q).unaryMul hw).congr_fun fun _ => by simp [offset, Nat.mul_comm]

theorem stateCount_logspace (q R : ℕ) :
    ComputableInLogSpace (stateCount q R) encUnary encUnary :=
  (offset_logspace q R).comp (ComputableInLogSpace.id.pair
    (ComputableInLogSpace.id.unaryAdd (ComputableInLogSpace.const 1)))

theorem eventCount_logspace (q R : ℕ) :
    ComputableInLogSpace (eventCount q R) encUnary encUnary :=
  (offset_logspace q R).comp
    ((ComputableInLogSpace.id.unarySub (ComputableInLogSpace.const 1)).pair ComputableInLogSpace.id)

theorem eventCount_polynomial (q R T : ℕ) :
    eventCount q R T + 1 ≤ (q * (R + 1) + 1) * (T + 1) ^ 2 := by
  rw [eventCount_eq]
  have h₁ : q * T ≤ q * (T + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
  have h₂ : R * (T - 1) + 1 ≤ (R + 1) * (T + 1) := by
    have := Nat.mul_le_mul_left R (Nat.sub_le T 1)
    nlinarith
  have h := Nat.mul_le_mul h₁ h₂
  nlinarith

/-- Count the completed layers by comparing their end addresses to `j`.
Indices used by the circuit are all within a layer; the decoder is total. -/
def layerOf (q R H j : ℕ) : ℕ :=
  ((List.range H).filter fun t => decide (offset q R H (t + 1) ≤ j)).length

private theorem offset_mono {q R H a b : ℕ} (hab : a ≤ b) (hb : b ≤ H + 1) :
    offset q R H a ≤ offset q R H b := by
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | succ b ih =>
    by_cases h : a = b + 1
    · simp [h]
    · rw [offset_succ q R H b (by omega)]
      exact (ih (by omega) (by omega)).trans (Nat.le_add_right _ _)

/-- Dense event addresses respect the order of update times. -/
theorem eventIndex_chronological (q R T : ℕ) (v z : Event (coneWidth q R T) T)
    (h : v.1.val < z.1.val) : eventIndex q R T v < eventIndex q R T z := by
  rcases v with ⟨t, i⟩
  rcases z with ⟨s, j⟩
  have hs := s.isLt
  have ht := t.isLt
  change t.val < s.val at h
  change (eventIndex q R T ⟨t, i⟩).val < (eventIndex q R T ⟨s, j⟩).val
  rw [eventIndex_val, eventIndex_val]
  calc
    _ < offset q R (T - 1) (t.val + 1) := by
      rw [offset_succ q R (T - 1) t.val (by omega), ← event_width q R T t]
      exact Nat.add_lt_add_left i.isLt _
    _ ≤ offset q R (T - 1) s.val := offset_mono (by omega) (by omega)
    _ ≤ _ := Nat.le_add_right _ _

private theorem filter_range_below (m t : ℕ) (h : t ≤ m) :
    ((List.range m).filter fun j => decide (j < t)) = List.range t := by
  induction m with
  | zero =>
    obtain rfl : t = 0 := by omega
    rfl
  | succ m ih =>
    by_cases he : t = m + 1
    · subst t
      exact List.filter_eq_self.mpr fun j hj => decide_eq_true (List.mem_range.mp hj)
    · rw [List.range_succ, List.filter_append, ih (by omega)]
      simp [show ¬m < t by omega]

private theorem layerOf_eq {q R H t j : ℕ} (ht : t ≤ H)
    (hl : offset q R H t ≤ j) (hr : j < offset q R H (t + 1)) :
    layerOf q R H j = t := by
  have hfilter :
      ((List.range H).filter fun s => decide (offset q R H (s + 1) ≤ j)) =
        ((List.range H).filter fun s => decide (s < t)) := by
    apply List.filter_congr
    intro s hs
    by_cases h : s < t
    · have hle := (offset_mono (q := q) (R := R) (H := H)
        (show s + 1 ≤ t by omega) (by omega)).trans hl
      simp [h, hle]
    · have hmono := offset_mono (q := q) (R := R) (H := H)
        (show t + 1 ≤ s + 1 by omega) (show s + 1 ≤ H + 1 by have := List.mem_range.mp hs; omega)
      simp [h, not_le_of_gt (hr.trans_le hmono)]
  simp [layerOf, hfilter, filter_range_below H t ht]

theorem layerOf_stateIndex (q R T : ℕ) (_hq : 0 < q) (t : Fin (T + 1))
    (i : Fin (coneWidth q R T t.val)) :
    layerOf q R T (stateIndex q R T ⟨t, i⟩).val = t.val := by
  rw [stateIndex_val]
  apply layerOf_eq (show t.val ≤ T by omega) (Nat.le_add_right _ _)
  rw [offset_succ q R T t.val (by omega)]
  exact Nat.add_lt_add_left i.isLt _

theorem layerOf_eventIndex (q R T : ℕ) (_hq : 0 < q) (t : Fin T)
    (i : Fin (coneWidth q R T (t.val + 1))) :
    layerOf q R (T - 1) (eventIndex q R T ⟨t, i⟩).val = t.val := by
  rw [eventIndex_val]
  apply layerOf_eq (show t.val ≤ T - 1 by omega) (Nat.le_add_right _ _)
  rw [offset_succ q R (T - 1) t.val (by omega), ← event_width q R T t]
  exact Nat.add_lt_add_left i.isLt _

theorem layerOf_logspace (q R : ℕ) :
    ComputableInLogSpace (fun p : ℕ × ℕ => layerOf q R p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  let e := encPair encUnary encUnary
  have hH := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  have hp := ComputableInLogSpace.fst e encUnary
  have ht := ComputableInLogSpace.snd e encUnary
  have ho := (offset_logspace q R).comp
    ((hH.comp hp).pair (ht.unaryAdd (ComputableInLogSpace.const 1)))
  have hword : ComputableInLogSpace
      (fun p : (ℕ × ℕ) × ℕ => if offset q R p.1.1 (p.2 + 1) ≤ p.1.2 then [true] else [])
      (encPair e encUnary) encBits :=
    ((ho.unaryLe (hj.comp hp)).ite (ComputableInLogSpace.const [true])
      (ComputableInLogSpace.const [])).congr_fun fun _ => by simp only [decide_eq_true_eq,
        Function.comp_apply]
  exact (CodeLogspace.bitsLength.comp (LogspaceBatch.flatMap_range hH hword)).congr_fun fun p => by
    unfold layerOf
    change ((List.range p.1).filter _).length = ((List.range p.1).flatMap _).length
    induction List.range p.1 with
    | nil => rfl
    | cons a l ih =>
      by_cases h : offset q R p.1 (a + 1) ≤ p.2 <;> simp [h, ih]

end PredictionDepth.SparseCorrections.Cone
