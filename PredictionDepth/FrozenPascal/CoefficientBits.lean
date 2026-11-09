import PredictionDepth.FrozenPascal.Decoder
import Mathlib.Data.Nat.Choose.Lucas

/-! A bitwise version of the coefficient table suitable for a uniform writer. -/

namespace PredictionDepth.FrozenPascal

open Linear (F₂)
open scoped BigOperators

theorem cast_nat_parity (n : ℕ) : (n : F₂) = bit (decide (n % 2 = 1)) := by
  have htwo : (2 : F₂) = 0 := rfl
  have h := congrArg (Nat.cast : ℕ → F₂) (Nat.mod_add_div n 2)
  push_cast at h
  rw [htwo, zero_mul, add_zero] at h
  rw [← h]
  have hcases : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hcases with hzero | hone
  · simp [hzero]
  · simp [hone]

def chooseParity (n k : ℕ) : Bool :=
  (List.range (max n k + 1)).all (fun i => !k.testBit i || n.testBit i)

theorem choose_digit (n k i : ℕ) :
    (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) =
      if !k.testBit i || n.testBit i then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hn : n / 2 ^ i % 2 = 0 ∨ n / 2 ^ i % 2 = 1 := by omega
  have hk : k / 2 ^ i % 2 = 0 ∨ k / 2 ^ i % 2 = 1 := by omega
  rcases hn with hn | hn <;> rcases hk with hk | hk <;> simp [hn, hk]

theorem chooseParity_correct (n k : ℕ) :
    (Nat.choose n k : F₂) = bit (chooseParity n k) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let a := max n k + 1
  have hmax : max n k < 2 ^ a :=
    (Nat.lt_succ_self _).trans (Nat.lt_two_pow_self (n := a))
  have hl := Choose.choose_modEq_prod_range_choose_nat (p := 2)
    ((le_max_left n k).trans_lt hmax) ((le_max_right n k).trans_lt hmax)
  change n.choose k % 2 =
    (∏ i ∈ Finset.range a, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2)) % 2 at hl
  simp only [choose_digit] at hl
  rw [cast_nat_parity, hl]
  cases hh : chooseParity n k
  · have hn : ¬ ∀ i ∈ List.range a, (!k.testBit i || n.testBit i) = true := by
      intro h
      have hh' : chooseParity n k = true := List.all_eq_true.mpr h
      rw [hh] at hh'
      cases hh'
    obtain ⟨i, hi, hf⟩ : ∃ i ∈ List.range a, (!k.testBit i || n.testBit i) = false := by
      by_contra h
      apply hn
      intro i hi
      cases he : (!k.testBit i || n.testBit i)
      · exact False.elim (h ⟨i, hi, he⟩)
      · rfl
    have hp : (∏ j ∈ Finset.range a, if !k.testBit j || n.testBit j then 1 else 0) = (0 : ℕ) :=
      Finset.prod_eq_zero (Finset.mem_range.mpr (List.mem_range.mp hi)) (by simp [hf])
    rw [hp]
    rfl
  · have h₁ : ∀ i ∈ Finset.range a, (!k.testBit i || n.testBit i) = true := by
      intro i hi
      exact List.all_eq_true.mp hh i (List.mem_range.mpr (Finset.mem_range.mp hi))
    have hp : (∏ j ∈ Finset.range a, if !k.testBit j || n.testBit j then 1 else 0) = (1 : ℕ) :=
      Finset.prod_eq_one (fun i hi => by simp [h₁ i hi])
    rw [hp]
    rfl

def directTableBit (u k s : ℕ) : Bool :=
  if k ≤ u then chooseParity (s + (u - k) - 1) (u - k) else false

/-- No entry of the decoder's coefficient table requires computing a large
binomial coefficient. Each entry is a conjunction of bit implications. -/
theorem directTableBit_eq (u k s : ℕ) : directTableBit u k s = tableBit u k s := by
  unfold directTableBit tableBit
  split
  · apply bit_injective
    rw [bit_ofBoolRing, Nat.multichoose_eq, chooseParity_correct]
  · rfl

end PredictionDepth.FrozenPascal
