import PredictionDepth.Linear
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
# One-sided cellular automata with frozen controls

Each site carries a frozen control symbol and a mutable bit. The control chooses
whether the bit at that site survives, and whether the bit to its right enters.
The local rule is identical at every site. The controls can vary arbitrarily
over the input configuration.

A length-`t` path arriving at displacement `k` crosses exactly the first `k`
edges. The remaining `t-k` steps are stays, distributed in order among the
enabled sites in the inclusive interval. This produces a multichoose
coefficient, cast into the two-element ring.
-/

namespace PredictionDepth.FrozenPascal

open scoped BigOperators
open Linear (F₂)

abbrev Config (Q : Type*) := (ℤ → Q) × (ℤ → F₂)

def bit (b : Bool) : F₂ := if b then 1 else 0

@[simp] theorem bit_false : bit false = 0 := rfl
@[simp] theorem bit_true : bit true = 1 := rfl

def step {Q : Type*} (stay hop : Q → Bool) (x : Config Q) : Config Q :=
  (x.1, fun i => bit (stay (x.1 i)) * x.2 i + bit (hop (x.1 i)) * x.2 (i + 1))

def enabled {Q : Type*} (stay : Q → Bool) (a : ℤ → Q) (i : ℤ) : ℕ → ℕ
  | 0 => (stay (a i)).toNat
  | k + 1 => (stay (a i)).toNat + enabled stay a (i + 1) k

def edgeProduct {Q : Type*} (hop : Q → Bool) (a : ℤ → Q) (i : ℤ) : ℕ → F₂
  | 0 => 1
  | k + 1 => bit (hop (a i)) * edgeProduct hop a (i + 1) k

def coefficient {Q : Type*} (stay hop : Q → Bool) (a : ℤ → Q)
    (i : ℤ) (t k : ℕ) : F₂ :=
  if k ≤ t then edgeProduct hop a i k * (Nat.multichoose (enabled stay a i k) (t - k) : F₂)
  else 0

variable {Q : Type*} (stay hop : Q → Bool) (a : ℤ → Q)

theorem enabled_le (i : ℤ) (k : ℕ) : enabled stay a i k ≤ k + 1 := by
  induction k generalizing i with
  | zero =>
    cases h : stay (a i) <;> simp [enabled, h]
  | succ k ih =>
    have := ih (i + 1)
    cases h : stay (a i) <;> simp [enabled, h] <;> omega

theorem coefficient_of_lt (i : ℤ) {t k : ℕ} (h : t < k) :
    coefficient stay hop a i t k = 0 := by
  simp [coefficient, Nat.not_le_of_lt h]

@[simp] theorem coefficient_time_zero (i : ℤ) :
    coefficient stay hop a i 0 0 = 1 := by
  simp [coefficient, edgeProduct]

theorem coefficient_zero_succ (i : ℤ) (t : ℕ) :
    coefficient stay hop a i (t + 1) 0 =
      bit (stay (a i)) * coefficient stay hop a i t 0 := by
  cases h : stay (a i) <;> simp [coefficient, enabled, edgeProduct, h]

theorem coefficient_succ_succ (i : ℤ) (t k : ℕ) :
    coefficient stay hop a i (t + 1) (k + 1) =
      bit (stay (a i)) * coefficient stay hop a i t (k + 1) +
        bit (hop (a i)) * coefficient stay hop a (i + 1) t k := by
  by_cases hk : k ≤ t
  · rcases lt_or_eq_of_le hk with hlt | rfl
    · have h₁ : k + 1 ≤ t := by omega
      have h₂ : t + 1 - (k + 1) = (t - (k + 1)) + 1 := by omega
      have h₃ : t - k = (t - (k + 1)) + 1 := by omega
      have h₄ : k + 1 ≤ t + 1 := by omega
      cases h : stay (a i)
      · simp [coefficient, enabled, edgeProduct, h, hk, h₁, h₂, h₃, mul_assoc]
      · simp only [coefficient, ite_eq_left hk, ite_eq_left h₁, ite_eq_left h₄, h₂, h₃,
          enabled, edgeProduct, h, Bool.toNat_true, bit_true, one_mul]
        rw [Nat.add_comm 1, Nat.multichoose_succ_succ, Nat.cast_add]
        ring
    · simp [coefficient, edgeProduct]
  · have h₁ : ¬ k + 1 ≤ t := by omega
    have h₂ : ¬ k + 1 ≤ t + 1 := by omega
    simp [coefficient, hk, h₁, h₂]

theorem iterate_control (t : ℕ) (x : Config Q) : ((step stay hop)^[t] x).1 = x.1 := by
  induction t with
  | zero => rfl
  | succ t ih => simpa [Function.iterate_succ_apply', step] using ih

/-- Exact response for an arbitrary, possibly infinite, initial configuration. -/
theorem iterate_data (t : ℕ) (x : Config Q) (i : ℤ) :
    ((step stay hop)^[t] x).2 i =
      ∑ k ∈ Finset.range (t + 1), coefficient stay hop x.1 i t k * x.2 (i + k) := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    change bit (stay (((step stay hop)^[t] x).1 i)) * ((step stay hop)^[t] x).2 i +
      bit (hop (((step stay hop)^[t] x).1 i)) * ((step stay hop)^[t] x).2 (i + 1) = _
    rw [iterate_control, ih i, ih (i + 1)]
    rw [Finset.sum_range_succ' (f := fun k : ℕ =>
      coefficient stay hop x.1 i (t + 1) k * x.2 (i + k)) (n := t + 1), coefficient_zero_succ]
    have hlast :
        (∑ k ∈ Finset.range (t + 1), coefficient stay hop x.1 i t (k + 1) * x.2 (i + (k + 1))) +
          coefficient stay hop x.1 i t 0 * x.2 i =
          ∑ k ∈ Finset.range (t + 1), coefficient stay hop x.1 i t k * x.2 (i + k) := by
      let f (k : ℕ) := coefficient stay hop x.1 i t k * x.2 (i + k)
      calc
        _ = ∑ k ∈ Finset.range (t + 1 + 1), f k := by
          simpa only [f, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] using
            (Finset.sum_range_succ' f (t + 1)).symm
        _ = _ := by
          rw [Finset.sum_range_succ]
          simp [f, coefficient_of_lt stay hop x.1 i (Nat.lt_succ_self t)]
    rw [← hlast]
    simp only [Finset.mul_sum, mul_add, add_mul, Finset.sum_add_distrib, coefficient_succ_succ,
      Nat.cast_zero, add_zero]
    have hshift : ∀ k : ℕ, i + 1 + ↑k = i + (↑k + 1) := by intro k; omega
    simp only [hshift, Nat.cast_add, Nat.cast_one, mul_assoc]
    ac_rfl

/-- Two separate inputs can switch the rule's self-dependence. -/
theorem nonaffine_local (q₀ q₁ : Q) (h₀ : stay q₀ = false) (h₁ : stay q₁ = true) :
    ¬ ∃ (g : Q → F₂) (c : F₂), ∀ q v : _, bit (stay q) * v = g q + c * v := by
  rintro ⟨g, c, h⟩
  have hg (q : Q) : g q = 0 := by simpa using (h q 0).symm
  have hc : c = 0 := by simpa [h₀, hg] using (h q₀ 1).symm
  have hz : (1 : F₂) = 0 := by simpa [h₁, hg, hc] using h q₁ 1
  have hbad : true = false := congrArg ofBoolRing hz
  cases hbad

end PredictionDepth.FrozenPascal
