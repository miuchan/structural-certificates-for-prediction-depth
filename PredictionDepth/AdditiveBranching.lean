import PredictionDepth.FrozenPascal.Semantics
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Interval.Finset.Nat

/-! Additively evolving binary controls with unconditional hops. One control
parity is shared by the nonterminal coefficients and gated by zero suffixes. -/

namespace PredictionDepth.AdditiveBranching

open Linear (F₂)
open scoped BigOperators

/-- The first track evolves by Pascal addition and gates the stay term on the second track. -/
def step (x : FrozenPascal.Config F₂) : FrozenPascal.Config F₂ :=
  (fun i => x.1 i + x.1 (i + 1), fun i => x.1 i * x.2 i + x.2 (i + 1))

def controlAt (a : ℤ → F₂) : ℕ → ℤ → F₂
  | 0, i => a i
  | t + 1, i => controlAt a t i + controlAt a t (i + 1)

theorem iterate_control (x : FrozenPascal.Config F₂) (t : ℕ) (i : ℤ) :
    (step^[t] x).1 i = controlAt x.1 t i := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih => simp [Function.iterate_succ_apply', step, controlAt, ih]

/-- The Pascal coefficient sum for the evolving control track. -/
theorem controlAt_eq_sum (a : ℤ → F₂) (t : ℕ) (i : ℤ) :
    controlAt a t i = ∑ k ∈ Finset.range (t + 1), (t.choose k : F₂) * a (i + k) := by
  let initial : FrozenPascal.Config Unit := (fun _ => (), a)
  let evolve := FrozenPascal.step (Q := Unit) (fun _ => true) (fun _ => true)
  have he (t : ℕ) (i : ℤ) : (evolve^[t] initial).2 i = controlAt a t i := by
    induction t generalizing i with
    | zero => rfl
    | succ t ih => simp [Function.iterate_succ_apply', evolve, FrozenPascal.step, controlAt, ih]
  rw [← he, show evolve = FrozenPascal.step (Q := Unit) (fun _ => true) (fun _ => true) from rfl,
    FrozenPascal.iterate_data]
  have hstay (j : ℤ) (k : ℕ) : FrozenPascal.enabled (fun _ => true) initial.1 j k = k + 1 := by
    induction k generalizing j with
    | zero => rfl
    | succ k ih => simp [FrozenPascal.enabled, ih, Nat.add_comm 1]
  have hhop (j : ℤ) (k : ℕ) : FrozenPascal.edgeProduct (fun _ => true) initial.1 j k = 1 := by
    induction k generalizing j with
    | zero => rfl
    | succ k ih => simp [FrozenPascal.edgeProduct, ih]
  apply Finset.sum_congr rfl
  intro k hk
  have hkt : k ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp [initial, FrozenPascal.coefficient, hkt, hstay, hhop, Nat.multichoose_eq,
    show k + 1 + (t - k) - 1 = t by omega, Nat.choose_symm hkt]

/-- Control parity with the rightmost term removed. -/
def trimmedParity (a : ℤ → F₂) (i : ℤ) (t : ℕ) : F₂ :=
  controlAt a t i + a (i + t)

theorem trimmedParity_eq_sum (a : ℤ → F₂) (i : ℤ) (t : ℕ) :
    trimmedParity a i t = ∑ k ∈ Finset.range t, (t.choose k : F₂) * a (i + k) := by
  rw [trimmedParity, controlAt_eq_sum, Finset.sum_range_succ]
  simp [add_assoc, BooleanRing.add_self]

/-- One exactly when all the initial controls strictly between `k` and `t` are zero. -/
def zeroSuffix (a : ℤ → F₂) (i : ℤ) (t k : ℕ) : F₂ :=
  ∏ j ∈ Finset.Ioo k t, (1 + a (i + j))

/-- The all-hop coefficient is one. Earlier coefficients share `trimmedParity`. -/
def coefficient (a : ℤ → F₂) (i : ℤ) (t k : ℕ) : F₂ :=
  if k < t then zeroSuffix a i t k * trimmedParity a i t else if k = t then 1 else 0

private theorem coefficient_lt (h : k < t) :
    coefficient a i t k = zeroSuffix a i t k * trimmedParity a i t := by simp [coefficient, h]

@[simp] theorem coefficient_diag : coefficient a i t t = 1 := by simp [coefficient]

private theorem coefficient_outside (h : t < k) : coefficient a i t k = 0 := by
  simp [coefficient, Nat.not_lt_of_ge h.le, h.ne']

private theorem zeroSuffix_extend (a : ℤ → F₂) (i : ℤ) (h : k < t) :
    zeroSuffix a i (t + 1) k = (1 + a (i + t)) * zeroSuffix a i t k := by
  have hs : Finset.Ioo k (t + 1) = insert t (Finset.Ioo k t) := by
    ext j
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  simp [zeroSuffix, hs]

private theorem zeroSuffix_shift (a : ℤ → F₂) (i : ℤ) (t k : ℕ) :
    zeroSuffix a (i + 1) t k = zeroSuffix a i (t + 1) (k + 1) := by
  let e : ℕ ↪ ℕ := ⟨Nat.succ, fun _ _ => Nat.succ.inj⟩
  have hs : Finset.Ioo (k + 1) (t + 1) = (Finset.Ioo k t).map e := by
    ext j
    cases j with
    | zero => simp [e]
    | succ j =>
      simp only [Finset.mem_Ioo, Finset.mem_map, Nat.succ_lt_succ_iff]
      refine ⟨fun hj => ⟨j, hj, rfl⟩, ?_⟩
      rintro ⟨l, hl, he⟩
      have heq : l = j := Nat.succ.inj he
      rwa [heq] at hl
  rw [zeroSuffix, zeroSuffix, hs, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro j _
  have hj : i + 1 + (j : ℤ) = i + (e j : ℤ) := by
    change i + 1 + (j : ℤ) = i + (j.succ : ℤ)
    omega
  rw [hj]

private theorem trimmedParity_succ (a : ℤ → F₂) (i : ℤ) (t : ℕ) :
    trimmedParity a i (t + 1) = controlAt a t i + trimmedParity a (i + 1) t := by
  have hi : i + ((t + 1 : ℕ) : ℤ) = i + 1 + t := by omega
  rw [trimmedParity, hi, controlAt, add_assoc, ← trimmedParity]

private theorem zeroSuffix_mul_shifted_parity (a : ℤ → F₂) (i : ℤ) (t : ℕ) :
    zeroSuffix a i (t + 1) 0 * trimmedParity a (i + 1) t = 0 := by
  by_cases h : ∀ k : ℕ, k < t → a (i + 1 + k) = 0
  · have hz : trimmedParity a (i + 1) t = 0 := by
      rw [trimmedParity_eq_sum]
      exact Finset.sum_eq_zero (fun k hk => by rw [h k (Finset.mem_range.mp hk), mul_zero])
    rw [hz, mul_zero]
  · push Not at h
    obtain ⟨k, hk, ha⟩ := h
    have hs : i + ((k + 1 : ℕ) : ℤ) = i + 1 + k := by omega
    have hbit : a (i + 1 + k) = 1 := by
      obtain ⟨b, hb⟩ := (@toBoolRing Bool).surjective (a (i + 1 + k))
      cases b
      · exact (ha hb.symm).elim
      · exact hb.symm
    have hp : zeroSuffix a i (t + 1) 0 = 0 :=
      Finset.prod_eq_zero (i := k + 1) (by simp; omega)
        (by rw [hs, hbit, BooleanRing.add_self])
    simp [hp]

private theorem stay_term (a : ℤ → F₂) (i : ℤ) (h : k ≤ t) :
    controlAt a t i * coefficient a i t k = zeroSuffix a i (t + 1) k * controlAt a t i := by
  rcases lt_or_eq_of_le h with h | rfl
  · rw [coefficient_lt h, zeroSuffix_extend a i h, trimmedParity]
    rw [mul_left_comm, mul_add, BooleanRing.mul_self]
    ring
  · have hs : Finset.Ioo k (k + 1) = ∅ := by ext j; simp; omega
    simp [zeroSuffix, hs]

theorem coefficient_zero_succ (a : ℤ → F₂) (i : ℤ) (t : ℕ) :
    coefficient a i (t + 1) 0 = controlAt a t i * coefficient a i t 0 := by
  rw [coefficient_lt (Nat.zero_lt_succ t), trimmedParity_succ, mul_add,
    zeroSuffix_mul_shifted_parity, add_zero, stay_term a i (Nat.zero_le t)]

theorem coefficient_succ_succ (a : ℤ → F₂) (i : ℤ) (t k : ℕ) :
    coefficient a i (t + 1) (k + 1) =
      controlAt a t i * coefficient a i t (k + 1) + coefficient a (i + 1) t k := by
  rcases lt_trichotomy k t with h | rfl | h
  · rw [coefficient_lt (Nat.succ_lt_succ h), stay_term a i (Nat.succ_le_of_lt h),
      coefficient_lt h, zeroSuffix_shift, trimmedParity_succ, mul_add]
  · rw [coefficient_diag, coefficient_outside (Nat.lt_succ_self k), coefficient_diag]
    simp
  · rw [coefficient_outside (Nat.succ_lt_succ h), coefficient_outside (by omega : t < k + 1),
      coefficient_outside h, mul_zero, add_zero]

/-- The coefficient formula evaluates the actual coupled dynamics on the infinite lattice. -/
theorem iterate_data (x : FrozenPascal.Config F₂) (t : ℕ) (i : ℤ) :
    (step^[t] x).2 i =
      ∑ k ∈ Finset.range (t + 1), coefficient x.1 i t k * x.2 (i + k) := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    change (step^[t] x).1 i * (step^[t] x).2 i + (step^[t] x).2 (i + 1) = _
    rw [iterate_control, ih i, ih (i + 1), Finset.sum_range_succ' (f := fun k : ℕ =>
      coefficient x.1 i (t + 1) k * x.2 (i + k)) (n := t + 1), coefficient_zero_succ]
    let f (k : ℕ) := coefficient x.1 i t k * x.2 (i + k)
    have hlast : (∑ k ∈ Finset.range (t + 1), f (k + 1)) + f 0 =
        ∑ k ∈ Finset.range (t + 1), f k := by
      rw [← Finset.sum_range_succ', Finset.sum_range_succ]
      simp [f, coefficient_outside (Nat.lt_succ_self t)]
    change controlAt x.1 t i * (∑ k ∈ Finset.range (t + 1), f k) + _ = _
    rw [← hlast]
    have hshift (k : ℕ) : i + 1 + (k : ℤ) = i + ((k + 1 : ℕ) : ℤ) := by omega
    simp only [f, Finset.mul_sum, mul_add, add_mul, Finset.sum_add_distrib,
      coefficient_succ_succ, hshift, Nat.cast_zero, add_zero, mul_assoc]
    exact add_right_comm _ _ _

end PredictionDepth.AdditiveBranching
