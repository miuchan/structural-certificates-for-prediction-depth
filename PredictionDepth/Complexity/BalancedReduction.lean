import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-! A fixed-width, layer-by-layer OR reduction with regular wire indices. -/

namespace PredictionDepth.RegularReduction

theorem size_eq_clog_succ (n : ℕ) : n.size = Nat.clog 2 (n + 1) := by
  apply Nat.le_antisymm
  · apply Nat.size_le.mpr
    have := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (n + 1)
    omega
  · apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
    have := Nat.lt_size_self n
    omega

theorem two_pow_size_le {n : ℕ} (hn : 0 < n) : 2 ^ n.size ≤ 2 * n := by
  have hs := Nat.size_pos.mpr hn
  have hp : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
  have he : n.size = (n.size - 1) + 1 := by omega
  rw [he, pow_succ]
  omega

def reduce : ℕ → (ℕ → Bool) → ℕ → Bool
  | 0, v, j => v j
  | d + 1, v, j => reduce d v (2 * j) || reduce d v (2 * j + 1)

/-- Node `j` after `d` reduction layers is the OR of its contiguous block of
`2^d` leaves. This form supports a serializer with simple arithmetic wires. -/
theorem reduce_true_iff (d : ℕ) (v : ℕ → Bool) (j : ℕ) :
    reduce d v j = true ↔ ∃ i < 2 ^ d, v (2 ^ d * j + i) = true := by
  induction d generalizing j with
  | zero =>
      simp only [reduce, pow_zero, one_mul]
      constructor
      · intro h
        exact ⟨0, by decide, by simpa using h⟩
      · rintro ⟨i, hi, h⟩
        have : i = 0 := by omega
        simpa [this] using h
  | succ d ih =>
      simp only [reduce, Bool.or_eq_true, ih]
      have hp : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; omega
      rw [hp]
      constructor
      · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
        · refine ⟨i, by have := Nat.two_pow_pos d; omega, ?_⟩
          convert h using 1; congr 1; ring
        · refine ⟨2 ^ d + i, by omega, ?_⟩
          convert h using 1; congr 1; ring
      · rintro ⟨i, hi, h⟩
        by_cases hleft : i < 2 ^ d
        · left
          refine ⟨i, hleft, ?_⟩
          convert h using 1; congr 1; ring
        · right
          refine ⟨i - 2 ^ d, by omega, ?_⟩
          have he : i = 2 ^ d + (i - 2 ^ d) := by omega
          rw [he] at h
          convert h using 1; congr 1; ring

theorem reduce_root_true_iff (d : ℕ) (v : ℕ → Bool) :
    reduce d v 0 = true ↔ ∃ i < 2 ^ d, v i = true := by
  simpa using reduce_true_iff d v 0

theorem reduce_eq_false_of_zero_tail {P d j : ℕ} {v : ℕ → Bool}
    (hv : ∀ i, P ≤ i → v i = false) (hj : P ≤ 2 ^ d * j) :
    reduce d v j = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨i, _, hi⟩ := (reduce_true_iff d v j).mp h
  rw [hv _ (by omega)] at hi
  cases hi

/-- All values outside a fixed padded width remain false, so a finite circuit
can omit their wires without affecting any reduction layer. -/
theorem reduce_zero_tail {P d : ℕ} {v : ℕ → Bool}
    (hv : ∀ i, P ≤ i → v i = false) :
    ∀ j, P ≤ j → reduce d v j = false := by
  intro j hj
  apply reduce_eq_false_of_zero_tail hv
  exact hj.trans (Nat.le_mul_of_pos_left j (Nat.two_pow_pos d))

def extend {P : ℕ} (v : Fin P → Bool) (j : ℕ) : Bool :=
  if h : j < P then v ⟨j, h⟩ else false

@[simp] theorem extend_in_range {P : ℕ} (v : Fin P → Bool) (j : Fin P) :
    extend v j.val = v j := dite_eq_left j.isLt

theorem extend_zero_tail {P : ℕ} (v : Fin P → Bool) :
    ∀ j, P ≤ j → extend v j = false := by
  intro j hj
  exact dite_eq_right (by omega)

/-- Every stage has the same width and the same arithmetic wire pattern.
The unused upper half consists of constant-false gates. -/
def mergeVector {P : ℕ} (v : Fin P → Bool) (j : Fin P) : Bool :=
  if h : 2 * j.val + 1 < P then v ⟨2 * j.val, by omega⟩ || v ⟨2 * j.val + 1, h⟩
  else false

theorem extend_mergeVector {P : ℕ} (hP : ∃ q, P = q + q) (v : Fin P → Bool) (j : ℕ) :
    extend (mergeVector v) j = (extend v (2 * j) || extend v (2 * j + 1)) := by
  obtain ⟨q, rfl⟩ := hP
  by_cases hj : j < q + q
  · simp only [extend, dite_eq_left hj]
    by_cases h : 2 * j + 1 < q + q
    · simp only [mergeVector, dite_eq_left h, dite_eq_left (show 2 * j < q + q by omega)]
    · have h₁ : ¬ 2 * j < q + q := by omega
      simp only [mergeVector, dite_eq_right h, dite_eq_right h₁, Bool.false_or]
  · have h₁ : ¬ 2 * j < q + q := by omega
    have h₂ : ¬ 2 * j + 1 < q + q := by omega
    simp only [extend, dite_eq_right hj, dite_eq_right h₁, dite_eq_right h₂, Bool.false_or]

def reduceVector {P : ℕ} : ℕ → (Fin P → Bool) → Fin P → Bool
  | 0, v => v
  | d + 1, v => mergeVector (reduceVector d v)

theorem extend_reduceVector {P : ℕ} (hP : ∃ q, P = q + q) (d : ℕ) (v : Fin P → Bool) :
    extend (reduceVector d v) = reduce d (extend v) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      funext j
      rw [reduceVector, extend_mergeVector hP, ih]
      rfl

theorem reduceVector_root_true_iff (s : ℕ) (v : Fin (2 ^ (s + 1)) → Bool) :
    reduceVector (s + 1) v ⟨0, Nat.two_pow_pos _⟩ = true ↔ ∃ i, v i = true := by
  have hP : ∃ q, 2 ^ (s + 1) = q + q := by
    refine ⟨2 ^ s, ?_⟩
    rw [pow_succ]
    omega
  have he := congrFun (extend_reduceVector hP (s + 1) v) 0
  simp only [extend, dite_eq_left (Nat.two_pow_pos (s + 1))] at he
  rw [he, reduce_root_true_iff]
  constructor
  · rintro ⟨j, hj, hv⟩
    exact ⟨⟨j, hj⟩, by simpa only [extend, dite_eq_left hj] using hv⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.isLt, by simpa only [extend_in_range] using hi⟩

theorem reduceVector_pow_root_true_iff {d : ℕ} (hd : 0 < d)
    (v : Fin (2 ^ d) → Bool) :
    reduceVector d v ⟨0, Nat.two_pow_pos _⟩ = true ↔ ∃ i, v i = true := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  exact reduceVector_root_true_iff s v

/-- Padding leaves has no semantic cost, and the larger width is a power of two. -/
def padTo {n P : ℕ} (v : Fin n → Bool) (j : Fin P) : Bool :=
  if h : j.val < n then v ⟨j.val, h⟩ else false

theorem exists_padTo_true_iff {n P : ℕ} (hn : n ≤ P) (v : Fin n → Bool) :
    (∃ j : Fin P, padTo v j = true) ↔ ∃ i : Fin n, v i = true := by
  constructor
  · rintro ⟨j, hj⟩
    unfold padTo at hj
    split_ifs at hj with h
    exact ⟨⟨j.val, h⟩, hj⟩
  · rintro ⟨i, hi⟩
    refine ⟨⟨i.val, i.isLt.trans_le hn⟩, ?_⟩
    simpa only [padTo, dite_eq_left i.isLt] using hi

theorem reduceVector_padded_root_true_iff {n d : ℕ} (hd : 0 < d) (hn : n ≤ 2 ^ d)
    (v : Fin n → Bool) :
    reduceVector d (padTo (P := 2 ^ d) v) ⟨0, Nat.two_pow_pos _⟩ = true ↔
      ∃ i : Fin n, v i = true :=
  (reduceVector_pow_root_true_iff hd _).trans (exists_padTo_true_iff hn v)

end PredictionDepth.RegularReduction
