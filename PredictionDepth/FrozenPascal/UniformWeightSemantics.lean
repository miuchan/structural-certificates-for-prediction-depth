import PredictionDepth.FrozenPascal.UniformWeightDefinitions

/-! Correctness of a regularly padded carry-save tree. -/

namespace PredictionDepth.FrozenPascal.UniformWeight

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Finset
open scoped BigOperators

variable {w P : ℕ}

private theorem pairVal_zero (w : ℕ) : pairVal (zero w) = 0 := by
  simp [zero, pairVal, BitString.fstBits, BitString.sndBits, BitString.val_equivFin_false]

private def value (v : Fin P → Pair w) (j : ℕ) : ℕ :=
  pairVal (extend v j) % 2 ^ w

private theorem value_merge (v : Fin P → Pair w) (j : ℕ) :
    value (mergeValues v) j = (value v (2 * j) + value v (2 * j + 1)) % 2 ^ w := by
  by_cases hj : j < P
  · rw [value, extend, dite_eq_left hj]
    change pairVal ((csa4to2 w).eval interpretation
        (Fin.append (extend v (2 * j)) (extend v (2 * j + 1)))) % 2 ^ w =
      (pairVal (extend v (2 * j)) % 2 ^ w + pairVal (extend v (2 * j + 1)) % 2 ^ w) % 2 ^ w
    rw [pairVal_eval_csa4to2_mod, ← Nat.add_mod]
  · have h₀ : ¬ 2 * j < P := by omega
    have h₁ : ¬ 2 * j + 1 < P := by omega
    simp [value, extend, hj, h₀, h₁, pairVal_zero]

private theorem value_reduce (d : ℕ) (v : Fin P → Pair w) (j : ℕ) :
    value (reduceValues d v) j =
      (∑ i ∈ range (2 ^ d), value v (2 ^ d * j + i)) % 2 ^ w := by
  induction d generalizing j with
  | zero => simp [reduceValues, value]
  | succ d ih =>
    rw [reduceValues, value_merge, ih (2 * j), ih (2 * j + 1), ← Nat.add_mod]
    rw [pow_succ, mul_two, sum_range_add]
    congr 1
    congr 1
    · apply sum_congr rfl
      intro i _
      congr 1
      ring
    · apply sum_congr rfl
      intro i _
      congr 1
      ring

/-- The root of a power-of-two tree holds the sum of the leaves modulo the word capacity. -/
theorem reduceValues_root_mod (d : ℕ) (v : Fin (2 ^ d) → Pair w) :
    pairVal (reduceValues d v 0) % 2 ^ w = (∑ j, pairVal (v j)) % 2 ^ w := by
  have h₀ : 0 < (2 : ℕ) ^ d := by positivity
  have h := value_reduce d v 0
  simp only [Nat.mul_zero, zero_add] at h
  rw [show pairVal (reduceValues d v 0) % 2 ^ w = value (reduceValues d v) 0 by
    simp [value, extend, h₀]]
  rw [h, Finset.sum_nat_mod Finset.univ (2 ^ w) (fun j => pairVal (v j))]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (value v)]
  apply Finset.sum_congr rfl
  intro j _
  simp [value, extend, j.isLt]

/-- Zero padding preserves the total Hamming weight represented by the tree. -/
theorem leaves_root_mod (d n w : ℕ) (hn : n ≤ 2 ^ d) (x : BitString n) :
    pairVal (reduceValues d (leaves n w (2 ^ d) x) 0) % 2 ^ w =
      BitString.weight x % 2 ^ w := by
  rw [reduceValues_root_mod, BitString.weight_eq_sum_toNat, Finset.sum_nat_mod,
    Finset.sum_nat_mod Finset.univ (2 ^ w) (fun i => (x i).toNat)]
  congr 1
  let term (j : ℕ) : ℕ := if h : j < n then (x ⟨j, h⟩).toNat % 2 ^ w else 0
  calc
    _ = ∑ j ∈ range (2 ^ d), term j := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val < n
      · simp [leaves, term, hj, pairVal_eval_bitPairCircuit_mod]
      · simp [leaves, term, hj, pairVal_zero]
    _ = ∑ j ∈ range n, term j := by
      symm
      apply sum_subset (range_mono hn)
      intro j _ hj
      simp [term, Finset.mem_range.not.mp hj]
    _ = _ := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      simp [term, j.isLt]

end PredictionDepth.FrozenPascal.UniformWeight
