import PredictionDepth.Linear
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Full description bounds for binary linear prediction

These bounds count wiring tables and circuit syntax in addition to Boolean
gates. The finite matrix representation has width `n*n`; uniform generation
of the initial matrix family remains a separate hypothesis.
-/

namespace PredictionDepth.Linear
open FastComposition

namespace Circuits

theorem collect_descriptionSize_le {n m G : ℕ} (cs : Fin m → BinaryCircuit n 1)
    (h : ∀ i, (cs i).descriptionSize ≤ G) :
    (collect cs).descriptionSize ≤ m * (G + 1) + 1 := by
  induction m with
  | zero => simp [collect, BinaryCircuit.descriptionSize]
  | succ m ih =>
      simp only [collect, BinaryCircuit.descriptionSize, Nat.succ_mul]
      have h₁ := ih (fun i => cs i.castSucc) (fun i => h i.castSucc)
      have h₂ := h (Fin.last m)
      omega

theorem sumTree_descriptionSize_le {n k G : ℕ} (cs : Fin k → BinaryCircuit n 1)
    (h : ∀ i, (cs i).descriptionSize ≤ G) (hG : 2 ≤ G)
    (d : ℕ) (xs : List (Fin k)) :
    (sumTree cs d xs).descriptionSize + 3 ≤ (G + 3) * 2 ^ d := by
  induction d generalizing xs with
  | zero =>
      cases xs with
      | nil => simpa [sumTree, BinaryCircuit.constant, BinaryCircuit.descriptionSize] using hG
      | cons i xs => simpa [sumTree] using h i
  | succ d ih =>
      simp only [sumTree, BinaryCircuit.descriptionSize]
      have h₁ := ih (xs.take (2 ^ d))
      have h₂ := ih (xs.drop (2 ^ d))
      rw [pow_succ, ← Nat.mul_assoc]
      omega

@[simp] theorem productTerm_descriptionSize {m : ℕ} (a b : Fin m) :
    (productTerm a b).descriptionSize = 5 := rfl

theorem pow_clog_two_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * n + 1 := by
  by_cases hn : n ≤ 1
  · simp only [Nat.clog_of_right_le_one hn, pow_zero]
    omega
  · have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) (by omega : 1 < n)
    have hc := Nat.clog_pos (by decide : 1 < (2 : ℕ)) (by omega : 1 < n)
    simp only [Nat.pred_eq_sub_one] at hp
    have he : Nat.clog 2 n = (Nat.clog 2 n - 1) + 1 := by omega
    rw [he, pow_succ]
    omega

theorem dot_descriptionSize_le {m n : ℕ} (a b : Fin n → Fin m) :
    (dot a b).descriptionSize ≤ 16 * n + 8 := by
  have h := sumTree_descriptionSize_le (fun k => productTerm (a k) (b k))
    (G := 5) (fun _ => by simp) (by decide) (Nat.clog 2 n) (List.finRange n)
  change (dot a b).descriptionSize + 3 ≤ 8 * 2 ^ Nat.clog 2 n at h
  have hp := pow_clog_two_le n
  omega

end Circuits

theorem compositionCircuit_descriptionSize_le (n : ℕ) :
    (compositionCircuit n).descriptionSize ≤ (n * n) * (16 * n + 9) + 1 := by
  exact Circuits.collect_descriptionSize_le _ (fun _ => Circuits.dot_descriptionSize_le _ _)

theorem observationCircuit_descriptionSize_le {n : ℕ} (i : Fin n) :
    (observationCircuit i).descriptionSize ≤ 16 * n + 8 :=
  Circuits.dot_descriptionSize_le _ _

theorem initializationCircuit_descriptionSize {n : ℕ} (A : BinaryMatrix n) :
    (initializationCircuit A).descriptionSize = 2 * (n * n) + n + 5 := by
  simp only [initializationCircuit, BinaryCircuit.constant, BinaryCircuit.select,
    BinaryCircuit.descriptionSize]
  omega

/-- The matrix predictor has polynomial description overhead per binary time bit. -/
theorem predictor_descriptionSize_le {n : ℕ} (A : BinaryMatrix n) (i : Fin n) (T : ℕ) :
    (predictor A i T).descriptionSize ≤
      (2 * (n * n) + n + 5) +
      2 * Nat.clog 2 (T + 1) * ((n * n) * (16 * n + 9) + 3 * (n * n) + n + 8) +
      (16 * n + 8) + n * n + n + 3 := by
  have h := (implementation A i).predictor_descriptionSize_le T
  change (predictor A i T).descriptionSize ≤ (initializationCircuit A).descriptionSize +
    2 * Nat.clog 2 (T + 1) * ((compositionCircuit n).descriptionSize + 3 * (n * n) + n + 7) +
    (observationCircuit i).descriptionSize + n * n + n + 3 at h
  rw [initializationCircuit_descriptionSize] at h
  have hm := compositionCircuit_descriptionSize_le n
  have ho := observationCircuit_descriptionSize_le i
  have hm' : (compositionCircuit n).descriptionSize + 3 * (n * n) + n + 7 ≤
      (n * n) * (16 * n + 9) + 3 * (n * n) + n + 8 := by omega
  have hmul := Nat.mul_le_mul_left (2 * Nat.clog 2 (T + 1)) hm'
  omega

/-- A finite form of the `O(log² T)` consequence: any dimension bounded by a
fixed power of `T+1` has a logarithm-squared prediction bound. -/
theorem predictor_depth_polynomial_dimension {n : ℕ} (A : BinaryMatrix n)
    (i : Fin n) (T k : ℕ) (hn : n ≤ (T + 1) ^ k) :
    (predictor A i T).depth ≤ 3 * (k + 1) * (Nat.clog 2 (T + 1) + 1) ^ 2 := by
  let l := Nat.clog 2 (T + 1)
  have hp : n ≤ 2 ^ (l * k) := by
    calc
      n ≤ (T + 1) ^ k := hn
      _ ≤ (2 ^ l) ^ k := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) (T + 1)) k
      _ = 2 ^ (l * k) := (pow_mul 2 l k).symm
  have hlog : Nat.clog 2 n ≤ l * k := (Nat.clog_le_iff_le_pow (by decide)).mpr hp
  calc
    (predictor A i T).depth ≤ 2 * l * (Nat.clog 2 n + 1) + (Nat.clog 2 n + 1) :=
      predictor_depth_le A i T
    _ = (2 * l + 1) * (Nat.clog 2 n + 1) := by ring
    _ ≤ (2 * l + 1) * (l * k + 1) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1)
    _ ≤ (3 * (l + 1)) * ((k + 1) * (l + 1)) :=
      Nat.mul_le_mul (by omega) (by nlinarith)
    _ = 3 * (k + 1) * (Nat.clog 2 (T + 1) + 1) ^ 2 := by dsimp [l]; ring

theorem predictor_depth_diagonal_le {n : ℕ} (A : BinaryMatrix n) (i : Fin n) :
    (predictor A i n).depth ≤ 6 * (Nat.clog 2 (n + 1) + 1) ^ 2 := by
  simpa using predictor_depth_polynomial_dimension A i n 1 (by simp)

end PredictionDepth.Linear
