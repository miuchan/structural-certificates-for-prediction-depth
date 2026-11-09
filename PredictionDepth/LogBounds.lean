import PredictionDepth.DependencyGrowth
import Mathlib.Tactic.Linarith

/-! Explicit finite logarithm inequalities for polynomially sized encodings. -/
namespace PredictionDepth

theorem clog_mul_bound {b : ℕ} (hb : 1 < b) (a c : ℕ) :
    Nat.clog b (a * c) ≤ Nat.clog b a + Nat.clog b c := by
  apply (Nat.clog_le_iff_le_pow hb).mpr
  calc
    a * c ≤ (b ^ Nat.clog b a) * (b ^ Nat.clog b c) :=
      Nat.mul_le_mul (Nat.le_pow_clog hb a) (Nat.le_pow_clog hb c)
    _ = b ^ (Nat.clog b a + Nat.clog b c) := (pow_add _ _ _).symm

theorem clog_succ_le_log_add_one (n : ℕ) :
    Nat.clog 2 (n + 1) ≤ Nat.log 2 n + 1 := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
  omega

theorem clog_of_polynomial_bound {m n C k : ℕ} (h : m ≤ C * (n + 1) ^ k) :
    Nat.clog 2 m ≤ (Nat.clog 2 C + k) * (Nat.log 2 n + 1) := by
  have hm := Nat.clog_mono_right 2 h
  have hc := clog_mul_bound (by decide : 1 < 2) C ((n + 1) ^ k)
  have hp := clog_power_bound (b := 2) (n := n + 1) (by decide) k
  have hl := Nat.mul_le_mul_left k (clog_succ_le_log_add_one n)
  nlinarith

/-- The binary length of a polynomially bounded counter is logarithmic. -/
theorem bitLength_of_polynomial_bound {m n C k : ℕ} (h : m ≤ C * (n + 1) ^ k) :
    Nat.clog 2 (m + 1) ≤ (Nat.clog 2 (C + 1) + k) * (Nat.log 2 n + 1) := by
  apply clog_of_polynomial_bound
  have hp : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  nlinarith

end PredictionDepth
