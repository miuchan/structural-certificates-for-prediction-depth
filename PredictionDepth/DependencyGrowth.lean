import PredictionDepth.Circuit

/-! The numerical limit of a lower-bound method based only on input counts. -/
namespace PredictionDepth

theorem essentialInputs_card_le_inputLength {n : ℕ} (f : BooleanInput n → Bool) :
    (essentialInputs f).card ≤ n := by
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin n)

theorem clog_power_bound {b n : ℕ} (hb : 1 < b) (dimension : ℕ) :
    Nat.clog b (n ^ dimension) ≤ dimension * Nat.clog b n := by
  apply (Nat.clog_le_iff_le_pow hb).mpr
  calc
    n ^ dimension ≤ (b ^ Nat.clog b n) ^ dimension :=
      Nat.pow_le_pow_left (Nat.le_pow_clog hb n) dimension
    _ = b ^ (dimension * Nat.clog b n) := by rw [← pow_mul, Nat.mul_comm]

/-- This bounds the *dependency-count lower bound*, not actual circuit depth.
For a polynomial-volume light cone it grows at most logarithmically in side length. -/
theorem dependency_method_limit {b n : ℕ} (hb : 1 < b)
    (f : BooleanInput n → Bool) (radius time dimension : ℕ)
    (hvolume : n ≤ (2 * radius * time + 1) ^ dimension) :
    Nat.clog b (essentialInputs f).card ≤
      dimension * Nat.clog b (2 * radius * time + 1) := by
  exact (Nat.clog_mono_right b ((essentialInputs_card_le_inputLength f).trans hvolume)).trans
    (clog_power_bound hb dimension)

end PredictionDepth
