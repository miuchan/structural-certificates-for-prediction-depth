import PredictionDepth.Complexity.CodeLogspace
import PredictionDepth.Complexity.BalancedReduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower

/-!
# Native widths for the carry-save weight circuit

The word width stores every count from zero through `n`. The number of padded
leaves is a power of two but is still linear in `n`; its unary generation is
proved using an actual logspace transducer, not an arithmetic oracle.
-/

namespace PredictionDepth.FrozenPascal.UniformWeight
open Cslib
open Turing.MultiTapeTM
open StandardComplexity

def wordWidth (n : ℕ) : ℕ := Nat.clog 2 (n + 1)
def paddedCount (n : ℕ) : ℕ := 2 ^ wordWidth n

@[simp] theorem wordWidth_zero : wordWidth 0 = 0 := rfl
@[simp] theorem paddedCount_zero : paddedCount 0 = 1 := rfl

theorem wordWidth_eq_size (n : ℕ) : wordWidth n = n.size :=
  (RegularReduction.size_eq_clog_succ n).symm

/-- The width is sufficient for the full (unreduced) natural count. -/
theorem lt_pow_wordWidth (n : ℕ) : n < 2 ^ wordWidth n := by
  have h := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (n + 1)
  change n < 2 ^ Nat.clog 2 (n + 1)
  omega

theorem lt_paddedCount (n : ℕ) : n < paddedCount n := lt_pow_wordWidth n

theorem le_paddedCount (n : ℕ) : n ≤ paddedCount n := (lt_paddedCount n).le

theorem paddedCount_pos (n : ℕ) : 0 < paddedCount n := Nat.two_pow_pos _

theorem wordWidth_pos_iff (n : ℕ) : 0 < wordWidth n ↔ 0 < n := by
  rw [wordWidth_eq_size, Nat.size_pos]

theorem wordWidth_le (n : ℕ) : wordWidth n ≤ n := by
  rw [wordWidth_eq_size]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem paddedCount_le_two_mul {n : ℕ} (hn : 0 < n) : paddedCount n ≤ 2 * n := by
  rw [paddedCount, wordWidth_eq_size]
  exact RegularReduction.two_pow_size_le hn

/-- Padding is linear even at the empty-input boundary. -/
theorem paddedCount_le (n : ℕ) : paddedCount n ≤ 2 * (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · exact (paddedCount_le_two_mul hn).trans (by omega)

/-- Printing the width in unary uses the native unary-to-binary conversion,
followed by a streaming digit count. -/
theorem wordWidth_logspace :
    ComputableInLogSpace wordWidth encUnary encUnary := by
  have hb : ComputableInLogSpace Nat.bits encUnary encBits :=
    (ComputableInLogSpace.id (encIn := encUnary)).unaryToBinary.congr (fun _ => rfl)
  have h := CodeLogspace.bitsLength.comp hb
  exact h.congr_fun (fun n => by
    simp only [wordWidth_eq_size, Function.comp_apply, Nat.size_eq_bits_len])

/-- The binary padded count is `w` zeros followed by one. -/
theorem paddedCount_binary_logspace :
    ComputableInLogSpace paddedCount encUnary encNat := by
  have hu : ComputableInLogSpace (fun n => List.replicate (wordWidth n) true)
      encUnary encBits := wordWidth_logspace.congr (fun _ => rfl)
  have hz := (ComputableInLogSpace.bitsMap (fun _ => false)).comp hu
  have hbits := hz.bitsAppend (ComputableInLogSpace.const [true])
  exact hbits.congr (fun n => by
    simp only [paddedCount, encNat_two_pow, encBits_apply, Function.comp_apply, List.map_replicate])

/-- Printing `P(n)` in unary is logarithmic-space: the binary value is bounded
by the explicit unary clock `2*(n+1)`. This charges the complete output. -/
theorem paddedCount_logspace :
    ComputableInLogSpace paddedCount encUnary encUnary := by
  have hB : ComputableInLogSpace (fun n : ℕ => 2 * (n + 1)) encUnary encUnary :=
    (ComputableInLogSpace.const 2).unaryMul
      (ComputableInLogSpace.id.unaryAdd (ComputableInLogSpace.const 1))
  exact CodeLogspace.boundedBinaryToUnary paddedCount_binary_logspace hB paddedCount_le

theorem wordWidth_polynomial : PolynomiallyBounded wordWidth :=
  (show PolynomiallyBounded (fun n : ℕ => n) by fun_prop).mono_of_le wordWidth_le

theorem paddedCount_polynomial : PolynomiallyBounded paddedCount :=
  (show PolynomiallyBounded (fun n : ℕ => 2 * (n + 1)) by fun_prop).mono_of_le paddedCount_le

end PredictionDepth.FrozenPascal.UniformWeight
