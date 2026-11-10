import PredictionDepth.FrozenPascal.CoefficientUniform
import PredictionDepth.FrozenPascal.UniformWeightWidths

/-! Logspace arithmetic for the two candidate encodings. -/

namespace PredictionDepth.SparseCorrections

open Cslib Turing.MultiTapeTM StandardComplexity

variable {α : Type} {enc : α ↪ List Bool}

theorem fixedPower_logspace {f : α → ℕ} (hf : ComputableInLogSpace f enc encUnary) (k : ℕ) :
    ComputableInLogSpace (fun a => f a ^ k) enc encUnary := by
  induction k with
  | zero => exact (ComputableInLogSpace.const 1).congr_fun fun _ => by simp
  | succ k ih => simpa only [pow_succ] using ih.unaryMul hf

/-- For a fixed tuple length, base-`(M+1)` decoding uses counters of
polynomial magnitude. A digit of zero is padding. -/
theorem digitBit_logspace {M j i : α → ℕ}
    (hM : ComputableInLogSpace M enc encUnary) (hj : ComputableInLogSpace j enc encUnary)
    (hi : ComputableInLogSpace i enc encUnary) (k : ℕ) :
    ComputableInLogSpace
      (fun a => (List.range k).any (fun p => j a / (M a + 1) ^ p % (M a + 1) == i a + 1))
      enc encBool := by
  have hbase := hM.unaryAdd (ComputableInLogSpace.const 1)
  have hit := hi.unaryAdd (ComputableInLogSpace.const 1)
  induction k with
  | zero => exact ComputableInLogSpace.const false
  | succ k ih =>
    have h := ((hj.unaryDiv (fixedPower_logspace hbase k)).unaryMod hbase).unaryEq hit
    exact (ih.bool_or h).congr_fun fun a => by
      simp only [List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      rfl

/-- The scheduled count is streamed in unary against a proved polynomial
clock. The binary representation uses `K` zero digits and a final one. -/
theorem scheduledCount_logspace {K B : α → ℕ}
    (hK : ComputableInLogSpace K enc encUnary) (hB : ComputableInLogSpace B enc encUnary)
    (hbound : ∀ a, 2 ^ K a ≤ B a) :
    ComputableInLogSpace (fun a => 2 ^ K a) enc encUnary := by
  have hu : ComputableInLogSpace (fun a => List.replicate (K a) true) enc encBits :=
    hK.congr (fun _ => rfl)
  have hz := (ComputableInLogSpace.bitsMap (fun _ => false)).comp hu
  have hbits := hz.bitsAppend (ComputableInLogSpace.const [true])
  have hbinary : ComputableInLogSpace (fun a => 2 ^ K a) enc encNat := by
    exact hbits.congr (fun _ => by
      simp only [encNat_two_pow, encBits_apply, Function.comp_apply, List.map_replicate])
  exact CodeLogspace.boundedBinaryToUnary hbinary hB hbound

/-- Multiple slots can name an address; with distinct slots this is simply
the assignment bit at the listed address, or zero off the schedule. -/
theorem scheduledBit_logspace {K j i : α → ℕ} {slot : α × ℕ → ℕ}
    (hK : ComputableInLogSpace K enc encUnary) (hj : ComputableInLogSpace j enc encUnary)
    (hi : ComputableInLogSpace i enc encUnary)
    (hs : ComputableInLogSpace slot (encPair enc encUnary) encUnary) :
    ComputableInLogSpace
      (fun a => (List.range (K a)).any (fun p => (slot (a, p) == i a) && (j a).testBit p))
      enc encBool := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hq := ComputableInLogSpace.snd enc encUnary
  have h := (hs.unaryEq (hi.comp hp)).bool_and (FrozenPascal.testBit_logspace (hj.comp hp) hq)
  have hword : ComputableInLogSpace
      (fun p : α × ℕ => [(slot p == i p.1) && (j p.1).testBit p.2])
      (encPair enc encUnary) encBits := h.congr (fun p => by simp; rfl)
  have hlist := LogspaceBatch.flatMap_range hK hword
  exact ((ComputableInLogSpace.bitsAny id).comp hlist).congr_fun fun a => by
    simp only [← List.map_eq_flatMap, List.any_map, Function.comp_apply]
    rfl

end PredictionDepth.SparseCorrections
