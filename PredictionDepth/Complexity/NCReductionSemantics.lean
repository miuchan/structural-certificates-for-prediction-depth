import PredictionDepth.Complexity.NCReductionConstruction

/-! Correctness of the variable-output-length selection circuit. -/

namespace PredictionDepth.StandardComplexity.ReductionConstruction
open Cslib Cslib.Circuits Cslib.Circuits.Boolean

variable {f : List Bool → List Bool} {target bits lengthTest : BooleanCircuitFamily}
  {B : Set (List Bool)} {bound : ℕ → ℕ}
  (hbits : ∀ n j (x : Fin n → Bool),
    (prefixed bits n j).eval interpretation x 0 = (f (List.ofFn x)).getD j false)
  (hlen : ∀ n m (x : Fin n → Bool),
    (prefixed lengthTest n m).eval interpretation x 0 = decide ((f (List.ofFn x)).length = m))
  (htarget : FamilyDecides target B)
  (hbound : ∀ x, (f x).length ≤ bound x.length)

include hbits in
theorem bitBank_eval (n m : ℕ) (x : Fin n → Bool) :
    (bitBank bits n m).eval interpretation x =
      fun j => (f (List.ofFn x)).getD j.val false := by
  funext j
  exact (congrFun (Circuit.eval_pi _ x) j).trans (hbits n j.val x)

include hbits hlen in
theorem branch_eval (n m : ℕ) (x : Fin n → Bool) :
    (branch target bits lengthTest n m).eval interpretation x 0 =
      ((target m).eval interpretation (fun j => (f (List.ofFn x)).getD j.val false) 0 &&
        decide ((f (List.ofFn x)).length = m)) := by
  simp only [branch, Circuit.eval_comp, Circuit.eval_oneGate, Circuit.eval_append]
  change ((target m).eval interpretation ((bitBank bits n m).eval interpretation x) 0 &&
    (prefixed lengthTest n m).eval interpretation x 0) = _
  rw [bitBank_eval hbits, hlen]

include hbits hlen htarget in
theorem branch_true_iff (n m : ℕ) (x : Fin n → Bool) :
    (branch target bits lengthTest n m).eval interpretation x 0 = true ↔
      (f (List.ofFn x)).length = m ∧ f (List.ofFn x) ∈ B := by
  rw [branch_eval hbits hlen, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hm⟩
    refine ⟨hm, ?_⟩
    apply (htarget (f (List.ofFn x))).mpr
    subst m
    exact h
  · rintro ⟨hm, h⟩
    refine ⟨?_, hm⟩
    subst m
    exact (htarget (f (List.ofFn x))).mp h

include hbits hlen htarget hbound in
/-- The true length is among the branches, and every other branch is rejected.
No assumption that output length depends only on input length is used. -/
theorem family_eval_true_iff (n : ℕ) (x : Fin n → Bool) :
    (family target bits lengthTest bound n).eval interpretation x 0 = true ↔
      f (List.ofFn x) ∈ B := by
  rw [family, Circuit.eval_comp, UniformOR.family_true_iff]
  simp only [Circuit.eval_pi, branch_true_iff hbits hlen htarget]
  constructor
  · rintro ⟨j, _, h⟩
    exact h
  · intro h
    have hb := hbound (List.ofFn x)
    simp only [List.length_ofFn] at hb
    exact ⟨⟨(f (List.ofFn x)).length, by omega⟩, rfl, h⟩

include hbits hlen htarget hbound in
theorem family_decides_preimage :
    FamilyDecides (family target bits lengthTest bound) (f ⁻¹' B) := by
  intro x
  have hw : List.ofFn (BitString.ofList x.length x) = x := BitString.ofFn_ofList rfl
  change f x ∈ B ↔
    (family target bits lengthTest bound x.length).eval interpretation
      (BitString.ofList x.length x) 0 = true
  rw [family_eval_true_iff hbits hlen htarget hbound, hw]

end PredictionDepth.StandardComplexity.ReductionConstruction
