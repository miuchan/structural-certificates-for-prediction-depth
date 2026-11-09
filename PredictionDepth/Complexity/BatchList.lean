import Mathlib.Data.List.Range

/-! Finite list identities used by the genuine streaming logspace compiler. -/
namespace PredictionDepth.StandardComplexity

/-- A fixed polynomial-length enumeration may emit the empty word after the
actual input-dependent count, without changing the streamed concatenation. -/
theorem range_flatMap_mask {α : Type*} (f : ℕ → List α) {r p : ℕ} (hr : r ≤ p) :
    (List.range p).flatMap (fun j => if j < r then f j else []) =
      (List.range r).flatMap f := by
  induction p generalizing r with
  | zero =>
    have : r = 0 := by omega
    subst r
    rfl
  | succ p ih =>
    by_cases hle : r ≤ p
    · rw [List.range_succ, List.flatMap_append, ih hle]
      simp [show ¬ p < r by omega]
    · have he : r = p + 1 := by omega
      subst r
      apply List.flatMap_congr
      intro j hj
      simp [List.mem_range.mp hj]

end PredictionDepth.StandardComplexity
