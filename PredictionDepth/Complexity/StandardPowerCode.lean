import PredictionDepth.Complexity.StandardPowerLayout
import PredictionDepth.Complexity.AdjacencyCode
import PredictionDepth.Complexity.LayerCode

/-! Closed gate-index arithmetic for the genuine De Morgan matrix-power circuits. -/
namespace PredictionDepth.StandardComplexity.StandardPower
open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-- The unshifted product block is already a flat parallel one-gate family. -/
def unshiftedProductCode (N P q : ℕ) : Op × List ℕ :=
  let entry := q / P
  let k := q % P
  if k < N then (.and, [(entry / N) * N + k, k * N + entry % N])
  else (.const false, [])

def unshiftedMergeCode (_N P q : ℕ) : Op × List ℕ :=
  let entry := q / P
  let k := q % P
  if 2 * k + 1 < P then (.or, [entry * P + 2 * k, entry * P + 2 * k + 1])
  else (.const false, [])

theorem productEntry_code {N P : ℕ} (e : Fin (N * N)) (k : Fin P) :
    (productEntry e k).code =
      ([if k.val < N then
        (.and, [(e.val / N) * N + k.val, k.val * N + e.val % N])
        else (.const false, [])], [N * N]) := by
  unfold productEntry
  split_ifs
  · change ([(Op.and, [_, _])], [N * N]) = _
    simp [ParallelReachability.index, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  · rfl

theorem products_code (N P : ℕ) :
    (products N P).code =
      ((List.range ((N * N) * P)).map (unshiftedProductCode N P),
        (List.range ((N * N) * P)).map (fun q => N * N + q)) := by
  rw [products, Adjacency.pi_inputGate_code
    _ (fun q => unshiftedProductCode N P q.val)]
  · simp only [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
      List.map_map, Function.comp_def]
  · intro q
    simpa only [unshiftedProductCode, finProdFinEquiv_symm_apply, Fin.divNat, Fin.modNat] using
      productEntry_code (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
  · intro q j hj
    have he : q.val / P < N * N := (finProdFinEquiv.symm q).1.isLt
    dsimp only [unshiftedProductCode] at hj
    split_ifs at hj with hk
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      have hN : 0 < N := by omega
      have hrow : q.val / P / N < N := (Nat.div_lt_iff_lt_mul hN).mpr he
      have hcol : q.val / P % N < N := Nat.mod_lt _ hN
      rcases hj with rfl | rfl <;> nlinarith
    · simp at hj

theorem mergeEntry_code {N P : ℕ} (e : Fin (N * N)) (k : Fin P) :
    (mergeEntry e k).code =
      ([if 2 * k.val + 1 < P then
        (.or, [e.val * P + 2 * k.val, e.val * P + 2 * k.val + 1])
        else (.const false, [])], [(N * N) * P]) := by
  unfold mergeEntry
  split_ifs
  · change ([(Op.or, [_, _])], [(N * N) * P]) = _
    simp [slot, finProdFinEquiv, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
  · rfl

theorem merge_code (N P : ℕ) :
    (merge N P).code =
      ((List.range ((N * N) * P)).map (unshiftedMergeCode N P),
        (List.range ((N * N) * P)).map (fun q => (N * N) * P + q)) := by
  rw [merge, Adjacency.pi_inputGate_code
    _ (fun q => unshiftedMergeCode N P q.val)]
  · simp only [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
      List.map_map, Function.comp_def]
  · intro q
    simpa only [unshiftedMergeCode, finProdFinEquiv_symm_apply, Fin.divNat, Fin.modNat] using
      mergeEntry_code (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
  · intro q j hj
    have he : q.val / P < N * N := (finProdFinEquiv.symm q).1.isLt
    dsimp only [unshiftedMergeCode] at hj
    split_ifs at hj with hk
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> nlinarith
    · simp at hj

theorem compCodeWire_input_range (n m : ℕ) (gs : List (Op × List ℕ))
    (out : ℕ → ℕ) {i : ℕ} (hi : i < m) :
    compCodeWire n (gs, (List.range m).map out) i = out i := by
  simp [compCodeWire, hi, List.getD_eq_getElem?_getD]

/-- Feed a parallel input-only gate layer through an arbitrary previous block.
Only the output indices of the prefix matter; none of its gates are copied. -/
theorem serial_layer_code (n m w : ℕ) (gs : List (Op × List ℕ))
    (out : ℕ → ℕ) (g : ℕ → Op × List ℕ)
    (hg : ∀ j < w, ∀ i ∈ (g j).2, i < m) :
    compCode n ((List.range w).map g, (List.range w).map (fun j => m + j))
      (gs, (List.range m).map out) =
    (gs ++ (List.range w).map (fun j => ((g j).1, (g j).2.map out)),
      (List.range w).map (fun j => n + gs.length + j)) := by
  apply Prod.ext
  · simp only [compCode, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro j hj
    congr 1
    apply List.map_congr_left
    intro i hi
    exact compCodeWire_input_range n m gs out (hg j (List.mem_range.mp hj) i hi)
  · simp only [compCode, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro j _
    simp [compCodeWire, show ¬ m + j < m by omega]

theorem unshiftedMergeCode_inputs (N P : ℕ) {q : ℕ} (hq : q < (N * N) * P) :
    ∀ j ∈ (unshiftedMergeCode N P q).2, j < (N * N) * P := by
  have hP : 0 < P := by nlinarith
  have he : q / P < N * N := (Nat.div_lt_iff_lt_mul hP).mpr hq
  intro j hj
  dsimp only [unshiftedMergeCode] at hj
  split_ifs at hj with hk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> nlinarith
  · simp at hj

/-- Gate table of repeated fixed-width pair merging, with consecutive outputs. -/
def mergeRoundsGate (N P q : ℕ) : Op × List ℕ :=
  let W := (N * N) * P
  let g := unshiftedMergeCode N P (q % W)
  (g.1, g.2.map (fun i => (q / W) * W + i))

theorem mergeRounds_code (N P d : ℕ) :
    (mergeRounds N P d).code =
      ((List.range (d * ((N * N) * P))).map (mergeRoundsGate N P),
        (List.range ((N * N) * P)).map (fun i => d * ((N * N) * P) + i)) := by
  let W := (N * N) * P
  by_cases hW : W = 0
  · have hW' : (N * N) * P = 0 := hW
    have hs : (mergeRounds N P d).size = 0 := by
      simp only [mergeRounds_size, hW', Nat.mul_zero]
    have hg : (mergeRounds N P d).code.1 = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [Circuit.length_code_fst]
      exact hs
    have ho : (mergeRounds N P d).code.2 = [] := by
      change (List.ofFn _ : List ℕ) = []
      exact List.eq_nil_of_length_eq_zero (by simpa only [List.length_ofFn] using hW')
    apply Prod.ext <;> simp only [hg, ho, hW', Nat.mul_zero, List.range_zero, List.map_nil]
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW
  induction d with
  | zero => simp [mergeRounds]
  | succ d ih =>
    rw [mergeRounds, ← compCode_code, merge_code, ih,
      serial_layer_code _ _ _ _ _ _ (fun j hj => unshiftedMergeCode_inputs N P hj)]
    simp only [List.length_map, List.length_range]
    change ((List.range (d * W)).map (mergeRoundsGate N P) ++
      (List.range W).map (fun j => ((unshiftedMergeCode N P j).1,
        (unshiftedMergeCode N P j).2.map (fun i => d * W + i))),
      (List.range W).map (fun j => W + d * W + j)) =
      ((List.range ((d + 1) * W)).map (mergeRoundsGate N P),
        (List.range W).map (fun i => (d + 1) * W + i))
    rw [Nat.succ_mul, List.range_add, List.map_append, List.map_map]
    apply Prod.ext
    · dsimp only
      congr 1
      apply List.map_congr_left
      intro j hj
      have hj' : j < W := List.mem_range.mp hj
      have hdiv : (d * W + j) / W = d := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hWpos, Nat.div_eq_of_lt hj']
        omega
      have hmod : (d * W + j) % W = j := by simp [Nat.mod_eq_of_lt hj']
      simp only [Function.comp_def, mergeRoundsGate,
        show (N * N) * P = W from rfl, hdiv, hmod]
    · dsimp only
      apply List.map_congr_left
      intro j _
      omega

end PredictionDepth.StandardComplexity.StandardPower
