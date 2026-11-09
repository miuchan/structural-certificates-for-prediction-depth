import PredictionDepth.Complexity.StandardPowerCode

/-! Constant-space wire arithmetic for regular circuit composition. -/
namespace PredictionDepth.StandardComplexity.RegularCompositionCode
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardPower

abbrev Gate := Op × List ℕ

def shiftGate (base : ℕ) (g : Gate) : Gate := (g.1, g.2.map (fun i => base + i))

theorem compCodeWire_affine (n m base : ℕ) (gs : List Gate)
    (hb : base + m = n + gs.length) (i : ℕ) :
    compCodeWire n (gs, (List.range m).map (fun j => base + j)) i = base + i := by
  by_cases hi : i < m
  · exact compCodeWire_input_range n m gs _ hi
  · simp only [compCodeWire, List.length_map, List.length_range, hi, ↓reduceIte]
    omega

/-- Consecutive output wires permit a pure affine relocation of an entire
later circuit, even for references to its own intermediate gates. -/
theorem compCode_affine (n m base : ℕ) (gs : List Gate)
    (hb : base + m = n + gs.length) (later : List Gate × List ℕ) :
    compCode n later (gs, (List.range m).map (fun j => base + j)) =
      (gs ++ later.1.map (shiftGate base), later.2.map (fun j => base + j)) := by
  have hw := funext (compCodeWire_affine n m base gs hb)
  simp only [compCode, hw]
  rfl

theorem unshiftedProductCode_inputs (N P : ℕ) {q : ℕ} (hq : q < (N * N) * P) :
    ∀ j ∈ (unshiftedProductCode N P q).2, j < N * N := by
  have hP : 0 < P := by nlinarith
  have he : q / P < N * N := (Nat.div_lt_iff_lt_mul hP).mpr hq
  intro j hj
  dsimp only [unshiftedProductCode] at hj
  split_ifs at hj with hk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    have hN : 0 < N := by omega
    have hrow : q / P / N < N := (Nat.div_lt_iff_lt_mul hN).mpr he
    have hcol : q / P % N < N := Nat.mod_lt _ hN
    rcases hj with rfl | rfl <;> nlinarith
  · simp at hj

theorem rewiredProductCode (N stage q : ℕ) :
    ((unshiftedProductCode N (width N) q).1,
      (unshiftedProductCode N (width N) q).2.map (matrixWire N stage)) =
      productGateCode N stage q := by
  dsimp only [unshiftedProductCode, productGateCode]
  split <;> rfl

theorem selectRoots_code (N : ℕ) :
    (selectRoots N).code = ([], (List.range (N * N)).map (fun i => i * width N)) := by
  apply Circuit.code_wiring_eq_map
  intro i
  simp [slot, finProdFinEquiv, Nat.mul_comm]

theorem shiftedMergeRoundsGate (N stage q : ℕ) :
    shiftGate (N * N + stage * layerWidth N) (mergeRoundsGate N (width N) q) =
      mergeGateCode N (stage + 1 + q / layerWidth N) (q % layerWidth N) := by
  have hs : stage + 1 + q / ((N * N) * width N) - 1 =
      stage + q / ((N * N) * width N) := by
    rw [Nat.add_right_comm stage 1, Nat.add_sub_cancel]
  dsimp only [shiftGate, mergeRoundsGate, unshiftedMergeCode, mergeGateCode, layerWidth]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Prod.mk.injEq, true_and,
      List.cons.injEq, and_true, hs, Nat.add_mul]
    constructor <;> omega
  · rfl

theorem compCode_selection (n m count : ℕ) (gs : List Gate)
    (out select : ℕ → ℕ) (hs : ∀ i < count, select i < m) :
    compCode n ([], (List.range count).map select) (gs, (List.range m).map out) =
      (gs, (List.range count).map (fun i => out (select i))) := by
  apply Prod.ext
  · simp only [compCode, List.map_nil, List.append_nil]
  · simp only [compCode, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i hi
    exact compCodeWire_input_range n m gs out (hs i (List.mem_range.mp hi))

def squareGateList (N : ℕ) : List Gate :=
  (List.range (layerWidth N)).map (productGateCode N 0) ++
    (List.range (N.size * layerWidth N)).map
      (fun q => shiftGate (N * N) (mergeRoundsGate N (width N) q))

@[simp] theorem squareGateList_length (N : ℕ) :
    (squareGateList N).length = stageCount N * layerWidth N := by
  simp only [squareGateList, List.length_append, List.length_map, List.length_range, stageCount]
  ring

theorem square_code_blocks (N : ℕ) :
    (square N).code = (squareGateList N,
      (List.range (N * N)).map (fun i => N * N + N.size * layerWidth N + i * width N)) := by
  have hprod : unshiftedProductCode N (width N) = productGateCode N 0 := by
    funext q
    dsimp only [unshiftedProductCode, productGateCode]
    split_ifs <;> simp only [matrixWire, ↓reduceIte]
  rw [square, ← compCode_code, ← compCode_code, selectRoots_code,
    mergeRounds_code, products_code, compCode_affine]
  · simp only [List.map_map, Function.comp_def]
    rw [compCode_selection]
    · simp only [squareGateList, hprod]
      congr 1
      apply List.map_congr_left
      intro i _
      dsimp only [layerWidth]
      omega
    · intro i hi
      exact Nat.mul_lt_mul_of_pos_right hi (Nat.two_pow_pos _)
  · simp only [List.length_map, List.length_range]

end PredictionDepth.StandardComplexity.RegularCompositionCode
