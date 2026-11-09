import PredictionDepth.Complexity.RegularCompositionCode
import PredictionDepth.Complexity.PowerLayoutArithmetic

/-! Exact serialization of the previously verified, shared power circuit. -/
namespace PredictionDepth.StandardComplexity.StandardPower
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open RegularCompositionCode

def stageRewire (N stage i : ℕ) : ℕ :=
  if i < N * N then matrixWire N stage i else stage * layerWidth N + i

def rewireGate (f : ℕ → ℕ) (g : Op × List ℕ) : Op × List ℕ := (g.1, g.2.map f)

theorem compCodeWire_stage (N stage : ℕ) (gs : List (Op × List ℕ))
    (hg : gs.length = stage * layerWidth N) :
    compCodeWire (N * N) (gs, (List.range (N * N)).map (matrixWire N stage)) =
      stageRewire N stage := by
  funext i
  by_cases hi : i < N * N
  · simpa only [stageRewire, hi, ↓reduceIte] using
      compCodeWire_input_range (N * N) (N * N) gs (matrixWire N stage) hi
  · simp only [compCodeWire, stageRewire, List.length_map, List.length_range, hi,
      ↓reduceIte, hg]
    omega

theorem productGateCode_zero (N q : ℕ) :
    productGateCode N 0 q = unshiftedProductCode N (width N) q := by
  dsimp only [productGateCode, unshiftedProductCode]
  split_ifs <;> simp only [matrixWire, ↓reduceIte]

theorem rewire_productGateCode (N stage q : ℕ) (hq : q < layerWidth N) :
    rewireGate (stageRewire N stage) (productGateCode N 0 q) = productGateCode N stage q := by
  rw [productGateCode_zero, ← rewiredProductCode]
  apply Prod.ext
  · rfl
  · apply List.map_congr_left
    intro i hi
    have hb := unshiftedProductCode_inputs N (width N) hq i hi
    exact ite_eq_left hb

theorem rewire_shiftGate (N stage : ℕ) (g : Op × List ℕ) :
    rewireGate (stageRewire N stage) (shiftGate (N * N) g) =
      shiftGate (N * N + stage * layerWidth N) g := by
  apply Prod.ext
  · rfl
  · simp only [rewireGate, shiftGate, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i _
    simp only [stageRewire, show ¬ N * N + i < N * N by omega, ↓reduceIte]
    omega

theorem rewire_square_output (N stage i : ℕ) :
    stageRewire N stage (N * N + N.size * layerWidth N + i * width N) =
      matrixWire N (stage + stageCount N) i := by
  have hn : stage + stageCount N ≠ 0 := by dsimp only [stageCount]; omega
  have hs : stage + stageCount N - 1 = stage + N.size := by dsimp only [stageCount]; omega
  have hi : ¬ N * N + N.size * layerWidth N + i * width N < N * N := by omega
  simp only [stageRewire, matrixWire, hi, hn, ↓reduceIte, hs, Nat.add_mul]
  omega

/-- Add one whole square to any prefix with the claimed spaced matrix outputs. -/
theorem square_comp_code_blocks {N stage : ℕ} (c : Circuit signature (N * N) (N * N))
    (gs : List (Op × List ℕ))
    (hc : c.code = (gs, (List.range (N * N)).map (matrixWire N stage)))
    (hg : gs.length = stage * layerWidth N) :
    ((square N).comp c).code =
      (gs ++ ((List.range (layerWidth N)).map (productGateCode N stage) ++
        (List.range (N.size * layerWidth N)).map
          (fun q => mergeGateCode N (stage + 1 + q / layerWidth N) (q % layerWidth N))),
        (List.range (N * N)).map (matrixWire N (stage + stageCount N))) := by
  rw [← compCode_code, square_code_blocks, hc]
  simp only [compCode, compCodeWire_stage N stage gs hg,
    squareGateList, List.map_append, List.map_map, Function.comp_def]
  apply Prod.ext
  · dsimp only
    congr 1
    apply congrArg₂ List.append
    · apply List.map_congr_left
      intro q hq
      exact rewire_productGateCode N stage q (List.mem_range.mp hq)
    · apply List.map_congr_left
      intro q _
      exact (rewire_shiftGate N stage (mergeRoundsGate N (width N) q)).trans
        (shiftedMergeRoundsGate N stage q)
  · dsimp only
    apply List.map_congr_left
    intro i _
    exact rewire_square_output N stage i

/-- The exact serialized power circuit has a direct formula for every gate
and output index. This is the bridge to its actual logspace writer. -/
theorem power_code (N rounds : ℕ) : (power N rounds).code = powerCode N rounds := by
  induction rounds with
  | zero =>
    simp only [power, Circuit.code_wiring_id, powerCode, Nat.zero_mul,
      List.range_zero, List.map_nil, Prod.mk.injEq, true_and]
    rw [show powerOutput N 0 = (id : ℕ → ℕ) by
      funext i
      simp [powerOutput, matrixWire]]
    exact (List.map_id _).symm
  | succ r ih =>
    let gs := (List.range (r * (stageCount N * layerWidth N))).map (powerGate N)
    have hc : (power N r).code =
        (gs, (List.range (N * N)).map (matrixWire N (r * stageCount N))) := by
      exact ih
    have hg : gs.length = (r * stageCount N) * layerWidth N := by
      simp only [gs, List.length_map, List.length_range, Nat.mul_assoc]
    change ((square N).comp (power N r)).code = _
    rw [square_comp_code_blocks (power N r) gs hc hg]
    change (gs ++ roundGateList N (r * stageCount N),
      (List.range (N * N)).map (matrixWire N (r * stageCount N + stageCount N))) = _
    simp only [powerCode]
    rw [Nat.succ_mul, List.range_add, List.map_append, List.map_map]
    apply Prod.ext
    · dsimp only
      rw [show (powerGate N ∘ fun x => r * (stageCount N * layerWidth N) + x) =
        (fun q => powerGate N (r * (stageCount N * layerWidth N) + q)) from rfl,
        powerGate_round_map]
    · dsimp only
      apply List.map_congr_left
      intro i _
      change matrixWire N (r * stageCount N + stageCount N) i =
        matrixWire N ((r + 1) * stageCount N) i
      rw [Nat.succ_mul]

end PredictionDepth.StandardComplexity.StandardPower
