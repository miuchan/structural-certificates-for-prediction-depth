import PredictionDepth.Complexity.StandardPowerLayout
import Mathlib.Tactic.Ring

/-! Closed index arithmetic for one matrix-power block and its accepting block. -/

namespace PredictionDepth.StandardComplexity.StandardPower

open Cslib.Circuits.Boolean

def roundGateList (N s : ℕ) : List (Op × List ℕ) :=
  (List.range (layerWidth N)).map (productGateCode N s) ++
    (List.range (N.size * layerWidth N)).map
      (fun q => mergeGateCode N (s + 1 + q / layerWidth N) (q % layerWidth N))

def acceptingRoundGateList (N start : ℕ) (accept : ℕ → Bool) (s : ℕ) : List (Op × List ℕ) :=
  (List.range (layerWidth N)).map (acceptingGateCode N start accept s) ++
    (List.range (N.size * layerWidth N)).map
      (fun q => mergeGateCode N (s + 1 + q / layerWidth N) (q % layerWidth N))

theorem round_index_div (N r q : ℕ) (hW : 0 < layerWidth N) :
    (r * (stageCount N * layerWidth N) + q) / layerWidth N =
      r * stageCount N + q / layerWidth N := by
  rw [show r * (stageCount N * layerWidth N) + q =
    layerWidth N * (r * stageCount N) + q by ring]
  exact Nat.mul_add_div hW _ _

theorem round_index_mod (N r q : ℕ) :
    (r * (stageCount N * layerWidth N) + q) % layerWidth N = q % layerWidth N := by
  rw [show r * (stageCount N * layerWidth N) + q =
    layerWidth N * (r * stageCount N) + q by ring]
  exact Nat.mul_add_mod_self_left _ _ _

theorem powerGate_round_first (N r q : ℕ) (hq : q < layerWidth N) :
    powerGate N (r * (stageCount N * layerWidth N) + q) =
      productGateCode N (r * stageCount N) q := by
  have hW : 0 < layerWidth N := by omega
  simp only [powerGate, round_index_div N r q hW, round_index_mod,
    Nat.div_eq_of_lt hq, Nat.mod_eq_of_lt hq, Nat.add_zero,
    Nat.mul_mod_left, ↓reduceIte]

theorem merge_index_div (N q : ℕ) (hW : 0 < layerWidth N) :
    (layerWidth N + q) / layerWidth N = 1 + q / layerWidth N := by
  rw [Nat.add_div_left _ hW]
  omega

theorem merge_quotient_lt (N q : ℕ) (hq : q < N.size * layerWidth N) :
    1 + q / layerWidth N < stageCount N := by
  have hW : 0 < layerWidth N := by
    by_contra h
    have : layerWidth N = 0 := by omega
    simp [this] at hq
  have hdiv : q / layerWidth N < N.size :=
    (Nat.div_lt_iff_lt_mul hW).mpr hq
  simpa only [stageCount, Nat.add_comm] using Nat.add_lt_add_left hdiv 1

theorem powerGate_round_merge (N r q : ℕ) (hq : q < N.size * layerWidth N) :
    powerGate N (r * (stageCount N * layerWidth N) + (layerWidth N + q)) =
      mergeGateCode N (r * stageCount N + 1 + q / layerWidth N) (q % layerWidth N) := by
  have hW : 0 < layerWidth N := by
    by_contra h
    have : layerWidth N = 0 := by omega
    simp [this] at hq
  have hl := merge_quotient_lt N q hq
  simp only [powerGate, round_index_div N r (layerWidth N + q) hW,
    round_index_mod, merge_index_div N q hW, Nat.add_mod_left,
    Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hl]
  have hne : (1 : ℕ) + q / layerWidth N ≠ 0 := by simp
  rw [ite_eq_right hne]
  congr 1
  omega

/-- The complete global block agrees with its local product-then-merge layout,
including the degenerate zero-width case. -/
theorem powerGate_round_map (N r : ℕ) :
    (List.range (stageCount N * layerWidth N)).map
      (fun q => powerGate N (r * (stageCount N * layerWidth N) + q)) =
      roundGateList N (r * stageCount N) := by
  nth_rw 2 [show stageCount N * layerWidth N = layerWidth N + N.size * layerWidth N by
    unfold stageCount; ring]
  rw [List.range_add (n := layerWidth N) (m := N.size * layerWidth N), List.map_append]
  unfold roundGateList
  congr 1
  · apply List.map_congr_left
    intro q hq
    exact powerGate_round_first N r q (List.mem_range.mp hq)
  · rw [List.map_map]
    apply List.map_congr_left
    intro q hq
    simpa only [Function.comp_def] using powerGate_round_merge N r q (List.mem_range.mp hq)

theorem deciderGate_prefix (N start : ℕ) (accept : ℕ → Bool) (q : ℕ)
    (hq : q < N.size * (stageCount N * layerWidth N)) :
    deciderGate N start accept q = powerGate N q := by
  have hW : 0 < layerWidth N := by
    by_contra h
    have : layerWidth N = 0 := by omega
    simp [this] at hq
  have hdiv : q / layerWidth N < N.size * stageCount N :=
    (Nat.div_lt_iff_lt_mul hW).mpr (by simpa only [Nat.mul_assoc] using hq)
  simp [deciderGate, hdiv]

theorem deciderGate_round_first (N start : ℕ) (accept : ℕ → Bool) (q : ℕ)
    (hq : q < layerWidth N) :
    deciderGate N start accept (N.size * (stageCount N * layerWidth N) + q) =
      acceptingGateCode N start accept (N.size * stageCount N) q := by
  have hW : 0 < layerWidth N := by omega
  simp only [deciderGate, round_index_div N N.size q hW, round_index_mod,
    Nat.div_eq_of_lt hq, Nat.mod_eq_of_lt hq, Nat.add_zero,
    Nat.lt_irrefl, ↓reduceIte, Nat.mul_mod_left]

theorem deciderGate_round_merge (N start : ℕ) (accept : ℕ → Bool) (q : ℕ)
    (hq : q < N.size * layerWidth N) :
    deciderGate N start accept (N.size * (stageCount N * layerWidth N) + (layerWidth N + q)) =
      mergeGateCode N (N.size * stageCount N + 1 + q / layerWidth N) (q % layerWidth N) := by
  have hW : 0 < layerWidth N := by
    by_contra h
    have : layerWidth N = 0 := by omega
    simp [this] at hq
  have hl := merge_quotient_lt N q hq
  simp only [deciderGate, round_index_div N N.size (layerWidth N + q) hW,
    round_index_mod, merge_index_div N q hW, Nat.add_mod_left]
  have hnot : ¬ N.size * stageCount N + ((1 : ℕ) + q / layerWidth N) <
      N.size * stageCount N := Nat.not_lt.mpr (Nat.le_add_right _ _)
  rw [ite_eq_right hnot]
  simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hl]
  have hne : (1 : ℕ) + q / layerWidth N ≠ 0 := by simp
  rw [ite_eq_right hne]
  congr 1
  omega

/-- After all matrix-power blocks, the accepting block has the same merge
layout but a different first layer. -/
theorem deciderGate_round_map (N start : ℕ) (accept : ℕ → Bool) :
    (List.range (stageCount N * layerWidth N)).map
      (fun q => deciderGate N start accept (N.size * (stageCount N * layerWidth N) + q)) =
      acceptingRoundGateList N start accept (N.size * stageCount N) := by
  nth_rw 2 [show stageCount N * layerWidth N = layerWidth N + N.size * layerWidth N by
    unfold stageCount; ring]
  rw [List.range_add (n := layerWidth N) (m := N.size * layerWidth N), List.map_append]
  unfold acceptingRoundGateList
  congr 1
  · apply List.map_congr_left
    intro q hq
    exact deciderGate_round_first N start accept q (List.mem_range.mp hq)
  · rw [List.map_map]
    apply List.map_congr_left
    intro q hq
    simpa only [Function.comp_def] using deciderGate_round_merge N start accept q (List.mem_range.mp hq)

end PredictionDepth.StandardComplexity.StandardPower
