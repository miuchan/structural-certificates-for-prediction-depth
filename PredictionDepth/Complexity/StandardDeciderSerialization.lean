import PredictionDepth.Complexity.StandardPowerSerialization
import PredictionDepth.Complexity.PowerLayoutArithmetic

/-! Exact agreement of the typed accepting circuit with its streamed gate table. -/

namespace PredictionDepth.StandardComplexity.StandardPower
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open RegularCompositionCode

theorem acceptingEntry_code {N : ℕ} (start : Fin N) (accept : Fin N → Bool)
    (acceptNat : ℕ → Bool) (ha : ∀ i : Fin N, acceptNat i.val = accept i)
    (j : Fin (width N)) :
    (acceptingEntry start accept j).code =
      ([acceptingGateCode N start.val acceptNat 0 j.val], [N * N]) := by
  by_cases hj : j.val < N
  · rw [acceptingEntry, dite_eq_left hj]
    have hjmod : j.val % width N = j.val := Nat.mod_eq_of_lt j.isLt
    simp only [acceptingGateCode, hjmod, ite_eq_left hj, ha ⟨j.val, hj⟩,
      matrixWire]
    by_cases hb : accept ⟨j.val, hj⟩ = true
    · rw [ite_eq_left hb, ite_eq_left hb]
      change ([(Op.and, [_, _])], [N * N]) = _
      simp [ParallelReachability.index, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
    · rw [ite_eq_right hb, ite_eq_right hb]
      rfl
  · rw [acceptingEntry, dite_eq_right hj]
    simp only [acceptingGateCode, Nat.mod_eq_of_lt j.isLt, ite_eq_right hj]
    rfl

theorem acceptingGateCode_zero_inputs {N : ℕ} (start : Fin N) (acceptNat : ℕ → Bool)
    (q : ℕ) : ∀ i ∈ (acceptingGateCode N start.val acceptNat 0 q).2, i < N * N := by
  intro i hi
  simp only [acceptingGateCode, matrixWire, ↓reduceIte] at hi
  split_ifs at hi with hk ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
    subst i
    nlinarith [start.isLt]
  · simp at hi
  · simp at hi

theorem acceptingLeaves_code {N : ℕ} (start : Fin N) (accept : Fin N → Bool)
    (acceptNat : ℕ → Bool) (ha : ∀ i : Fin N, acceptNat i.val = accept i) :
    (acceptingLeaves start accept).code =
      ((List.range (layerWidth N)).map (acceptingGateCode N start.val acceptNat 0),
        (List.range (layerWidth N)).map (fun i => N * N + i)) := by
  rw [acceptingLeaves, CircuitWriter.pi_inputGate_code _
    (fun q => acceptingGateCode N start.val acceptNat 0 q.val)]
  · simp only [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
      List.map_map, Function.comp_def]
  · intro q
    simpa only [acceptingGateCode, finProdFinEquiv_symm_apply, Fin.modNat, Nat.mod_mod] using
      acceptingEntry_code start accept acceptNat ha (finProdFinEquiv.symm q).2
  · intro q i hi
    exact acceptingGateCode_zero_inputs start acceptNat q.val i hi

theorem rootSelector_code {N : ℕ} (start : Fin N) :
    (rootSelector start).code =
      ([], [(start.val * N + start.val) * width N]) := by
  simp [rootSelector, Circuit.code_wiring, slot, ParallelReachability.index,
    finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem rewire_acceptingGateCode (N start : ℕ) (accept : ℕ → Bool) (stage q : ℕ) :
    ((acceptingGateCode N start accept 0 q).1,
      (acceptingGateCode N start accept 0 q).2.map (matrixWire N stage)) =
      acceptingGateCode N start accept stage q := by
  dsimp only [acceptingGateCode]
  split_ifs <;> simp only [matrixWire, ↓reduceIte, List.map_cons, List.map_nil]

theorem accepting_comp_code_blocks {N stage : ℕ} (start : Fin N)
    (accept : Fin N → Bool) (acceptNat : ℕ → Bool)
    (ha : ∀ i : Fin N, acceptNat i.val = accept i)
    (c : Circuit signature (N * N) (N * N)) (gs : List (Op × List ℕ))
    (hc : c.code = (gs, (List.range (N * N)).map (matrixWire N stage)))
    (hg : gs.length = stage * layerWidth N) :
    ((mergeRounds N (width N) N.size).comp ((acceptingLeaves start accept).comp c)).code =
      (gs ++ acceptingRoundGateList N start.val acceptNat stage,
        (List.range (layerWidth N)).map
          (fun i => N * N + (stage + N.size) * layerWidth N + i)) := by
  rw [← compCode_code, ← compCode_code, acceptingLeaves_code start accept acceptNat ha,
    mergeRounds_code, hc]
  rw [serial_layer_code _ _ _ _ _ _ (fun j _ => acceptingGateCode_zero_inputs start acceptNat j)]
  have hrewire : (fun j => ((acceptingGateCode N start.val acceptNat 0 j).1,
      (acceptingGateCode N start.val acceptNat 0 j).2.map (matrixWire N stage))) =
      acceptingGateCode N start.val acceptNat stage := by
    funext j
    exact rewire_acceptingGateCode N start.val acceptNat stage j
  rw [hrewire]
  rw [compCode_affine]
  · simp only [List.map_map, Function.comp_def, hg]
    apply Prod.ext
    · dsimp only
      rw [List.append_assoc]
      apply congrArg (gs ++ ·)
      unfold acceptingRoundGateList
      congr 1
      apply List.map_congr_left
      intro q _
      exact shiftedMergeRoundsGate N stage q
    · dsimp only
      apply List.map_congr_left
      intro i _
      unfold layerWidth
      ring
  · simp only [List.length_append, List.length_map, List.length_range]
    omega

theorem deciderCode_gates (N start : ℕ) (accept : ℕ → Bool) :
    (deciderCode N start accept).1 =
      (powerCode N N.size).1 ++
        acceptingRoundGateList N start accept (N.size * stageCount N) := by
  have hcount : stageCount N ^ 2 * layerWidth N =
      N.size * (stageCount N * layerWidth N) + stageCount N * layerWidth N := by
    unfold stageCount
    ring
  simp only [deciderCode, powerCode]
  rw [hcount, List.range_add, List.map_append, List.map_map]
  rw [show (deciderGate N start accept ∘
      (fun q => N.size * (stageCount N * layerWidth N) + q)) =
      (fun q => deciderGate N start accept (N.size * (stageCount N * layerWidth N) + q)) from rfl,
    deciderGate_round_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  exact deciderGate_prefix N start accept q (List.mem_range.mp hq)

/-- The complete native logspace gate table denotes exactly the previously
verified Cslib accepting circuit, with no source-code consistency premise. -/
theorem decider_code {N : ℕ} (start : Fin N) (accept : Fin N → Bool)
    (acceptNat : ℕ → Bool) (ha : ∀ i : Fin N, acceptNat i.val = accept i) :
    (decider start accept).code = deciderCode N start.val acceptNat := by
  let gs := (powerCode N N.size).1
  let stage := N.size * stageCount N
  have hc : (power N N.size).code =
      (gs, (List.range (N * N)).map (matrixWire N stage)) := by
    rw [power_code]
    rfl
  have hg : gs.length = stage * layerWidth N := by
    simp only [gs, powerCode, List.length_map, List.length_range, stage, Nat.mul_assoc]
  have hslot : (start.val * N + start.val) * width N < layerWidth N := by
    have hentry : start.val * N + start.val < N * N := by nlinarith [start.isLt]
    exact Nat.mul_lt_mul_of_pos_right hentry (Nat.two_pow_pos _)
  rw [decider, ← compCode_code, rootSelector_code,
    accepting_comp_code_blocks start accept acceptNat ha (power N N.size) gs hc hg]
  apply Prod.ext
  · simp only [compCode, List.map_nil, List.append_nil]
    exact (deciderCode_gates N start.val acceptNat).symm
  · simp only [compCode, List.map_singleton]
    rw [compCodeWire_input_range (N * N) (layerWidth N) _ _ hslot]
    change [N * N + (stage + N.size) * layerWidth N +
      (start.val * N + start.val) * width N] = [deciderOutput N start.val]
    have he : stage + N.size = stageCount N ^ 2 - 1 := by
      have hpow : stageCount N ^ 2 = stage + N.size + 1 := by
        dsimp only [stage, stageCount]
        ring
      omega
    rw [he]
    rfl

theorem decider_code_nat {N : ℕ} (start : Fin N) (accept : ℕ → Bool) :
    (decider start (fun i => accept i.val)).code = deciderCode N start.val accept :=
  decider_code start _ accept (fun _ => rfl)

end PredictionDepth.StandardComplexity.StandardPower
