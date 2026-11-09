import PredictionDepth.Complexity.UniformOR
import CslibFrontier.Computability.Circuit.FanIn

/-!
# An optimal-depth genuinely uniform OR family

The initial circuit is free identity wiring. Each regular merge layer uses
OR on complete pairs and copies an unmatched last input. Thus positive arity
needs exactly `ceil(log₂ n)` layers, without the initialization layer of the
more general padded construction. Arity zero has a separate false gate.
-/

namespace PredictionDepth.StandardComplexity.UniformOROptimal
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM

def stages (n : ℕ) : ℕ → Circuit signature n n
  | 0 => Circuit.id signature n
  | d + 1 => (UniformOR.merge n).comp (stages n d)

theorem stages_eval (n d : ℕ) (x : Fin n → Bool) :
    (stages n d).eval interpretation x = UniformOR.mergeValues d x := by
  induction d with
  | zero => rfl
  | succ d ih => simp [stages, Circuit.eval_comp, ih, UniformOR.merge_eval, UniformOR.mergeValues]

theorem stages_size (n d : ℕ) : (stages n d).size = n * d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [stages, ih]; ring

theorem stages_depth (n d : ℕ) : (stages n d).depth ≤ d := by
  induction d with
  | zero => simp [stages]
  | succ d ih =>
    exact (Circuit.depth_comp_le _ _).trans (by
      have := UniformOR.merge_depth n
      omega)

def positiveFamily (n : ℕ) (hn : 0 < n) : Circuit signature n 1 :=
  (Circuit.wiring signature (fun _ : Fin 1 => (⟨0, hn⟩ : Fin n))).comp
    (stages n (UniformOR.levels n))

def family (n : ℕ) : Circuit signature n 1 :=
  if hn : 0 < n then positiveFamily n hn
  else Circuit.oneGate (.const false) Fin.elim0

theorem positiveFamily_depth (n : ℕ) (hn : 0 < n) :
    (positiveFamily n hn).depth ≤ Nat.clog 2 n := by
  apply (Circuit.depth_comp_le _ _).trans
  simpa only [Circuit.depth_wiring, Nat.zero_add, UniformOR.levels_eq_clog] using
    stages_depth n (UniformOR.levels n)

theorem family_depth (n : ℕ) (hn : 0 < n) : (family n).depth ≤ Nat.clog 2 n := by
  simpa only [family, dite_eq_left hn] using positiveFamily_depth n hn

theorem positiveFamily_true_iff (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) :
    (positiveFamily n hn).eval interpretation x 0 = true ↔ ∃ i, x i = true := by
  have he := congrFun (UniformOR.extend_mergeValues (UniformOR.levels n) x) 0
  rw [RegularReduction.extend_in_range _ (⟨0, hn⟩ : Fin n)] at he
  simp only [positiveFamily, Circuit.eval_comp, Circuit.eval_wiring, Function.comp_apply,
    stages_eval]
  rw [he, RegularReduction.reduce_root_true_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    by_cases hin : i < n
    · exact ⟨⟨i, hin⟩, by simpa [RegularReduction.extend, hin] using hi⟩
    · simp [RegularReduction.extend, hin] at hi
  · rintro ⟨i, hi⟩
    have hp := Nat.le_pow_clog (by omega : 1 < (2 : ℕ)) n
    rw [← UniformOR.levels_eq_clog] at hp
    exact ⟨i.val, i.isLt.trans_le hp, by simpa using hi⟩

theorem family_true_iff (n : ℕ) (x : Fin n → Bool) :
    (family n).eval interpretation x 0 = true ↔ ∃ i, x i = true := by
  by_cases hn : 0 < n
  · simpa only [family, dite_eq_left hn] using positiveFamily_true_iff n hn x
  · have hn0 : n = 0 := by omega
    subst n
    simp [family, interpretation]

/-- The same model's unconditional lower bound; no uniformity or size premise
is required for this direction. -/
theorem or_depth_lower_bound {n : ℕ} (c : Circuit signature n 1)
    (hc : ∀ x, c.eval interpretation x 0 = boolOr n x) : Nat.clog 2 n ≤ c.depth := by
  have hcompute : c.Computes interpretation (fun x _ => boolOr n x) := by
    intro x
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hc x
  have hess (i : Fin n) : EssentialAt (fun x (_ : Fin 1) => boolOr n x) i := by
    obtain ⟨x, y, hxy, hne⟩ := boolOr_essential i
    exact ⟨x, y, hxy, fun he => hne (congrFun he 0)⟩
  have h := c.essential_le_depth hcompute (selected := Finset.univ)
    (fun i _ => hess i) c.fanInAtMost_two
  apply (Nat.clog_le_iff_le_pow (by omega : 1 < (2 : ℕ))).mpr
  simpa using h

theorem family_exact_depth (n : ℕ) (hn : 0 < n) : (family n).depth = Nat.clog 2 n := by
  apply Nat.le_antisymm (family_depth n hn)
  apply or_depth_lower_bound
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [family_true_iff, boolOr, decide_eq_true_eq]

/-! ### Regular code without an initialization layer -/

def gateCode (n q : ℕ) : Op × List ℕ :=
  if n = 0 then (.const false, [])
  else UniformOR.mergeGateCode n ((q / n) * n) (q % n)

def stageCode (n d : ℕ) : List (Op × List ℕ) × List ℕ :=
  ((List.range (n * d)).map (gateCode n), (List.range n).map (fun i => d * n + i))

theorem gateCode_block (n d j : ℕ) (hj : j < n) :
    gateCode n (n * d + j) = UniformOR.mergeGateCode n (d * n) j := by
  have hn : 0 < n := by omega
  simp only [gateCode, Nat.ne_of_gt hn, ↓reduceIte]
  rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hj, Nat.add_zero,
    Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hj]

theorem stageCode_wire (n d i : ℕ) : compCodeWire n (stageCode n d) i = d * n + i := by
  by_cases hi : i < n
  · simp [compCodeWire, stageCode, hi, List.getD_eq_getElem?_getD]
  · simp only [compCodeWire, stageCode, List.length_map, List.length_range, hi, ↓reduceIte]
    have hn : n ≤ i := by omega
    have hcomm : n * d = d * n := Nat.mul_comm _ _
    omega

theorem stages_code (n d : ℕ) : (stages n d).code = stageCode n d := by
  induction d with
  | zero =>
    rw [stages, Circuit.code_wiring_id]
    simp [stageCode]
  | succ d ih =>
    rw [stages, ← compCode_code, UniformOR.merge_code, ih]
    have hw := funext (stageCode_wire n d)
    simp only [compCode, hw]
    simp only [stageCode, List.map_map, Function.comp_def]
    rw [show n * (d + 1) = n * d + n by ring, List.range_add, List.map_append, List.map_map]
    apply Prod.ext
    · dsimp only
      congr 1
      apply List.map_congr_left
      intro j hj
      simp only [Function.comp_def]
      rw [gateCode_block n d j (List.mem_range.mp hj)]
      exact UniformOR.mergeGateCode_shift n (d * n) j
    · dsimp only
      apply List.map_congr_left
      intro j _
      ring

def gateCount (n : ℕ) : ℕ := if n = 0 then 1 else n * UniformOR.levels n
def outputWire (n : ℕ) : ℕ := UniformOR.levels n * n

theorem positiveFamily_code (n : ℕ) (hn : 0 < n) :
    (positiveFamily n hn).code =
      ((List.range (n * UniformOR.levels n)).map (gateCode n), [outputWire n]) := by
  rw [positiveFamily, ← compCode_code, Circuit.code_wiring, stages_code]
  simp only [compCode, List.ofFn_succ, List.ofFn_zero, List.map_nil, List.map_cons,
    List.append_nil]
  rw [stageCode_wire]
  simp only [stageCode, outputWire, Nat.add_zero]

theorem family_code (n : ℕ) :
    (family n).code = ((List.range (gateCount n)).map (gateCode n), [outputWire n]) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · have hp := Nat.pos_of_ne_zero hn
    simpa only [family, dite_eq_left hp, gateCount, ite_eq_right hn] using positiveFamily_code n hp

theorem family_size (n : ℕ) : (family n).size = gateCount n := by
  have h := congrArg (fun c : List (Op × List ℕ) × List ℕ => c.1.length) (family_code n)
  rw [← Circuit.length_code_fst (family n)]
  simpa only [List.length_map, List.length_range] using h

theorem family_size_bound (n : ℕ) : (family n).size ≤ (n + 1) ^ 2 := by
  rw [family_size]
  have h := UniformOR.levels_le n
  unfold gateCount
  split_ifs <;> nlinarith

theorem gateCount_polynomial : PolynomiallyBounded gateCount := by
  apply PolynomiallyBounded.of_forall_le 1 2
  intro n
  have h := UniformOR.levels_le n
  unfold gateCount
  split_ifs <;> nlinarith

/-! ### Actual finite-machine serialization -/

open ComputableInSpace
section Generator
variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

theorem gateCode_budget {n q : α → ℕ}
    (hn : ComputableInSpace n enc encNat S)
    (hq : ComputableInSpace q enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => gateCode (n a) (q a)) enc encGate S := by
  have hmerge := UniformOR.mergeGateCode_budget hn (budget_natMul (budget_natDiv hq hn) hn)
    (budget_natMod hq hn) hin
  exact (budget_ite (budget_natIsZero hn) (budget_const (Op.const false, []) hin) hmerge).of_enc_eq
    fun a => by simp only [gateCode, decide_eq_true_eq]

theorem gateCount_budget {n : α → ℕ} (hn : ComputableInSpace n enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => gateCount (n a)) enc encNat S :=
  (budget_ite (budget_natIsZero hn) (budget_const 1 hin)
    (budget_natMul hn (UniformOR.levels_budget hn))).of_enc_eq
    (fun a => by simp only [gateCount, decide_eq_true_eq])

theorem outputWire_budget {n : α → ℕ} (hn : ComputableInSpace n enc encNat S) :
    ComputableInSpace (fun a => outputWire (n a)) enc encNat S :=
  budget_natMul (UniformOR.levels_budget hn) hn

end Generator

theorem family_code_logspace :
    ComputableInLogSpace (fun n => (family n).code) encUnary encCode := by
  have h := CircuitWriter.computableInLogSpace_code
    (G := gateCount) (O := fun _ => 1) (gate := gateCode) (output := fun n _ => outputWire n)
    (gateCount_budget CircuitWriter.length_inSpace CircuitWriter.input_budget)
    (budget_const 1 CircuitWriter.input_budget)
    (gateCode_budget CircuitWriter.length_inSpace CircuitWriter.index_inSpace CircuitWriter.input_budget)
    (outputWire_budget CircuitWriter.length_inSpace) gateCount_polynomial (by fun_prop)
  exact h.congr_fun fun n => by simp [family_code, CircuitWriter.code]

theorem family_uniform : LogspaceUniform family :=
  ((ComputableInLogSpace.id : ComputableInLogSpace (fun n : ℕ => n) encUnary encUnary).pair
    family_code_logspace).congr (fun _ => rfl)

theorem family_polynomialSize : PolynomiallyBounded (fun n => (family n).size) := by
  simpa only [family_size] using gateCount_polynomial

/-- Exact prediction semantics for the radius-one OR dynamics. -/
theorem predicts_automaton (T : ℕ) (x : Fin (2 * T + 1) → Bool) :
    (family (2 * T + 1)).eval interpretation x 0 = ORAutomaton.prediction T x := by
  apply Bool.eq_iff_iff.mpr
  rw [family_true_iff, ORAutomaton.prediction_true_iff]

theorem prediction_exact_depth (T : ℕ) :
    (family (2 * T + 1)).depth = Nat.clog 2 (2 * T + 1) :=
  family_exact_depth _ (by omega)

/-- The exact optimum is attained by this one polynomial-size uniform family;
the lower bound covers every De Morgan circuit, with arbitrary sharing. -/
theorem prediction_optimal (T : ℕ) :
    IsLeast {d | ∃ c : Circuit signature (2 * T + 1) 1, c.depth = d ∧
      ∀ x, c.eval interpretation x 0 = ORAutomaton.prediction T x}
      (Nat.clog 2 (2 * T + 1)) := by
  constructor
  · exact ⟨family (2 * T + 1), prediction_exact_depth T, predicts_automaton T⟩
  · rintro d ⟨c, hd, hc⟩
    rw [← hd]
    apply or_depth_lower_bound c
    intro x
    rw [hc x, ORAutomaton.prediction_eq_boolOr]

/-- A finite native machine generates the exact-depth predictor on unary time. -/
theorem time_indexed_uniform :
    ComputableInLogSpace
      (fun T => (⟨2 * T + 1, family (2 * T + 1)⟩ : Σ n, Circuit signature n 1))
      encUnary (encCircuit 1) := by
  have htwo := ComputableInLogSpace.unaryMulConst 2
    (ComputableInLogSpace.id : ComputableInLogSpace (fun T : ℕ => T) encUnary encUnary)
  have hwidth : ComputableInLogSpace (fun T : ℕ => 2 * T + 1) encUnary encUnary :=
    (htwo.unaryAdd (ComputableInLogSpace.const 1)).congr_fun fun T => by omega
  exact family_uniform.comp hwidth

/-- Complete finite statement of the original OR example: one actual uniform
generator, a fixed quadratic gate budget, and the matching optimal depth. -/
theorem exact_uniform_prediction :
    ComputableInLogSpace
      (fun T => (⟨2 * T + 1, family (2 * T + 1)⟩ : Σ n, Circuit signature n 1))
      encUnary (encCircuit 1) ∧
    ∀ T, (family (2 * T + 1)).size ≤ (2 * T + 2) ^ 2 ∧
      (family (2 * T + 1)).depth = Nat.clog 2 (2 * T + 1) ∧
      (∀ x, (family (2 * T + 1)).eval interpretation x 0 = ORAutomaton.prediction T x) ∧
      IsLeast {d | ∃ c : Circuit signature (2 * T + 1) 1, c.depth = d ∧
        ∀ x, c.eval interpretation x 0 = ORAutomaton.prediction T x}
        (Nat.clog 2 (2 * T + 1)) := by
  refine ⟨time_indexed_uniform, fun T => ⟨?_, prediction_exact_depth T,
    predicts_automaton T, prediction_optimal T⟩⟩
  simpa only [Nat.add_assoc] using family_size_bound (2 * T + 1)

example : (family 0).depth = 1 := by decide +kernel
example : (family 1).depth = 0 := by decide +kernel
example : (family 1).size = 0 := by decide +kernel
example : (family 3).depth = 2 := by decide +kernel

end PredictionDepth.StandardComplexity.UniformOROptimal
