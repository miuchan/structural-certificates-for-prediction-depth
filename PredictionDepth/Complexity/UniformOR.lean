import PredictionDepth.Complexity.UniformNC
import PredictionDepth.Complexity.Logspace
import PredictionDepth.Complexity.CircuitWriter
import PredictionDepth.Complexity.BalancedReduction
import PredictionDepth.ORAutomaton
import CslibFrontier.Computability.Circuit.Pi
import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import Mathlib.Data.Nat.Size

/-!
# A genuine logspace-uniform balanced OR family

The circuit has width `n+1`: an initial layer copies the `n` inputs and adds
one false coordinate. Each subsequent layer merges adjacent pairs, copying
an unmatched last coordinate and filling absent coordinates with false.
The number of merge layers is exactly `ceil(log₂ n)`.
-/

namespace PredictionDepth.StandardComplexity.UniformOR

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM

def levels (n : ℕ) : ℕ := Nat.size (n - 1)

theorem levels_eq_clog (n : ℕ) : levels n = Nat.clog 2 n := by
  unfold levels
  by_cases hn : n = 0
  · simp [hn]
  · apply Nat.le_antisymm
    · apply Nat.size_le.mpr
      have h := Nat.le_pow_clog (by omega : 1 < (2 : ℕ)) n
      omega
    · apply (Nat.clog_le_iff_le_pow (by omega : 1 < (2 : ℕ))).mpr
      have h := Nat.lt_size_self (n - 1)
      omega

theorem levels_le (n : ℕ) : levels n ≤ n := by
  apply Nat.size_le.mpr
  exact (Nat.sub_le n 1).trans_lt (show n < 2 ^ n from Nat.lt_two_pow_self)

def initialValue {n : ℕ} (x : Fin n → Bool) (j : Fin (n + 1)) : Bool :=
  if h : j.val < n then x ⟨j.val, h⟩ else false

def mergeValue {P : ℕ} (x : Fin P → Bool) (j : Fin P) : Bool :=
  if hl : 2 * j.val < P then
    if hr : 2 * j.val + 1 < P then x ⟨2 * j.val, hl⟩ || x ⟨2 * j.val + 1, hr⟩
    else x ⟨2 * j.val, hl⟩
  else false

def mergeValues {P : ℕ} : ℕ → (Fin P → Bool) → Fin P → Bool
  | 0, x => x
  | d + 1, x => mergeValue (mergeValues d x)

theorem extend_mergeValue {P : ℕ} (x : Fin P → Bool) (j : ℕ) :
    RegularReduction.extend (mergeValue x) j =
      (RegularReduction.extend x (2 * j) || RegularReduction.extend x (2 * j + 1)) := by
  by_cases hj : j < P
  · by_cases hl : 2 * j < P
    · by_cases hr : 2 * j + 1 < P
      · simp [RegularReduction.extend, mergeValue, hj, hl, hr]
      · simp [RegularReduction.extend, mergeValue, hj, hl, hr]
    · have hr : ¬2 * j + 1 < P := by omega
      simp [RegularReduction.extend, mergeValue, hj, hl, hr]
  · have hl : ¬2 * j < P := by omega
    have hr : ¬2 * j + 1 < P := by omega
    simp [RegularReduction.extend, hj, hl, hr]

theorem extend_mergeValues {P : ℕ} (d : ℕ) (x : Fin P → Bool) :
    RegularReduction.extend (mergeValues d x) =
      RegularReduction.reduce d (RegularReduction.extend x) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext j
    rw [mergeValues, extend_mergeValue, ih]
    rfl

def initialEntry (n : ℕ) (j : Fin (n + 1)) : Circuit signature n 1 :=
  if h : j.val < n then Circuit.oneGate .and (fun _ => ⟨j.val, h⟩)
  else Circuit.oneGate (.const false) Fin.elim0

def initial (n : ℕ) : Circuit signature n (n + 1) := Circuit.pi (initialEntry n)

def mergeEntry (P : ℕ) (j : Fin P) : Circuit signature P 1 :=
  if hl : 2 * j.val < P then
    if hr : 2 * j.val + 1 < P then Circuit.oneGate .or
      (fun b => if b = 0 then ⟨2 * j.val, hl⟩ else ⟨2 * j.val + 1, hr⟩)
    else Circuit.oneGate .and (fun _ => ⟨2 * j.val, hl⟩)
  else Circuit.oneGate (.const false) Fin.elim0

def merge (P : ℕ) : Circuit signature P P := Circuit.pi (mergeEntry P)

theorem initial_eval (n : ℕ) (x : Fin n → Bool) :
    (initial n).eval interpretation x = initialValue x := by
  funext j
  simp only [initial, Circuit.eval_pi]
  unfold initialEntry initialValue
  split <;> simp [interpretation]

theorem merge_eval (P : ℕ) (x : Fin P → Bool) :
    (merge P).eval interpretation x = mergeValue x := by
  funext j
  simp only [merge, Circuit.eval_pi]
  unfold mergeEntry mergeValue
  split
  · split <;> simp [interpretation]
  · simp [interpretation]

@[simp] theorem initialEntry_size (n : ℕ) (j : Fin (n + 1)) : (initialEntry n j).size = 1 := by
  unfold initialEntry
  split <;> simp

@[simp] theorem mergeEntry_size (P : ℕ) (j : Fin P) : (mergeEntry P j).size = 1 := by
  unfold mergeEntry
  split
  · split <;> simp
  · simp

@[simp] theorem initial_size (n : ℕ) : (initial n).size = n + 1 := by simp [initial]
@[simp] theorem merge_size (P : ℕ) : (merge P).size = P := by simp [merge]

theorem initial_depth (n : ℕ) : (initial n).depth ≤ 1 := by
  apply Circuit.depth_pi_le
  intro j
  unfold initialEntry
  split <;> simp

theorem merge_depth (P : ℕ) : (merge P).depth ≤ 1 := by
  apply Circuit.depth_pi_le
  intro j
  unfold mergeEntry
  split
  · split <;> simp
  · simp

def stages (n : ℕ) : ℕ → Circuit signature n (n + 1)
  | 0 => initial n
  | d + 1 => (merge (n + 1)).comp (stages n d)

theorem stages_eval (n d : ℕ) (x : Fin n → Bool) :
    (stages n d).eval interpretation x = mergeValues d (initialValue x) := by
  induction d with
  | zero => exact initial_eval n x
  | succ d ih => simp [stages, Circuit.eval_comp, ih, merge_eval, mergeValues]

theorem stages_size (n d : ℕ) : (stages n d).size = (n + 1) * (d + 1) := by
  induction d with
  | zero => simp [stages]
  | succ d ih => simp [stages, ih]; ring

theorem stages_depth (n d : ℕ) : (stages n d).depth ≤ d + 1 := by
  induction d with
  | zero => exact initial_depth n
  | succ d ih =>
    exact (Circuit.depth_comp_le _ _).trans (by
      have := merge_depth (n + 1)
      omega)

def family (n : ℕ) : Circuit signature n 1 :=
  (Circuit.wiring signature (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin (n + 1)))).comp
    (stages n (levels n))

theorem family_size (n : ℕ) : (family n).size = (n + 1) * (levels n + 1) := by
  simp [family, stages_size]

theorem family_depth (n : ℕ) : (family n).depth ≤ Nat.clog 2 n + 1 := by
  apply (Circuit.depth_comp_le _ _).trans
  simpa only [Circuit.depth_wiring, Nat.zero_add, levels_eq_clog] using stages_depth n (levels n)

theorem family_true_iff (n : ℕ) (x : Fin n → Bool) :
    (family n).eval interpretation x 0 = true ↔ ∃ i, x i = true := by
  have he := congrFun (extend_mergeValues (levels n) (initialValue x)) 0
  rw [RegularReduction.extend_in_range _ (⟨0, by omega⟩ : Fin (n + 1))] at he
  simp only [family, Circuit.eval_comp, Circuit.eval_wiring, Function.comp_apply, stages_eval]
  rw [he, RegularReduction.reduce_root_true_iff]
  constructor
  · rintro ⟨j, hj, hx⟩
    by_cases h : j < n
    · exact ⟨⟨j, h⟩, by simpa [RegularReduction.extend, initialValue, h,
        show j < n + 1 by omega] using hx⟩
    · have : RegularReduction.extend (initialValue x) j = false := by
        by_cases hj' : j < n + 1 <;> simp [RegularReduction.extend, initialValue, h, hj']
      rw [this] at hx
      cases hx
  · rintro ⟨i, hi⟩
    have hn := Nat.le_pow_clog (by omega : 1 < (2 : ℕ)) n
    rw [← levels_eq_clog] at hn
    exact ⟨i.val, i.isLt.trans_le hn,
      by simpa [RegularReduction.extend, initialValue, i.isLt,
        show i.val < n + 1 by omega] using hi⟩

/-! ### Exact regular wire code -/

def initialGateCode (n j : ℕ) : Op × List ℕ :=
  if j < n then (.and, [j, j]) else (.const false, [])

def mergeGateCode (P base j : ℕ) : Op × List ℕ :=
  if 2 * j < P then
    if 2 * j + 1 < P then (.or, [base + 2 * j, base + 2 * j + 1])
    else (.and, [base + 2 * j, base + 2 * j])
  else (.const false, [])

def stageGateCode (n t j : ℕ) : Op × List ℕ :=
  if t = 0 then initialGateCode n j
  else mergeGateCode (n + 1) (n + (t - 1) * (n + 1)) j

def gateCode (n i : ℕ) : Op × List ℕ :=
  stageGateCode n (i / (n + 1)) (i % (n + 1))

theorem gateCode_block (n t j : ℕ) (hj : j < n + 1) :
    gateCode n ((n + 1) * t + j) = stageGateCode n t j := by
  simp [gateCode, Nat.mul_add_div (by omega : 0 < n + 1), Nat.div_eq_of_lt hj,
    Nat.mod_eq_of_lt hj]

theorem initialEntry_code (n : ℕ) (j : Fin (n + 1)) :
    (initialEntry n j).code = ([initialGateCode n j.val], [n]) := by
  unfold initialEntry initialGateCode
  split <;> simp [Circuit.oneGate, Circuit.code, Program.code, Line.code,
    List.ofFn_succ]

theorem mergeEntry_code (P : ℕ) (j : Fin P) :
    (mergeEntry P j).code = ([mergeGateCode P 0 j.val], [P]) := by
  unfold mergeEntry mergeGateCode
  split
  · split <;> simp [Circuit.oneGate, Circuit.code, Program.code, Line.code,
      List.ofFn_succ]
  · simp [Circuit.oneGate, Circuit.code, Program.code, Line.code, List.ofFn_succ]

theorem initialGateCode_refs (n j : ℕ) : ∀ i ∈ (initialGateCode n j).2, i < n := by
  unfold initialGateCode
  split <;> simp_all

theorem mergeGateCode_refs (P j : ℕ) : ∀ i ∈ (mergeGateCode P 0 j).2, i < P := by
  unfold mergeGateCode
  split
  · split <;> simp_all
  · simp

theorem initial_code (n : ℕ) :
    (initial n).code = ((List.range (n + 1)).map (initialGateCode n),
      (List.range (n + 1)).map (fun j => n + j)) := by
  rw [initial, CircuitWriter.pi_inputGate_code _ _ (initialEntry_code n)
    (fun i => initialGateCode_refs n i.val)]
  simp only [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map, Function.comp_def]

theorem merge_code (P : ℕ) :
    (merge P).code = ((List.range P).map (mergeGateCode P 0),
      (List.range P).map (fun j => P + j)) := by
  rw [merge, CircuitWriter.pi_inputGate_code _ _ (mergeEntry_code P)
    (fun i => mergeGateCode_refs P i.val)]
  simp only [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map, Function.comp_def]

theorem mergeGateCode_shift (P base j : ℕ) :
    ((mergeGateCode P 0 j).1, (mergeGateCode P 0 j).2.map (fun i => base + i)) =
      mergeGateCode P base j := by
  unfold mergeGateCode
  split
  · split <;> simp [Nat.add_assoc]
  · rfl

def stageCode (n d : ℕ) : List (Op × List ℕ) × List ℕ :=
  ((List.range ((n + 1) * (d + 1))).map (gateCode n),
    (List.range (n + 1)).map (fun j => n + d * (n + 1) + j))

theorem stageCode_inputWire (n d i : ℕ) (hi : i < n + 1) :
    compCodeWire n (stageCode n d) i = n + d * (n + 1) + i := by
  simp [compCodeWire, stageCode, hi, List.getD_eq_getElem?_getD]

theorem stageCode_gateWire (n d i : ℕ) :
    compCodeWire n (stageCode n d) (n + 1 + i) = n + (d + 1) * (n + 1) + i := by
  simp only [compCodeWire, stageCode, List.length_map, List.length_range]
  rw [ite_eq_right (by omega : ¬ n + 1 + i < n + 1)]
  simp
  ring

theorem stages_code (n d : ℕ) : (stages n d).code = stageCode n d := by
  induction d with
  | zero =>
    rw [stages, initial_code]
    apply Prod.ext
    · simp only [stageCode, Nat.zero_add, Nat.mul_one]
      apply List.map_congr_left
      intro i hi
      have hi' := List.mem_range.mp hi
      have h := gateCode_block n 0 i hi'
      simpa [stageGateCode] using h.symm
    · simp [stageCode]
  | succ d ih =>
    rw [stages, ← compCode_code, ih, merge_code]
    apply Prod.ext
    · change (stageCode n d).1 ++
        ((List.range (n + 1)).map (mergeGateCode (n + 1) 0)).map
          (fun g => (g.1, g.2.map (compCodeWire n (stageCode n d)))) =
        (List.range ((n + 1) * (d + 1 + 1))).map (gateCode n)
      rw [show (n + 1) * (d + 1 + 1) = (n + 1) * (d + 1) + (n + 1) by ring,
        List.range_add (n := (n + 1) * (d + 1)) (m := n + 1), List.map_append]
      congr 1
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro j hj
      have hj' := List.mem_range.mp hj
      simp only [Function.comp_def]
      rw [gateCode_block n (d + 1) j hj']
      simp only [stageGateCode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel]
      rw [← mergeGateCode_shift (n + 1) (n + d * (n + 1)) j]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact stageCode_inputWire n d i (mergeGateCode_refs _ _ i hi)
    · change ((List.range (n + 1)).map (fun j => n + 1 + j)).map
        (compCodeWire n (stageCode n d)) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro j _
      exact stageCode_gateWire n d j

def gateCount (n : ℕ) : ℕ := (n + 1) * (levels n + 1)
def outputWire (n : ℕ) : ℕ := n + levels n * (n + 1)

theorem family_code (n : ℕ) :
    (family n).code = ((List.range (gateCount n)).map (gateCode n), [outputWire n]) := by
  rw [family, ← compCode_code, Circuit.code_wiring, stages_code]
  simp only [compCode, List.ofFn_succ, List.ofFn_zero, List.map_nil, List.map_cons,
    List.append_nil]
  rw [stageCode_inputWire n (levels n) 0 (by omega)]
  simp [stageCode, gateCount, outputWire]

/-! ### Native logarithmic-space serialization -/

open ComputableInSpace

section Generator
variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

theorem twoInputCode_budget (op : Op) {a b : α → ℕ}
    (ha : ComputableInSpace a enc encNat S) (hb : ComputableInSpace b enc encNat S)
    (hin : (fun x => (enc x).length) ≼ S) :
    ComputableInSpace (fun x => (op, [a x, b x])) enc encGate S :=
  budget_prod (budget_const (encB := encOp) op hin)
    (budget_cons ha (budget_cons hb (budget_const (encB := encList encNat) [] hin)))

theorem initialGateCode_budget {n j : α → ℕ}
    (hn : ComputableInSpace n enc encNat S) (hj : ComputableInSpace j enc encNat S)
    (hin : (fun x => (enc x).length) ≼ S) :
    ComputableInSpace (fun x => initialGateCode (n x) (j x)) enc encGate S :=
  (budget_ite (budget_natLt hj hn) (twoInputCode_budget .and hj hj hin)
    (budget_const (.const false, []) hin)).of_enc_eq fun x => by
      simp only [initialGateCode, decide_eq_true_eq]

theorem mergeGateCode_budget {P base j : α → ℕ}
    (hP : ComputableInSpace P enc encNat S)
    (hb : ComputableInSpace base enc encNat S) (hj : ComputableInSpace j enc encNat S)
    (hin : (fun x => (enc x).length) ≼ S) :
    ComputableInSpace (fun x => mergeGateCode (P x) (base x) (j x)) enc encGate S := by
  have hleft := budget_natMul (budget_const 2 hin) hj
  have hright := budget_natSucc hleft
  have ha := budget_natAdd hb hleft
  have hb' := budget_natSucc ha
  exact (budget_ite (budget_natLt hleft hP)
    (budget_ite (budget_natLt hright hP) (twoInputCode_budget .or ha hb' hin)
      (twoInputCode_budget .and ha ha hin))
    (budget_const (.const false, []) hin)).of_enc_eq fun x => by
      simp only [mergeGateCode, decide_eq_true_eq]

theorem gateCode_budget {n i : α → ℕ}
    (hn : ComputableInSpace n enc encNat S) (hi : ComputableInSpace i enc encNat S)
    (hin : (fun x => (enc x).length) ≼ S) :
    ComputableInSpace (fun x => gateCode (n x) (i x)) enc encGate S := by
  have hP := budget_natSucc hn
  have ht := budget_natDiv hi hP
  have hj := budget_natMod hi hP
  have hbase := budget_natAdd hn (budget_natMul (budget_natPred ht) hP)
  exact (budget_ite (budget_natEq ht (budget_const 0 hin))
    (initialGateCode_budget hn hj hin) (mergeGateCode_budget hP hbase hj hin)).of_enc_eq
      fun x => by simp only [gateCode, stageGateCode, decide_eq_true_eq]

theorem levels_budget {n : α → ℕ} (hn : ComputableInSpace n enc encNat S) :
    ComputableInSpace (fun x => levels (n x)) enc encNat S := by
  unfold levels
  exact budget_comp_linear natSize (budget_natPred hn)

theorem gateCount_budget {n : α → ℕ} (hn : ComputableInSpace n enc encNat S) :
    ComputableInSpace (fun x => gateCount (n x)) enc encNat S :=
  budget_natMul (budget_natSucc hn) (budget_natSucc (levels_budget hn))

theorem outputWire_budget {n : α → ℕ} (hn : ComputableInSpace n enc encNat S) :
    ComputableInSpace (fun x => outputWire (n x)) enc encNat S :=
  budget_natAdd hn (budget_natMul (levels_budget hn) (budget_natSucc hn))

end Generator

theorem gateCount_polynomial : PolynomiallyBounded gateCount := by
  apply PolynomiallyBounded.of_forall_le 1 2
  intro n
  have h := levels_le n
  unfold gateCount
  nlinarith

theorem family_code_logspace :
    ComputableInLogSpace (fun n => (family n).code) encUnary encCode := by
  have hc := CircuitWriter.computableInLogSpace_code
    (G := gateCount) (O := fun _ => 1) (gate := gateCode) (output := fun n _ => outputWire n)
    (gateCount_budget CircuitWriter.length_inSpace)
    (budget_const 1 CircuitWriter.input_budget)
    (gateCode_budget CircuitWriter.length_inSpace CircuitWriter.index_inSpace
      CircuitWriter.input_budget)
    (outputWire_budget CircuitWriter.length_inSpace)
    gateCount_polynomial (PolynomiallyBounded.const 1)
  refine hc.congr_fun ?_
  intro n
  simp [family_code, CircuitWriter.code]

/-- A concrete finite-state logspace machine prints the whole balanced family. -/
theorem family_uniform : LogspaceUniform family := by
  exact ((ComputableInLogSpace.id : ComputableInLogSpace (fun n : ℕ => n) encUnary encUnary).pair
    family_code_logspace).congr (fun _ => rfl)

def language : Set (List Bool) := {x | x.any id = true}

theorem family_decides : FamilyDecides family language := by
  intro x
  change x.any id = true ↔ (family x.length).eval interpretation (BitString.ofList x.length x) 0 = true
  rw [family_true_iff]
  nth_rw 1 [← BitString.ofFn_ofList (word := x) rfl]
  simp [List.any_eq_true, List.mem_ofFn]

/-- The OR language belongs to genuine logspace-uniform NC¹. -/
theorem mem_uniformNC_one : language ∈ UniformNCLevel 1 := by
  refine ⟨family, 2, family_decides, ?_, ?_, family_uniform⟩
  · convert gateCount_polynomial using 1
    funext n
    exact family_size n
  · intro n
    have h := family_depth n
    have hc : Nat.clog 2 n ≤ Nat.log2 n + 1 :=
      Nat.clog_le_of_le_pow Nat.lt_log2_self.le
    rw [Nat.log2_eq_log_two] at hc
    simp only [pow_one]
    omega

/-- The standard uniformly generated circuit predicts the actual radius-one
OR dynamics on its complete `2*T+1` input window. -/
theorem predicts_automaton (T : ℕ) (x : Fin (2 * T + 1) → Bool) :
    (family (2 * T + 1)).eval interpretation x 0 = ORAutomaton.prediction T x := by
  apply Bool.eq_iff_iff.mpr
  rw [family_true_iff, ORAutomaton.prediction_true_iff]

/-- Time-indexed generation is also a native logspace computation. -/
theorem time_indexed_uniform :
    ComputableInLogSpace
      (fun T => (⟨2 * T + 1, family (2 * T + 1)⟩ : Σ n, Circuit signature n 1))
      encUnary (encCircuit 1) := by
  have htwo := ComputableInLogSpace.unaryMulConst 2
    (ComputableInLogSpace.id : ComputableInLogSpace (fun n : ℕ => n) encUnary encUnary)
  have hw : ComputableInLogSpace (fun T : ℕ => 2 * T + 1) encUnary encUnary :=
    (htwo.unaryAdd (ComputableInLogSpace.const 1)).congr_fun fun T => by omega
  exact family_uniform.comp hw

end PredictionDepth.StandardComplexity.UniformOR
