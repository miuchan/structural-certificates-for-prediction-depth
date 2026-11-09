import PredictionDepth.FrozenPascal.PathWitness
import PredictionDepth.Complexity.CircuitWriter
import PredictionDepth.Complexity.CodeLogspaceFamilies

/-!
# Native logspace generators for the one-hot register circuits

The entire finite description is printed by a machine. The two shared
constants are charged as gates, and each output wire is computed from its
binary index. Time digits use the standard unary-to-binary transducer.
-/

namespace PredictionDepth.FrozenPascal.UniformRegisters
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInSpace
open StandardComplexity
open FastComposition

private theorem substitute_outputs {n m : ℕ} (ρ : Fin m → Fin n ⊕ Bool) (i : Fin m) :
    ((substituteCircuit ρ).outputs i).toNat =
      (ρ i).elim Fin.val (fun b => n + if b then 1 else 0) := by
  simp only [substituteCircuit, Circuit.comp, Circuit.wiring, Function.comp_apply]
  cases h : ρ i with
  | inl j =>
      simp only [Sum.elim_inl, Program.appendedWire_input, Circuit.append]
      rw [Fin.append_left]
      rfl
  | inr b =>
      cases b <;> simp only [Sum.elim_inr, Program.appendedWire_input, Circuit.append,
        Bool.false_eq_true, ↓reduceIte] <;> rw [Fin.append_right] <;> rfl

/-- Exact shared-constant substitution code, independent of the routing table. -/
theorem substituteCircuit_code {n m : ℕ} (ρ : Fin m → Fin n ⊕ Bool) :
    (substituteCircuit ρ).code =
      ([(.const false, []), (.const true, [])],
        List.ofFn (fun i => (ρ i).elim Fin.val (fun b => n + if b then 1 else 0))) := by
  apply Prod.ext
  · rfl
  · change List.ofFn _ = List.ofFn _
    congr 1
    funext i
    exact substitute_outputs ρ i

def initOutput (m j : ℕ) : ℕ :=
  if j < m then InputWidth m + if j = 0 then 1 else 0 else j - m

def squareOutput (m j : ℕ) : ℕ :=
  if j < m then if j % 2 = 0 then j / 2 else RegisterWidth m else j

def incrementOutput (m j : ℕ) : ℕ :=
  if j < m then if j = 0 then RegisterWidth m else j - 1 else j

theorem init_route (m : ℕ) (j : Fin (RegisterWidth m)) :
    (initialRoute m j).elim Fin.val (fun b => InputWidth m + if b then 1 else 0) =
      initOutput m j.val := by
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp [initialRoute, initOutput, i.isLt]
  · intro i
    simp only [initialRoute, Fin.addCases_right, Sum.elim_inl, Fin.val_natAdd,
      initOutput, ite_eq_right (show ¬ m + i.val < m by omega), Nat.add_sub_cancel_left]

theorem square_route (m : ℕ) (j : Fin (RegisterWidth m)) :
    (route (squareSource (m := m)) j).elim Fin.val
      (fun b => RegisterWidth m + if b then 1 else 0) = squareOutput m j.val := by
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [route, Fin.addCases_left, squareSource, squareOutput, Fin.val_castAdd,
      ite_eq_left i.isLt]
    split_ifs <;> simp [timeWire]
  · intro i
    simp only [route, Fin.addCases_right, Sum.elim_inl, trackWire, Fin.val_natAdd,
      squareOutput, ite_eq_right (show ¬ m + i.val < m by omega)]

theorem increment_route (m : ℕ) (j : Fin (RegisterWidth m)) :
    (route (incrementSource (m := m)) j).elim Fin.val
      (fun b => RegisterWidth m + if b then 1 else 0) = incrementOutput m j.val := by
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [route, Fin.addCases_left, incrementSource, incrementOutput, Fin.val_castAdd,
      ite_eq_left i.isLt]
    split_ifs <;> simp [timeWire]
  · intro i
    simp only [route, Fin.addCases_right, Sum.elim_inl, trackWire, Fin.val_natAdd,
      incrementOutput, ite_eq_right (show ¬ m + i.val < m by omega)]

def registerCode (output : ℕ → ℕ → ℕ) (m : ℕ) : List (Op × List ℕ) × List ℕ :=
  ([(.const false, []), (.const true, [])], (List.range (RegisterWidth m)).map (output m))

theorem initCircuit_code (m : ℕ) : (initCircuit m).code = registerCode initOutput m := by
  rw [initCircuit, substituteCircuit_code]
  simp only [init_route, registerCode, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map, Function.comp_def]

theorem square_code (m : ℕ) : (square m).code = registerCode squareOutput m := by
  rw [square, substituteCircuit_code]
  simp only [square_route, registerCode, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map, Function.comp_def]

theorem increment_code (m : ℕ) : (increment m).code = registerCode incrementOutput m := by
  rw [increment, substituteCircuit_code]
  simp only [increment_route, registerCode, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map, Function.comp_def]

section Native
variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {m j : α → ℕ}

theorem inputWidth_budget (hm : ComputableInSpace m enc encNat S) :
    ComputableInSpace (fun a => InputWidth (m a)) enc encNat S :=
  budget_natAdd hm (budget_natAdd hm hm)

theorem registerWidth_budget (hm : ComputableInSpace m enc encNat S) :
    ComputableInSpace (fun a => RegisterWidth (m a)) enc encNat S :=
  budget_natAdd hm (inputWidth_budget hm)

theorem initOutput_budget (hm : ComputableInSpace m enc encNat S)
    (hj : ComputableInSpace j enc encNat S) (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => initOutput (m a) (j a)) enc encNat S := by
  have hbit := budget_ite (budget_natEq hj (budget_const 0 hin))
    (budget_const (encB := encNat) 1 hin) (budget_const 0 hin)
  exact (budget_ite (budget_natLt hj hm) (budget_natAdd (inputWidth_budget hm) hbit)
    (budget_natSub hj hm)).of_enc_eq (fun _ => by simp only [initOutput, decide_eq_true_eq])

theorem squareOutput_budget (hm : ComputableInSpace m enc encNat S)
    (hj : ComputableInSpace j enc encNat S) (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => squareOutput (m a) (j a)) enc encNat S := by
  have htwo := budget_const (encB := encNat) 2 hin
  exact (budget_ite (budget_natLt hj hm)
    (budget_ite (budget_natEq (budget_natMod hj htwo) (budget_const 0 hin))
      (budget_natDiv hj htwo) (registerWidth_budget hm)) hj).of_enc_eq
        (fun _ => by simp only [squareOutput, decide_eq_true_eq])

theorem incrementOutput_budget (hm : ComputableInSpace m enc encNat S)
    (hj : ComputableInSpace j enc encNat S) (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => incrementOutput (m a) (j a)) enc encNat S := by
  exact (budget_ite (budget_natLt hj hm)
    (budget_ite (budget_natEq hj (budget_const 0 hin)) (registerWidth_budget hm)
      (budget_natSub hj (budget_const 1 hin))) hj).of_enc_eq
        (fun _ => by simp only [incrementOutput, decide_eq_true_eq])

end Native

private theorem registerCode_logspace (output : ℕ → ℕ → ℕ)
    (hout : ComputableInSpace
      (fun p : CircuitWriter.Input => output p.1.2.1 (p.1.2.2 - 3))
      CircuitWriter.inputEncoding encNat CircuitWriter.budget) :
    ComputableInLogSpace (registerCode output) encUnary encCode := by
  have hin := CircuitWriter.input_budget
  have hgate := budget_ite (budget_natEq CircuitWriter.index_inSpace (budget_const 0 hin))
    (budget_const (encB := encGate) (.const false, []) hin)
    (budget_const (encB := encGate) (.const true, []) hin)
  have h := CircuitWriter.computableInLogSpace_code
    (G := fun _ => 2) (O := RegisterWidth)
    (gate := fun _ i => if i = 0 then (.const false, []) else (.const true, []))
    (output := output)
    (budget_const 2 hin) (registerWidth_budget CircuitWriter.length_inSpace)
    (hgate.of_enc_eq (fun _ => by simp only [decide_eq_true_eq])) hout
    (by fun_prop) (by unfold RegisterWidth InputWidth; fun_prop)
  exact h.congr_fun (fun m => by simp [registerCode, CircuitWriter.code, List.range_succ])

theorem initCircuit_logspace :
    ComputableInLogSpace (fun m => (initCircuit m).code) encUnary encCode := by
  have hin := CircuitWriter.input_budget
  have hj := budget_natSub CircuitWriter.index_inSpace (budget_const 3 hin)
  exact (registerCode_logspace initOutput
    (initOutput_budget CircuitWriter.length_inSpace hj hin)).congr_fun initCircuit_code

theorem square_logspace :
    ComputableInLogSpace (fun m => (square m).code) encUnary encCode := by
  have hin := CircuitWriter.input_budget
  have hj := budget_natSub CircuitWriter.index_inSpace (budget_const 3 hin)
  exact (registerCode_logspace squareOutput
    (squareOutput_budget CircuitWriter.length_inSpace hj hin)).congr_fun square_code

theorem increment_logspace :
    ComputableInLogSpace (fun m => (increment m).code) encUnary encCode := by
  have hin := CircuitWriter.input_budget
  have hj := budget_natSub CircuitWriter.index_inSpace (budget_const 3 hin)
  exact (registerCode_logspace incrementOutput
    (incrementOutput_budget CircuitWriter.length_inSpace hj hin)).congr_fun increment_code

theorem binaryDigits_eq_bits (T : ℕ) : binaryDigits T = T.bits := by
  induction T using Nat.binaryRec' with
  | zero => simp [binaryDigits]
  | bit b n hn ih =>
      have hne := Nat.bit_ne_zero_iff.mpr hn
      rw [binaryDigits]
      split_ifs with hzero
      · exact (hne hzero).elim
      · rw [Nat.bit_mod_two, Nat.bit_div_two, ih, Nat.bits_append_bit n b hn]
        cases b <;> rfl

/-- Print the canonical exponent digits from unary time, including time zero. -/
theorem timeBits_logspace :
    ComputableInLogSpace binaryDigits encUnary encBits :=
  (ComputableInLogSpace.id (encIn := encUnary)).unaryToBinary.congr
    (fun T => by simp only [encBits_apply, binaryDigits_eq_bits, encNat_apply])

theorem succ_logspace : ComputableInLogSpace (fun T : ℕ => T + 1) encUnary encUnary :=
  ComputableInLogSpace.id.unaryAdd (ComputableInLogSpace.const 1)

theorem initCircuit_succ_logspace :
    ComputableInLogSpace (fun T => (initCircuit (T + 1)).code) encUnary encCode :=
  initCircuit_logspace.comp succ_logspace

theorem square_succ_logspace :
    ComputableInLogSpace (fun T => (square (T + 1)).code) encUnary encCode :=
  square_logspace.comp succ_logspace

theorem increment_succ_logspace :
    ComputableInLogSpace (fun T => (increment (T + 1)).code) encUnary encCode :=
  increment_logspace.comp succ_logspace

theorem inputWidth_succ_logspace :
    ComputableInLogSpace (fun T => InputWidth (T + 1)) encUnary encUnary :=
  succ_logspace.unaryAdd (succ_logspace.unaryAdd succ_logspace)

theorem registerWidth_succ_logspace :
    ComputableInLogSpace (fun T => RegisterWidth (T + 1)) encUnary encUnary :=
  succ_logspace.unaryAdd inputWidth_succ_logspace

end PredictionDepth.FrozenPascal.UniformRegisters
