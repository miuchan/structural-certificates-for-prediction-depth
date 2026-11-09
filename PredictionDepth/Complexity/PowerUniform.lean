import PredictionDepth.Complexity.PowerArithmetic
import PredictionDepth.Complexity.StandardPowerLayout
import PredictionDepth.Complexity.CircuitWriter
import PredictionDepth.Complexity.ConfigurationAcceptance

/-! Native logarithmic-workspace serialization of regular matrix powering. -/

namespace PredictionDepth.StandardComplexity.StandardPower
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInSpace

variable {α : Type} {enc : α ↪ List Bool} {budget : α → ℕ}
  {N stage q start : α → ℕ}

private theorem binaryGate_budget (op : Op) {a b : α → ℕ}
    (ha : ComputableInSpace a enc encNat budget)
    (hb : ComputableInSpace b enc encNat budget)
    (hin : (fun x => (enc x).length) ≼ budget) :
    ComputableInSpace (fun x => (op, [a x, b x])) enc encGate budget :=
  budget_prod (budget_const op hin) (budget_cons ha (budget_cons hb (budget_const [] hin)))

theorem matrixWire_budget (hN : ComputableInSpace N enc encNat budget)
    (hs : ComputableInSpace stage enc encNat budget)
    (hq : ComputableInSpace q enc encNat budget)
    (hin : (fun x => (enc x).length) ≼ budget) :
    ComputableInSpace (fun x => matrixWire (N x) (stage x) (q x)) enc encNat budget := by
  have hbase := budget_natAdd (budget_natMul hN hN)
    (budget_natMul (budget_natSub hs (budget_const 1 hin)) (layerWidth_budget hN hin))
  exact (budget_ite (budget_natEq hs (budget_const 0 hin)) hq
    (budget_natAdd hbase (budget_natMul hq (width_budget hN hin)))).of_enc_eq
      (fun x => by simp only [matrixWire, decide_eq_true_eq])

theorem productGateCode_budget (hN : ComputableInSpace N enc encNat budget)
    (hs : ComputableInSpace stage enc encNat budget)
    (hq : ComputableInSpace q enc encNat budget)
    (hin : (fun x => (enc x).length) ≼ budget) :
    ComputableInSpace (fun x => productGateCode (N x) (stage x) (q x)) enc encGate budget := by
  have hP := width_budget hN hin
  have he := budget_natDiv hq hP
  have hk := budget_natMod hq hP
  have ha := budget_natAdd (budget_natMul (budget_natDiv he hN) hN) hk
  have hb := budget_natAdd (budget_natMul hk hN) (budget_natMod he hN)
  exact (budget_ite (budget_natLt hk hN)
    (binaryGate_budget .and (matrixWire_budget hN hs ha hin) (matrixWire_budget hN hs hb hin) hin)
    (budget_const (.const false, []) hin)).of_enc_eq
      (fun x => by simp only [productGateCode, decide_eq_true_eq])

theorem mergeGateCode_budget (hN : ComputableInSpace N enc encNat budget)
    (hs : ComputableInSpace stage enc encNat budget)
    (hq : ComputableInSpace q enc encNat budget)
    (hin : (fun x => (enc x).length) ≼ budget) :
    ComputableInSpace (fun x => mergeGateCode (N x) (stage x) (q x)) enc encGate budget := by
  have hP := width_budget hN hin
  have he := budget_natDiv hq hP
  have hk := budget_natMod hq hP
  have hbase := budget_natAdd
    (budget_natAdd (budget_natMul hN hN)
      (budget_natMul (budget_natSub hs (budget_const 1 hin)) (layerWidth_budget hN hin)))
    (budget_natMul he hP)
  have htwok := budget_natMul (budget_const 2 hin) hk
  have htwok' := budget_natAdd htwok (budget_const 1 hin)
  exact (budget_ite (budget_natLt htwok' hP)
    (binaryGate_budget .or (budget_natAdd hbase htwok)
      (budget_natAdd (budget_natAdd hbase htwok) (budget_const 1 hin)) hin)
    (budget_const (.const false, []) hin)).of_enc_eq
      (fun x => by simp only [mergeGateCode, decide_eq_true_eq])

theorem powerGate_budget (hN : ComputableInSpace N enc encNat budget)
    (hq : ComputableInSpace q enc encNat budget)
    (hin : (fun x => (enc x).length) ≼ budget) :
    ComputableInSpace (fun x => powerGate (N x) (q x)) enc encGate budget := by
  have hW := layerWidth_budget hN hin
  have hs := budget_natDiv hq hW
  have hl := budget_natMod hq hW
  exact (budget_ite
    (budget_natEq (budget_natMod hs (blockDepth_budget hN hin)) (budget_const 0 hin))
    (productGateCode_budget hN hs hl hin) (mergeGateCode_budget hN hs hl hin)).of_enc_eq
      (fun x => by simp only [powerGate, stageCount, decide_eq_true_eq])

theorem powerOutput_budget {rounds : α → ℕ}
    (hN : ComputableInSpace N enc encNat budget)
    (hr : ComputableInSpace rounds enc encNat budget)
    (hq : ComputableInSpace q enc encNat budget)
    (hin : (fun x => (enc x).length) ≼ budget) :
    ComputableInSpace (fun x => powerOutput (N x) (rounds x) (q x)) enc encNat budget :=
  matrixWire_budget hN (budget_natMul hr (blockDepth_budget hN hin)) hq hin

theorem acceptingGateCode_budget {accept : α → ℕ → Bool}
    (hN : ComputableInSpace N enc encNat budget)
    (hstart : ComputableInSpace start enc encNat budget)
    (hs : ComputableInSpace stage enc encNat budget)
    (hq : ComputableInSpace q enc encNat budget)
    (ha : ComputableInSpace (fun x => accept x (q x % width (N x))) enc encBool budget)
    (hin : (fun x => (enc x).length) ≼ budget) :
    ComputableInSpace (fun x => acceptingGateCode (N x) (start x) (accept x) (stage x) (q x))
      enc encGate budget := by
  have hk := budget_natMod hq (width_budget hN hin)
  have hw := matrixWire_budget hN hs (budget_natAdd (budget_natMul hstart hN) hk) hin
  exact (budget_ite (budget_natLt hk hN)
    (budget_ite ha (binaryGate_budget .and hw hw hin) (budget_const (.const false, []) hin))
    (budget_const (.const false, []) hin)).of_enc_eq
      (fun x => by simp only [acceptingGateCode, decide_eq_true_eq])

theorem deciderGate_budget {accept : α → ℕ → Bool}
    (hN : ComputableInSpace N enc encNat budget)
    (hstart : ComputableInSpace start enc encNat budget)
    (hq : ComputableInSpace q enc encNat budget)
    (ha : ComputableInSpace
      (fun x => accept x ((q x % layerWidth (N x)) % width (N x))) enc encBool budget)
    (hin : (fun x => (enc x).length) ≼ budget) :
    ComputableInSpace (fun x => deciderGate (N x) (start x) (accept x) (q x))
      enc encGate budget := by
  have hW := layerWidth_budget hN hin
  have hs := budget_natDiv hq hW
  have hl := budget_natMod hq hW
  have hd := blockDepth_budget hN hin
  exact (budget_ite (budget_natLt hs (budget_natMul (size_budget hN) hd))
    (powerGate_budget hN hq hin)
    (budget_ite (budget_natEq (budget_natMod hs hd) (budget_const 0 hin))
      (acceptingGateCode_budget hN hstart hs hl ha hin)
      (mergeGateCode_budget hN hs hl hin))).of_enc_eq
        (fun x => by simp only [deciderGate, stageCount, decide_eq_true_eq])

theorem deciderOutput_budget (hN : ComputableInSpace N enc encNat budget)
    (hstart : ComputableInSpace start enc encNat budget)
    (hin : (fun x => (enc x).length) ≼ budget) :
    ComputableInSpace (fun x => deciderOutput (N x) (start x)) enc encNat budget := by
  exact budget_natAdd
    (budget_natAdd (budget_natMul hN hN)
      (budget_natMul (budget_natSub (budget_natPow (blockDepth_budget hN hin) hin 2)
        (budget_const 1 hin)) (layerWidth_budget hN hin)))
    (budget_natMul (budget_natAdd (budget_natMul hstart hN) hstart) (width_budget hN hin))

/-- Streaming the complete regular decider code from verified local arithmetic.
The accepted-vertex flag is queried only at the gate's binary leaf index. -/
theorem deciderCode_logspace {N start : ℕ → ℕ} {accept : ℕ → ℕ → Bool}
    (hN : ComputableInSpace (fun p : CircuitWriter.Input => N p.1.2.1)
      CircuitWriter.inputEncoding encNat CircuitWriter.budget)
    (hs : ComputableInSpace (fun p : CircuitWriter.Input => start p.1.2.1)
      CircuitWriter.inputEncoding encNat CircuitWriter.budget)
    (ha : ComputableInSpace (fun p : CircuitWriter.Input =>
      accept p.1.2.1 ((p.1.2.2 % layerWidth (N p.1.2.1)) % width (N p.1.2.1)))
      CircuitWriter.inputEncoding encBool CircuitWriter.budget)
    (hpoly : PolynomiallyBounded N) :
    ComputableInLogSpace (fun n => deciderCode (N n) (start n) (accept n)) encUnary encCode := by
  have h := CircuitWriter.computableInLogSpace_code
    (G := fun n => (stageCount (N n)) ^ 2 * layerWidth (N n)) (O := fun _ => 1)
    (gate := fun n => deciderGate (N n) (start n) (accept n))
    (output := fun n _ => deciderOutput (N n) (start n))
    (deciderGateCount_budget hN CircuitWriter.input_budget)
    (budget_const 1 CircuitWriter.input_budget)
    (deciderGate_budget hN hs CircuitWriter.index_inSpace ha CircuitWriter.input_budget)
    (deciderOutput_budget hN hs CircuitWriter.input_budget)
    (polynomiallyBounded_deciderGateCount hpoly) (by fun_prop)
  exact h.congr_fun (fun n => by simp [CircuitWriter.code, deciderCode])

open Turing.MultiTapeNTM ConfigurationGraph ConfigurationAcceptance

/-- The concrete configuration-graph decider's raw code, before feeding the
adjacency circuit. Both its source and its accepting flags come from the
source machine's finite transition table. -/
noncomputable def graphDeciderCode {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) : List (Op × List ℕ) × List ℕ :=
  deciderCode (vertexCount k State c n) (source tm c n).val
    (fun v => bad (k := k) (State := State) (graphRadix State c n) n v)

theorem graphDeciderCode_logspace {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeNTM k Bool State) (c : ℕ) :
    ComputableInLogSpace (graphDeciderCode tm c) encUnary encCode := by
  have hn := CircuitWriter.length_inSpace
  have hin := CircuitWriter.input_budget
  have hB := budget_natPow (budget_natAdd hn (budget_const 2 hin)) hin (radixExponent State c)
  have hN := vertexBound_budget (k := k) hB hin
  change ComputableInSpace (fun p : CircuitWriter.Input => vertexCount k State c p.1.2.1)
    CircuitWriter.inputEncoding encNat CircuitWriter.budget at hN
  have hs := source_budget tm c hn hin
  have hleaf := budget_natMod
    (budget_natMod CircuitWriter.index_inSpace (layerWidth_budget hN hin)) (width_budget hN hin)
  have ha := acceptsVertex_budget (k := k) (State := State) c hn hleaf hin
  exact deciderCode_logspace hN hs ha (vertexCount_polynomial c)

end PredictionDepth.StandardComplexity.StandardPower
