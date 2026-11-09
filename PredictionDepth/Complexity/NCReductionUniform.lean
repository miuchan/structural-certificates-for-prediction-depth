import PredictionDepth.Complexity.NCReductionConstruction
import PredictionDepth.Complexity.CodeLogspaceFamilies

/-!
# Actual logspace generation of the reduction-closure circuit

Prefix hardwiring, variable-size parallel banks, sequential composition, and
the final OR are all performed by verified logspace code transformations.
The reduction's output length may depend on its complete input, not just on
the input length; every candidate length up to the supplied unary clock is
generated uniformly.
-/

namespace PredictionDepth.StandardComplexity
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM

/-- Extract the raw gate/output code from a full uniform circuit generator. -/
theorem LogspaceUniform.code_logspace {F : BooleanCircuitFamily} (hF : LogspaceUniform F) :
    ComputableInLogSpace (fun n => (F n).code) encUnary encCode := by
  have hp : ComputableInLogSpace (fun n => (n, (F n).code)) encUnary
      (encPair encUnary encCode) := ComputableInLogSpace.congr hF (fun _ => rfl)
  exact hp.snd'

namespace ReductionConstruction

variable {α : Type} {enc : α ↪ List Bool}

theorem queryPrefix_logspace {j : α → ℕ}
    (hj : ComputableInLogSpace j enc encUnary) :
    ComputableInLogSpace (fun a => queryPrefix (j a)) enc encBits :=
  (ComputableInLogSpace.of_frame (encIn := encUnary) (encOut := encBits)
    (f := queryPrefix) (fun _ => rfl)).comp hj

theorem prefixed_code_logspace {F : BooleanCircuitFamily} (hF : LogspaceUniform F)
    {n j : α → ℕ} (hn : ComputableInLogSpace n enc encUnary)
    (hj : ComputableInLogSpace j enc encUnary) :
    ComputableInLogSpace (fun a => (prefixed F (n a) (j a)).code) enc encCode := by
  have hr := queryPrefix_logspace hj
  have hl := (CodeLogspace.bitsLength.comp hr).unaryAdd hn
  have hc := hF.code_logspace.comp hl
  exact CodeLogspace.circuit_prefix_logspace hr hn hc

theorem bitBank_code_logspace {F : BooleanCircuitFamily} (hF : LogspaceUniform F)
    {n m : α → ℕ} (hn : ComputableInLogSpace n enc encUnary)
    (hm : ComputableInLogSpace m enc encUnary) :
    ComputableInLogSpace (fun a => (bitBank F (n a) (m a)).code) enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hpre := prefixed_code_logspace hF (hn.comp hp) hi
  have htest := hi.unaryLt (hm.comp hp)
  apply CodeLogspaceFamilies.circuit_pi_of_indexed_logspace hn hm
  exact (htest.ite hpre (ComputableInLogSpace.const ([], []))).congr_fun fun p => by
    simp only [decide_eq_true_eq, Function.comp_apply]
    split_ifs <;> rfl

theorem branch_code_logspace {target bits lengthTest : BooleanCircuitFamily}
    (htarget : LogspaceUniform target) (hbits : LogspaceUniform bits)
    (hlength : LogspaceUniform lengthTest) {n m : α → ℕ}
    (hn : ComputableInLogSpace n enc encUnary)
    (hm : ComputableInLogSpace m enc encUnary) :
    ComputableInLogSpace (fun a => (branch target bits lengthTest (n a) (m a)).code)
      enc encCode := by
  have hbank := bitBank_code_logspace hbits hn hm
  have hvalue := CodeLogspace.circuit_comp_logspace hn hbank (htarget.code_logspace.comp hm)
  have hlengthTest := prefixed_code_logspace hlength hn hm
  have hpair := CodeLogspace.circuit_append_logspace hn hvalue hlengthTest
  have hand : ComputableInLogSpace
      (fun _ : α => (Circuit.oneGate (σ := signature) .and (id : Fin 2 → Fin 2)).code)
      enc encCode := ComputableInLogSpace.const _
  exact CodeLogspace.circuit_comp_logspace hn hpair hand

/-- The complete length-selection circuit has a genuine finite-machine
logspace generator. No equality of output lengths on same-length inputs is
required. -/
theorem family_uniform {target bits lengthTest : BooleanCircuitFamily} {bound : ℕ → ℕ}
    (htarget : LogspaceUniform target) (hbits : LogspaceUniform bits)
    (hlength : LogspaceUniform lengthTest)
    (hbound : ComputableInLogSpace bound encUnary encUnary) :
    LogspaceUniform (family target bits lengthTest bound) := by
  have hn : ComputableInLogSpace (fun n : ℕ => n) encUnary encUnary := ComputableInLogSpace.id
  have hm := hbound.unaryAdd (ComputableInLogSpace.const 1)
  have hp := ComputableInLogSpace.fst encUnary encUnary
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have hbranch := branch_code_logspace htarget hbits hlength hp hi
  have htest := hi.unaryLt (hm.comp hp)
  have hentry := htest.ite hbranch (ComputableInLogSpace.const ([], []))
  have hbank : ComputableInLogSpace
      (fun n => (Circuit.pi fun m : Fin (bound n + 1) => branch target bits lengthTest n m.val).code)
      encUnary encCode := by
    apply CodeLogspaceFamilies.circuit_pi_of_indexed_logspace hn hm
    exact hentry.congr_fun fun p => by
      simp only [decide_eq_true_eq, Function.comp_apply]
      split_ifs <;> rfl
  have hor := UniformOR.family_code_logspace.comp hm
  have hfamily := CodeLogspace.circuit_comp_logspace hn hbank hor
  exact (hn.pair hfamily).congr (fun _ => rfl)

end ReductionConstruction
end PredictionDepth.StandardComplexity
