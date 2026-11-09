import PredictionDepth.FrozenPascal.Classification
import PredictionDepth.FrozenPascal.UniformGuards

/-! The existing constant-depth predictors have native logspace code
generators. The generators preserve the depth and size of the typed circuits
by writing their exact code. -/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM
open StandardComplexity

/-- At time zero wire the origin data bit directly. At positive times,
compose the fixed stay circuit on the origin control word with one AND gate. -/
theorem noHopPrediction_code_logspace (stay : Gates q 1) :
    ComputableInLogSpace (fun T => (noHopPrediction stay T).code) encUnary encCode := by
  have hwidth := UniformGuards.rawWidth_succ_logspace q
  have hdata : ComputableInLogSpace
      (fun T => (wireBit (rawDataWire (q := q) (m := T + 1) 0)).code) encUnary encCode :=
    Code.wire (UniformRegisters.succ_logspace.unaryMulConst q).unaryToBinary (fun _ => rfl)
  have hcontrol : ComputableInLogSpace
      (fun T => (Circuit.wiring signature (controlWire (q := q) (m := T + 1) 0)).code)
      encUnary encCode := by
    apply (ComputableInLogSpace.const (([], List.range q) : CodeLogspace.RawCode)).congr_fun
    intro T
    simp [UniformGuards.controlWiring_code]
  have hguard := CodeLogspace.circuit_comp_logspace hwidth hcontrol
    (ComputableInLogSpace.const stay.code)
  have hpositive := Code.conjoin hwidth hguard hdata
  have hzero := (ComputableInLogSpace.id.unaryEq (ComputableInLogSpace.const 0))
  refine (hzero.ite hdata hpositive).congr_fun ?_
  intro T
  cases T <;> simp [noHopPrediction]

/-- For each time the sole output is a wire from the last data coordinate. -/
theorem shiftPrediction_code_logspace (q : ℕ) :
    ComputableInLogSpace (fun T => (shiftPrediction q T).code) encUnary encCode :=
  Code.wire ((UniformRegisters.succ_logspace.unaryMulConst q).unaryAdd
    ComputableInLogSpace.id).unaryToBinary (fun _ => rfl)

theorem noHopPrediction_uniform (stay : Gates q 1) :
    LogspaceUniform (UniformGuards.lift (noHopPrediction stay)) :=
  UniformGuards.lift_uniform _ (noHopPrediction_code_logspace stay)

theorem shiftPrediction_uniform (q : ℕ) :
    LogspaceUniform (UniformGuards.lift (shiftPrediction q)) :=
  UniformGuards.lift_uniform _ (shiftPrediction_code_logspace q)

end PredictionDepth.FrozenPascal
