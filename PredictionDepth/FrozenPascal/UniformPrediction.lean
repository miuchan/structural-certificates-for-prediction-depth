import PredictionDepth.FrozenPascal.UniformDecoderCode
import PredictionDepth.FrozenPascal.UniformRegisters
import PredictionDepth.FrozenPascal.GuardRules
import PredictionDepth.FrozenPascal.UniformGuards
import PredictionDepth.Complexity.UniformComposition.Generator

/-! Applying the path criterion with the generated decoder. -/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open StandardComplexity.UniformComposition
open Turing.MultiTapeTM

def uniformWitness (W : WeightBasis) (m T : ℕ) (hT : T < m) :
    RegisterWitness (W := RegisterWidth m) (realization Prod.fst Prod.snd)
      (initial (m := m)) observe (binaryDigits T) where
  register := register m
  initialization := initCircuit m
  square := square m
  multiplySeed := increment m
  observation := UniformDecoder.decoder W m
  initialization_correct := initialize_eval m
  path_correct := valid_path m .identity _
  observation_correct := by
    intro x
    rw [UniformDecoder.decoder_eval]
    exact (witness m T hT).observation_correct x

def uniformPrediction (W : WeightBasis) (T : ℕ) : Gates (InputWidth (T + 1)) 1 :=
  (uniformWitness W (T + 1) T (Nat.lt_succ_self T)).circuit

theorem uniformPrediction_correct (W : WeightBasis) (T : ℕ) (x : Bits (InputWidth (T + 1))) :
    (uniformPrediction W T).eval interpretation x 0 =
      observe ((step Prod.fst Prod.snd)^[T] (initial x)) :=
  (uniformWitness W (T + 1) T (Nat.lt_succ_self T)).circuit_at_time_correct x

theorem uniformPrediction_depth (W : WeightBasis) (T : ℕ) :
    (uniformPrediction W T).depth ≤ (16 + 4 * W.depthFactor) *
      (Nat.clog 2 (T + 3) + 1) := by
  let m := T + 1
  let L := Nat.clog 2 (T + 3) + 1
  have h := predictor_logarithmic_depth (initCircuit m) (square m) (increment m)
    (UniformDecoder.decoder W m) T
  have hi : (initCircuit m).depth ≤ 1 := depth_substituteCircuit_le _
  have hs : (square m).depth ≤ 1 := depth_substituteCircuit_le _
  have hm : (increment m).depth ≤ 1 := depth_substituteCircuit_le _
  have hmax : max (square m).depth (increment m).depth + 1 ≤ 2 :=
    Nat.add_le_add_right (max_le hs hm) 1
  have hstage := Nat.mul_le_mul_left (2 * Nat.clog 2 (T + 1)) hmax
  have ho : (UniformDecoder.decoder W m).depth ≤ (10 + 4 * W.depthFactor) * L :=
    UniformDecoder.decoder_depth W m
  have hlog : Nat.clog 2 (T + 1) + 1 ≤ L := Nat.add_le_add_right
    (Nat.clog_mono_right 2 (show T + 1 ≤ T + 3 by omega)) 1
  change (uniformPrediction W T).depth ≤ _ at h
  change _ ≤ (16 + 4 * W.depthFactor) * L
  simp only [Nat.add_mul] at ho ⊢
  omega

/-- The same path circuit used in the depth proof has an actual generator. -/
theorem uniformPrediction_code_logspace (W : WeightBasis) :
    ComputableInLogSpace (fun T => (uniformPrediction W T).code) encUnary encCode :=
  predictor_code_logspace UniformRegisters.inputWidth_succ_logspace
    UniformRegisters.registerWidth_succ_logspace UniformRegisters.timeBits_logspace
    UniformRegisters.initCircuit_succ_logspace UniformRegisters.square_succ_logspace
    UniformRegisters.increment_succ_logspace (UniformDecoder.decoder_succ_code_logspace W)

def uniformGuardedPrediction (W : WeightBasis) (stay hop : Gates q 1) (T : ℕ) :
    Gates (RawWidth q (T + 1)) 1 :=
  (uniformPrediction W T).comp (preprocess stay hop (T + 1))

theorem uniformGuardedPrediction_correct (W : WeightBasis) (stay hop : Gates q 1)
    (x : Config (Bits q)) (T : ℕ) :
    (uniformGuardedPrediction W stay hop T).eval interpretation (rawSample x (T + 1)) 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
  rw [uniformGuardedPrediction, Circuit.eval_comp, preprocess_eval, uniformPrediction_correct,
    observe, sample_prediction (guard stay) (guard hop) x (Nat.lt_succ_self T)]

theorem uniformGuardedPrediction_depth (W : WeightBasis) (stay hop : Gates q 1) (T : ℕ) :
    (uniformGuardedPrediction W stay hop T).depth ≤
      (16 + 4 * W.depthFactor) * (Nat.clog 2 (T + 3) + 1) + max stay.depth hop.depth :=
  (Circuit.depth_comp_le _ _).trans
    (Nat.add_le_add (uniformPrediction_depth W T) (preprocess_depth stay hop (T + 1)))

theorem uniformGuardedPrediction_eval (W : WeightBasis) (stay hop : Gates q 1) (T : ℕ)
    (x : Bits (RawWidth q (T + 1))) :
    (uniformGuardedPrediction W stay hop T).eval interpretation x 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] (decodeRaw x)).2 0) := by
  simpa only [rawSample_decodeRaw] using
    uniformGuardedPrediction_correct W stay hop (decodeRaw x) T

theorem uniformGuardedPrediction_code_logspace (W : WeightBasis) (stay hop : Gates q 1) :
    ComputableInLogSpace (fun T => (uniformGuardedPrediction W stay hop T).code)
      encUnary encCode :=
  StandardComplexity.CodeLogspace.circuit_comp_logspace (UniformGuards.rawWidth_succ_logspace q)
    (UniformGuards.preprocess_succ_logspace stay hop) (uniformPrediction_code_logspace W)

end PredictionDepth.FrozenPascal
