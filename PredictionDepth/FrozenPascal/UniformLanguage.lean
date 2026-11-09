import PredictionDepth.FrozenPascal.UniformPrediction
import PredictionDepth.FrozenPascal.UniformWeight

/-! The prediction problem as a standard language indexed by raw input length. -/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity

/-- A positive whole number of cells encodes its right-hand cone. A window
of m cells asks for time m-1. The blocks of controls and data are those
of `rawSample`. -/
def predictionLanguage (stay hop : Gates q 1) : Set (List Bool) :=
  {x | ∃ T, x.length = RawWidth q (T + 1) ∧
    ofBoolRing (((step (guard stay) (guard hop))^[T]
      (decodeRaw (BitString.ofList (RawWidth q (T + 1)) x))).2 0) = true}

theorem predictionLanguage_eq_liftLanguage (W : WeightBasis) (stay hop : Gates q 1) :
    UniformGuards.liftLanguage (uniformGuardedPrediction W stay hop) =
      predictionLanguage stay hop := by
  ext x
  change evaluateFamily (UniformGuards.lift (uniformGuardedPrediction W stay hop)) x = true ↔ _
  have he (T : ℕ) (h : x.length = RawWidth q (T + 1)) :
      evaluateFamily (UniformGuards.lift (uniformGuardedPrediction W stay hop)) x =
        ofBoolRing (((step (guard stay) (guard hop))^[T]
          (decodeRaw (BitString.ofList (RawWidth q (T + 1)) x))).2 0) := by
    rw [evaluateFamily, h, UniformGuards.lift_at_time, uniformGuardedPrediction_eval]
  constructor
  · intro hx
    by_cases h : UniformGuards.ValidLength q x.length
    · let T := UniformGuards.timeOfLength q x.length
      have hw : x.length = RawWidth q (T + 1) := (UniformGuards.rawWidth_timeOfLength h).symm
      exact ⟨T, hw, (he T hw).symm.trans hx⟩
    · have hbad := UniformGuards.lift_invalid_eval (uniformGuardedPrediction W stay hop) h
        (BitString.ofList x.length x)
      change evaluateFamily (UniformGuards.lift (uniformGuardedPrediction W stay hop)) x = false at hbad
      rw [hbad] at hx
      cases hx
  · rintro ⟨T, h, hx⟩
    exact (he T h).trans hx

private theorem clog_succ_bound (r : ℕ) (hr : 1 ≤ r) : Nat.clog 2 (r + 1) ≤ Nat.clog 2 r + 1 := by
  apply Nat.clog_le_of_le_pow
  rw [pow_succ]
  have hp := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) r
  omega

/-- For every fixed pair of control guards, the word language belongs to
logspace-uniform NC¹. The circuit is obtained by the path witness compiler. -/
theorem predictionLanguage_mem_uniformNC_one_of_basis (W : WeightBasis) (stay hop : Gates q 1) :
    predictionLanguage stay hop ∈ UniformNCLevel 1 := by
  rw [← predictionLanguage_eq_liftLanguage W stay hop]
  let K := 16 + 4 * W.depthFactor
  apply UniformGuards.lift_mem_uniformNC_one (uniformGuardedPrediction W stay hop)
    (uniformGuardedPrediction_code_logspace W stay hop) (2 * K + max stay.depth hop.depth) K
  intro T
  have ht : Nat.clog 2 (T + 3) + 1 ≤ Nat.clog 2 (T + 2) + 2 := by
    have h := clog_succ_bound (T + 2) (by omega)
    simpa only [Nat.add_assoc] using Nat.add_le_add_right h 1
  have hm := Nat.mul_le_mul_left K ht
  have hu := uniformGuardedPrediction_depth W stay hop T
  change _ ≤ K * (Nat.clog 2 (T + 3) + 1) + max stay.depth hop.depth at hu
  calc
    (uniformGuardedPrediction W stay hop T).depth ≤
        K * (Nat.clog 2 (T + 3) + 1) + max stay.depth hop.depth := hu
    _ ≤ K * (Nat.clog 2 (T + 2) + 2) + max stay.depth hop.depth :=
      Nat.add_le_add_right hm _
    _ = (2 * K + max stay.depth hop.depth) + K * Nat.clog 2 (T + 2) := by ring


/-- The fixed-guard prediction language has logspace-uniform NC¹ circuits. -/
theorem predictionLanguage_mem_uniformNC_one (stay hop : Gates q 1) :
    predictionLanguage stay hop ∈ UniformNCLevel 1 :=
  predictionLanguage_mem_uniformNC_one_of_basis UniformWeight.basis stay hop

end PredictionDepth.FrozenPascal
