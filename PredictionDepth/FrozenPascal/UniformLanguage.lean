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

/-- Correctness on sampled configurations lifts to a total language decider,
with invalid lengths rejected by the standard length wrapper. -/
theorem lift_decides_predictionLanguage (stay hop : Gates q 1)
    (P : ∀ T, Gates (RawWidth q (T + 1)) 1)
    (hcorrect : ∀ (T : ℕ) (x : Config (FastComposition.Bits q)),
      (P T).eval interpretation (rawSample x (T + 1)) 0 =
        ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0)) :
    FamilyDecides (UniformGuards.lift P) (predictionLanguage stay hop) := by
  intro x
  have he (T : ℕ) (h : x.length = RawWidth q (T + 1)) :
      evaluateFamily (UniformGuards.lift P) x =
        ofBoolRing (((step (guard stay) (guard hop))^[T]
          (decodeRaw (BitString.ofList (RawWidth q (T + 1)) x))).2 0) := by
    rw [evaluateFamily, h, UniformGuards.lift_at_time]
    simpa only [rawSample_decodeRaw] using
      hcorrect T (decodeRaw (BitString.ofList (RawWidth q (T + 1)) x))
  symm
  constructor
  · intro hx
    by_cases h : UniformGuards.ValidLength q x.length
    · let T := UniformGuards.timeOfLength q x.length
      have hw : x.length = RawWidth q (T + 1) := (UniformGuards.rawWidth_timeOfLength h).symm
      exact ⟨T, hw, (he T hw).symm.trans hx⟩
    · have hbad := UniformGuards.lift_invalid_eval P h
        (BitString.ofList x.length x)
      change evaluateFamily (UniformGuards.lift P) x = false at hbad
      rw [hbad] at hx
      cases hx
  · rintro ⟨T, h, hx⟩
    exact (he T h).trans hx

/-- Every decider for the word language predicts the sampled configuration
at the circuit indexed by its window length. -/
theorem predictionLanguage_correct_at_time (stay hop : Gates q 1)
    (F : BooleanCircuitFamily) (hF : FamilyDecides F (predictionLanguage stay hop))
    (T : ℕ) (x : Config (FastComposition.Bits q)) :
    (F (RawWidth q (T + 1))).eval interpretation (rawSample x (T + 1)) 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
  let word := List.ofFn (rawSample x (T + 1))
  have hlen : word.length = RawWidth q (T + 1) := List.length_ofFn
  have hwindow :
      ofBoolRing (((step (guard stay) (guard hop))^[T]
        (decodeRaw (rawSample x (T + 1)))).2 0) =
        ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
    rw [← guardedPrediction_correct stay hop (decodeRaw (rawSample x (T + 1))) T,
      rawSample_decodeRaw, guardedPrediction_correct stay hop x T]
  have hword : word ∈ predictionLanguage stay hop ↔
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) = true := by
    constructor
    · rintro ⟨U, hU, hy⟩
      have htime := congrArg (UniformGuards.timeOfLength q) (hU.symm.trans hlen)
      simp only [UniformGuards.timeOfLength_rawWidth] at htime
      subst U
      simpa only [word, BitString.ofList_ofFn, hwindow] using hy
    · intro hx
      exact ⟨T, hlen, by simpa only [word, BitString.ofList_ofFn, hwindow] using hx⟩
  have heval : evaluateFamily F word =
      (F (RawWidth q (T + 1))).eval interpretation (rawSample x (T + 1)) 0 := by
    rw [evaluateFamily, hlen]
    simp only [word, BitString.ofList_ofFn]
  rw [← heval]
  exact Bool.eq_iff_iff.mpr ((hF word).symm.trans hword)

theorem predictionLanguage_eq_liftLanguage (W : WeightBasis) (stay hop : Gates q 1) :
    UniformGuards.liftLanguage (uniformGuardedPrediction W stay hop) =
      predictionLanguage stay hop := by
  ext x
  exact (lift_decides_predictionLanguage stay hop _ (fun T y =>
    uniformGuardedPrediction_correct W stay hop y T) x).symm

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
