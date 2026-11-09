import PredictionDepth.FrozenPascal.UniformLocal
import PredictionDepth.FrozenPascal.UniformHomogeneous
import PredictionDepth.FrozenPascal.UniformLanguage

/-! A single uniform family realizes the depth bounds selected by the executable
classification, including the time-dependent homogeneous Pascal bound. -/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition StandardComplexity Turing.MultiTapeTM

/-- Select a time-indexed predictor from the fixed guards alone. -/
def classifiedPrediction (stay hop : Gates q 1) (T : ℕ) :
    Gates (RawWidth q (T + 1)) 1 :=
  match classify stay hop with
  | .noHop => noHopPrediction stay T
  | .shift => shiftPrediction q T
  | .varying => uniformGuardedPrediction UniformWeight.basis stay hop T
  | .pascal => uniformHomogeneousPrediction q T

theorem classifiedPrediction_correct (stay hop : Gates q 1) (T : ℕ) (x : Config (Bits q)) :
    (classifiedPrediction stay hop T).eval interpretation (rawSample x (T + 1)) 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
  cases h : classify stay hop <;> simp only [classifiedPrediction, h]
  case noHop =>
    exact noHopPrediction_correct stay hop ((classify_eq_iff stay hop _).mp h) T x
  case shift =>
    obtain ⟨hs, hh⟩ := (classify_eq_iff stay hop _).mp h
    exact shiftPrediction_correct stay hop hs hh T x
  case varying =>
    exact uniformGuardedPrediction_correct UniformWeight.basis stay hop x T
  case pascal =>
    obtain ⟨hs, hh⟩ := (classify_eq_iff stay hop _).mp h
    exact uniformHomogeneousPrediction_correct stay hop hs hh T x

theorem classifiedPrediction_code_logspace (stay hop : Gates q 1) :
    ComputableInLogSpace (fun T => (classifiedPrediction stay hop T).code) encUnary encCode := by
  cases h : classify stay hop <;> simp only [classifiedPrediction, h]
  case noHop => exact noHopPrediction_code_logspace stay
  case shift => exact shiftPrediction_code_logspace q
  case varying => exact uniformGuardedPrediction_code_logspace UniformWeight.basis stay hop
  case pascal => exact uniformHomogeneousPrediction_code_logspace q

/-- A depth bound on the selected uniform family at legal lengths. -/
def classifiedDepthUpper (stay hop : Gates q 1) (T : ℕ) : ℕ :=
  match classify stay hop with
  | .noHop => 1 + stay.depth
  | .shift => 0
  | .varying => 104 * (Nat.clog 2 (T + 3) + 1) + max stay.depth hop.depth
  | .pascal => 3 * T.bitIndices.length

theorem classifiedPrediction_depth (stay hop : Gates q 1) (T : ℕ) :
    (classifiedPrediction stay hop T).depth ≤ classifiedDepthUpper stay hop T := by
  cases h : classify stay hop <;> simp only [classifiedPrediction, classifiedDepthUpper, h]
  case noHop => exact noHopPrediction_depth stay T
  case shift => simp
  case varying => exact uniformGuardedPrediction_depth UniformWeight.basis stay hop T
  case pascal => exact uniformHomogeneousPrediction_depth q T

private theorem classifiedDepthUpper_log_bound (stay hop : Gates q 1) (T : ℕ) :
    classifiedDepthUpper stay hop T ≤
      (208 + max stay.depth hop.depth) + 104 * Nat.clog 2 (T + 2) := by
  cases h : classify stay hop <;> simp only [classifiedDepthUpper, h]
  case noHop =>
    have := le_max_left stay.depth hop.depth
    omega
  case shift => exact Nat.zero_le _
  case varying =>
    have hl : Nat.clog 2 (T + 3) ≤ Nat.clog 2 (T + 2) + 1 := by
      apply Nat.clog_le_of_le_pow
      rw [pow_succ]
      have := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (T + 2)
      omega
    omega
  case pascal =>
    have hp : T.bitIndices.length ≤ Nat.clog 2 (T + 2) := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
      rw [← pascalSupport_card]
      have hcard : (pascalSupport T).card ≤ T + 1 := by
        simpa using Finset.card_le_univ (pascalSupport T)
      exact (hcard.trans (Nat.le_succ _)).trans
        (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (T + 2))
    omega

/-- A per-time depth lower bound shared by all fan-in-two predictors. -/
def classifiedDepthLower (stay hop : Gates q 1) (T : ℕ) : ℕ :=
  match classify stay hop with
  | .noHop | .shift => 0
  | .varying => Nat.clog 2 (T + 1)
  | .pascal => T.bitIndices.length

theorem classifiedPrediction_depth_lower_bound (stay hop : Gates q 1)
    {σ : Signature} (I : Interpretation σ Bool)
    (T : ℕ) (c : Circuit σ (RawWidth q (T + 1)) 1) (hFan : c.FanInAtMost 2)
    (hc : ∀ x : Config (Bits q),
      c.eval I (rawSample x (T + 1)) 0 =
        ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0)) :
    classifiedDepthLower stay hop T ≤ c.depth := by
  cases h : classify stay hop <;> simp only [classifiedDepthLower, h]
  case noHop => exact Nat.zero_le _
  case shift => exact Nat.zero_le _
  case varying =>
    exact varyingGuard_prediction_depth_lower_bound stay hop
      ((classify_eq_iff stay hop _).mp h) I T c hFan hc
  case pascal =>
    obtain ⟨hs, hh⟩ := (classify_eq_iff stay hop _).mp h
    exact homogeneous_prediction_depth_lower_bound stay hop hs hh I T c hFan hc

/-- The circuit family chosen by the classifier is logspace-uniform and has
polynomial size, decides the prediction language at all lengths, and realizes
the branch-specific depth upper bound. The lower bound applies to every
De Morgan family deciding that language. -/
theorem uniform_depth_classification (stay hop : Gates q 1) :
    ∃ (F : BooleanCircuitFamily) (C : ℕ),
      FamilyDecides F (predictionLanguage stay hop) ∧
      LogspaceUniform F ∧ PolynomiallyBounded (fun n => (F n).size) ∧
      (∀ n, (F n).depth ≤ C * (Nat.log 2 n + 1)) ∧
      (∀ T, (F (RawWidth q (T + 1))).depth ≤ classifiedDepthUpper stay hop T) ∧
      ∀ G : BooleanCircuitFamily, FamilyDecides G (predictionLanguage stay hop) →
        ∀ T, classifiedDepthLower stay hop T ≤ (G (RawWidth q (T + 1))).depth := by
  let P := classifiedPrediction stay hop
  let C := 208 + max stay.depth hop.depth
  have hu := UniformGuards.lift_uniform P (classifiedPrediction_code_logspace stay hop)
  refine ⟨UniformGuards.lift P, C + 104 + 1,
    lift_decides_predictionLanguage stay hop P (classifiedPrediction_correct stay hop),
    hu, hu.polynomialSize, ?_, ?_, ?_⟩
  · exact UniformGuards.lift_depth_log_bound P C 104 (fun T =>
      (classifiedPrediction_depth stay hop T).trans (classifiedDepthUpper_log_bound stay hop T))
  · intro T
    rw [UniformGuards.lift_at_time]
    exact classifiedPrediction_depth stay hop T
  · intro G hG T
    exact classifiedPrediction_depth_lower_bound stay hop interpretation T _
      (G _).fanInAtMost_two (predictionLanguage_correct_at_time stay hop G hG T)

/-- The constant-depth classification also holds for the standard uniform
language model, with malformed lengths rejected. -/
theorem predictionLanguage_mem_uniformNC_zero_iff (stay hop : Gates q 1) :
    predictionLanguage stay hop ∈ UniformNCLevel 0 ↔
      classify stay hop = .noHop ∨ classify stay hop = .shift := by
  constructor
  · rintro ⟨F, D, hc, _, hd, _⟩
    have h := (bounded_prediction_depth_iff stay hop).mp
      ⟨D, fun T => F (RawWidth q (T + 1)),
        predictionLanguage_correct_at_time stay hop F hc,
        fun T => by simpa using hd (RawWidth q (T + 1))⟩
    exact h.imp ((classify_eq_iff stay hop .noHop).mpr) ((classify_eq_iff stay hop .shift).mpr)
  · intro h
    let P := classifiedPrediction stay hop
    refine mem_uniformNCLevel_of_uniform (c := 1 + stay.depth)
      (UniformGuards.lift_uniform P (classifiedPrediction_code_logspace stay hop))
      (lift_decides_predictionLanguage stay hop P (classifiedPrediction_correct stay hop)) ?_
    intro n
    by_cases hn : UniformGuards.ValidLength q n
    · have hbound (T : ℕ) : (P T).depth ≤ 1 + stay.depth := by
        apply (classifiedPrediction_depth stay hop T).trans
        rcases h with h | h <;> simp [classifiedDepthUpper, h]
      simpa only [UniformGuards.lift, dite_eq_left hn, UniformGuards.castInputs_depth, pow_zero,
        Nat.mul_one] using hbound (UniformGuards.timeOfLength q n)
    · simp [UniformGuards.lift, hn]

end PredictionDepth.FrozenPascal
