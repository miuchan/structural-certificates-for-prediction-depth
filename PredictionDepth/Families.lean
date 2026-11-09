import PredictionDepth.CircuitInterop
import PredictionDepth.ORAutomaton
import Mathlib.Data.ENat.Lattice

/-!
# Prediction families and admissible intrinsic depth

Input length, size coefficient, size exponent, and a family-wide uniformity
policy are fixed before minimization. No arbitrary function is declared
logspace-computable here: `uniform` is an explicit parameter to be instantiated
with a chosen generator model. In particular, total Lean code alone does not
prove logspace uniformity.

The pointwise infimum can choose different families at different times.
`RealizesProfile` instead requires ONE admissible family for the whole depth
profile, which is the appropriate quantifier order for asymptotic claims.
-/
namespace PredictionDepth.Families
open FastComposition

abbrev CircuitFamily (inputLength : ℕ → ℕ) :=
  (T : ℕ) → BinaryCircuit (inputLength T) 1

abbrev PredictionFamily (inputLength : ℕ → ℕ) :=
  (T : ℕ) → BooleanInput (inputLength T) → Bool

structure Policy (inputLength : ℕ → ℕ) where
  uniform : CircuitFamily inputLength → Prop
  sizeCoefficient : ℕ
  sizeExponent : ℕ

structure Admissible {n : ℕ → ℕ} (policy : Policy n) (target : PredictionFamily n)
    (C : CircuitFamily n) : Prop where
  uniform : policy.uniform C
  correct : ∀ T x, (C T).eval x 0 = target T x
  size : ∀ T, (C T).descriptionSize ≤ policy.sizeCoefficient * (n T + 1) ^ policy.sizeExponent

/-- The value is infinity if no admissible family exists. -/
noncomputable def intrinsicDepth {n : ℕ → ℕ} (policy : Policy n)
    (target : PredictionFamily n) (T : ℕ) : ℕ∞ :=
  ⨅ C : {C : CircuitFamily n // Admissible policy target C}, ((C.val T).depth : ℕ∞)

/-- A single family realizes a depth profile under the fixed resource policy. -/
def RealizesProfile {n : ℕ → ℕ} (policy : Policy n) (target : PredictionFamily n)
    (profile : ℕ → ℕ) : Prop :=
  ∃ C, Admissible policy target C ∧ ∀ T, (C T).depth ≤ profile T

theorem intrinsicDepth_le {n : ℕ → ℕ} {policy : Policy n}
    {target : PredictionFamily n} {C : CircuitFamily n}
    (h : Admissible policy target C) (T : ℕ) :
    intrinsicDepth policy target T ≤ ((C T).depth : ℕ∞) := by
  unfold intrinsicDepth
  exact iInf_le _ (⟨C, h⟩ : {D : CircuitFamily n // Admissible policy target D})

theorem le_intrinsicDepth {n : ℕ → ℕ} {policy : Policy n}
    {target : PredictionFamily n} (T lower : ℕ)
    (h : ∀ C, Admissible policy target C → lower ≤ (C T).depth) :
    (lower : ℕ∞) ≤ intrinsicDepth policy target T := by
  apply le_iInf
  intro C
  exact_mod_cast h C.val C.property

theorem intrinsicDepth_eq_top_iff {n : ℕ → ℕ} (policy : Policy n)
    (target : PredictionFamily n) (T : ℕ) :
    intrinsicDepth policy target T = ⊤ ↔ ¬ ∃ C, Admissible policy target C := by
  rw [intrinsicDepth, ENat.iInf_natCast_eq_top]
  constructor
  · intro h ⟨C, hC⟩
    exact h.false ⟨C, hC⟩
  · intro h
    exact ⟨fun C => h ⟨C.val, C.property⟩⟩

theorem RealizesProfile.intrinsicDepth_le {n : ℕ → ℕ} {policy : Policy n}
    {target : PredictionFamily n} {profile : ℕ → ℕ}
    (h : RealizesProfile policy target profile) (T : ℕ) :
    intrinsicDepth policy target T ≤ (profile T : ℕ∞) := by
  obtain ⟨C, hC, hdepth⟩ := h
  exact (Families.intrinsicDepth_le hC T).trans (by exact_mod_cast hdepth T)

/-- Transfer Theorem C to the compositional Boolean DAG syntax. -/
theorem circuit_dependency_lower_bound {n : ℕ} (c : BinaryCircuit n 1)
    (f : BooleanInput n → Bool) (hc : ∀ x, c.eval x 0 = f x) :
    Nat.clog 2 (essentialInputs f).card ≤ c.depth := by
  have he : (c.unfoldOutput 0).eval = f := by
    funext x
    exact (c.unfoldOutput_eval 0 x).trans (hc x)
  simpa only [he] using (c.unfoldOutput 0).essential_depth_lower_bound (by decide : 1 < 2)

theorem intrinsicDepth_dependency_lower_bound {n : ℕ → ℕ} (policy : Policy n)
    (target : PredictionFamily n) (T : ℕ) :
    (Nat.clog 2 (essentialInputs (target T)).card : ℕ∞) ≤ intrinsicDepth policy target T := by
  apply le_intrinsicDepth
  intro C hC
  exact circuit_dependency_lower_bound (C T) (target T) (hC.correct T)

/-- The explicit balanced-tree predictor, as one family. -/
def orFamily : CircuitFamily (fun T => 2 * T + 1) :=
  fun T => (ORAutomaton.optimalCircuit T).toBinary

/-- Conservative linear description budget, fixed before taking the infimum. -/
def orPolicy (uniform : CircuitFamily (fun T => 2 * T + 1) → Prop) :
    Policy (fun T => 2 * T + 1) := ⟨uniform, 12, 1⟩

theorem orFamily_correct (T : ℕ) (x : BooleanInput (2 * T + 1)) :
    (orFamily T).eval x 0 = ORAutomaton.prediction T x :=
  ((ORAutomaton.optimalCircuit T).toBinary_eval x).trans
    (congrFun (ORAutomaton.optimalCircuit_correct T) x)

theorem orFamily_admissible (uniform : CircuitFamily (fun T => 2 * T + 1) → Prop)
    (hu : uniform orFamily) :
    Admissible (orPolicy uniform) ORAutomaton.prediction orFamily := by
  refine ⟨hu, orFamily_correct, ?_⟩
  intro T
  have hs := ORAutomaton.optimalCircuit_size T
  simp only [orFamily, BoundedCircuit.toBinary_descriptionSize, orPolicy, pow_one]
  omega

theorem orFamily_realizes_logarithmic_profile
    (uniform : CircuitFamily (fun T => 2 * T + 1) → Prop) (hu : uniform orFamily) :
    RealizesProfile (orPolicy uniform) ORAutomaton.prediction
      (fun T => Nat.clog 2 (2 * T + 1)) :=
  ⟨orFamily, orFamily_admissible uniform hu, fun T => (ORAutomaton.optimalCircuit T).toBinary_depth⟩

/-- Under ANY uniformity policy accepting the explicit OR family, the fixed
linear-size model has the exact claimed intrinsic depth. -/
theorem or_intrinsicDepth (uniform : CircuitFamily (fun T => 2 * T + 1) → Prop)
    (hu : uniform orFamily) (T : ℕ) :
    intrinsicDepth (orPolicy uniform) ORAutomaton.prediction T =
      (Nat.clog 2 (2 * T + 1) : ℕ∞) := by
  apply le_antisymm
  · exact (orFamily_realizes_logarithmic_profile uniform hu).intrinsicDepth_le T
  · simpa only [ORAutomaton.prediction_eq_boolOr, boolOr_essential_count] using
      intrinsicDepth_dependency_lower_bound (orPolicy uniform) ORAutomaton.prediction T

end PredictionDepth.Families
