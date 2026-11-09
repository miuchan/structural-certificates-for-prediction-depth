import PredictionDepth.Dynamics
import PredictionDepth.Circuit

/-! The radius-one OR cellular automaton on the infinite integer lattice. -/
namespace PredictionDepth.ORAutomaton

abbrev Config := ℤ → Bool

def step (x : Config) (i : ℤ) : Bool := (x (i - 1) || x i) || x (i + 1)

def evolve : ℕ → Config → Config
  | 0, x => x
  | t + 1, x => step (evolve t x)

theorem evolve_eq_iterate (t : ℕ) (x : Config) : evolve t x = (step^[t]) x := by
  induction t with
  | zero => rfl
  | succ t ih => simp [evolve, Function.iterate_succ_apply', ih]

/-- Exact light-cone semantics, including time zero. -/
theorem evolve_true_iff (t : ℕ) (x : Config) (i : ℤ) :
    evolve t x i = true ↔
      ∃ j : ℤ, i - (t : ℤ) ≤ j ∧ j ≤ i + (t : ℤ) ∧ x j = true := by
  induction t generalizing i with
  | zero =>
    simp only [evolve, Nat.cast_zero, sub_zero, add_zero]
    constructor
    · intro h; exact ⟨i, le_rfl, le_rfl, h⟩
    · rintro ⟨j, h₁, h₂, h⟩
      have : j = i := by omega
      simpa [this] using h
  | succ t ih =>
    simp only [evolve, step, Bool.or_eq_true, ih]
    constructor
    · rintro ((⟨j, h₁, h₂, h⟩ | ⟨j, h₁, h₂, h⟩) | ⟨j, h₁, h₂, h⟩)
      all_goals exact ⟨j, by omega, by omega, h⟩
    · rintro ⟨j, h₁, h₂, h⟩
      by_cases hl : j < i - (t : ℤ)
      · exact Or.inl (Or.inl ⟨j, by omega, by omega, h⟩)
      · by_cases hr : i + (t : ℤ) < j
        · exact Or.inr ⟨j, by omega, by omega, h⟩
        · exact Or.inl (Or.inr ⟨j, by omega, by omega, h⟩)

/-- The specified finite input has exactly `2*T+1` bits. Outside it we choose false. -/
def embed (T : ℕ) (x : Fin (2 * T + 1) → Bool) (j : ℤ) : Bool :=
  if h : -(T : ℤ) ≤ j ∧ j ≤ (T : ℤ) then
    x ⟨(j + T).toNat, by omega⟩
  else false

def prediction (T : ℕ) (x : Fin (2 * T + 1) → Bool) : Bool :=
  evolve T (embed T x) 0

theorem prediction_true_iff (T : ℕ) (x : Fin (2 * T + 1) → Bool) :
    prediction T x = true ↔ ∃ i, x i = true := by
  rw [prediction, evolve_true_iff]
  simp only [zero_sub, zero_add]
  constructor
  · rintro ⟨j, hj₁, hj₂, hj⟩
    simp only [embed, hj₁, hj₂, and_self, ↓reduceDIte] at hj
    exact ⟨_, hj⟩
  · rintro ⟨i, hi⟩
    have hj₁ : -(T : ℤ) ≤ (i.val : ℤ) - T := by omega
    have hj₂ : (i.val : ℤ) - T ≤ (T : ℤ) := by omega
    refine ⟨(i.val : ℤ) - T, hj₁, hj₂, ?_⟩
    simpa only [embed, hj₁, hj₂, and_self, ↓reduceDIte,
      sub_add_cancel, Int.toNat_natCast] using hi

/-- Outside-cone boundary values do not affect the answer. -/
theorem prediction_independent_of_extension (T : ℕ) (x y : Config)
    (h : ∀ j, -(T : ℤ) ≤ j → j ≤ (T : ℤ) → x j = y j) :
    evolve T x 0 = evolve T y 0 := by
  apply Bool.eq_iff_iff.mpr
  simp only [evolve_true_iff, zero_sub, zero_add]
  constructor <;> rintro ⟨j, hj₁, hj₂, hj⟩
  · exact ⟨j, hj₁, hj₂, (h j hj₁ hj₂) ▸ hj⟩
  · exact ⟨j, hj₁, hj₂, (h j hj₁ hj₂).symm ▸ hj⟩

theorem prediction_eq_boolOr (T : ℕ) : prediction T = boolOr (2 * T + 1) := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [prediction_true_iff, boolOr, decide_eq_true_eq]

/-- A linear-size circuit attaining the lower bound. -/
def optimalCircuit (T : ℕ) : BoundedCircuit 2 (2 * T + 1) (Nat.clog 2 (2 * T + 1)) :=
  orCircuit (2 * T + 1)

theorem optimalCircuit_correct (T : ℕ) : (optimalCircuit T).eval = prediction T := by
  rw [prediction_eq_boolOr]
  exact orCircuit_eval _

theorem optimalCircuit_size (T : ℕ) : (optimalCircuit T).gateCount ≤ 2 * (2 * T + 1) :=
  orCircuit_linear_size _

/-- Exact optimum over every bounded-fan-in circuit; the witness has linear size. -/
theorem exact_prediction_depth (T : ℕ) :
    IsLeast {d | ∃ c : BoundedCircuit 2 (2 * T + 1) d, c.eval = prediction T}
      (Nat.clog 2 (2 * T + 1)) := by
  rw [prediction_eq_boolOr]
  exact boolOr_exact_depth _

theorem network_prediction_lower_bound {T d : ℕ} (N : LayeredNetwork 2 (2 * T + 1) d)
    (h : N.eval = prediction T) : Nat.clog 2 (2 * T + 1) ≤ d := by
  apply boolOr_network_depth_lower_bound N
  simpa [prediction_eq_boolOr] using h

/-- A finite form of the logarithmic asymptotic classification. -/
theorem optimal_depth_log_sandwich (T : ℕ) :
    Nat.clog 2 (T + 1) ≤ Nat.clog 2 (2 * T + 1) ∧
      Nat.clog 2 (2 * T + 1) ≤ Nat.clog 2 (T + 1) + 1 := by
  constructor
  · exact Nat.clog_mono_right 2 (by omega)
  · apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    have h := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (T + 1)
    rw [pow_succ]
    omega

theorem optimal_depth_log_factors {T : ℕ} (hT : 1 ≤ T) :
    Nat.clog 2 (T + 1) ≤ Nat.clog 2 (2 * T + 1) ∧
      Nat.clog 2 (2 * T + 1) ≤ 2 * Nat.clog 2 (T + 1) := by
  have h := optimal_depth_log_sandwich T
  have hp := Nat.clog_pos (by decide : 1 < (2 : ℕ)) (show 1 < T + 1 by omega)
  exact ⟨h.1, by omega⟩

theorem step_local : Geometry.Local 1 step := by
  intro x y i h
  simp only [step]
  rw [h (i - 1) (by omega) (by omega), h i (by omega) (by omega),
    h (i + 1) (by omega) (by omega)]

/-- The farthest cell in the light cone really can change the prediction. -/
theorem right_edge_influences (T : ℕ) : Geometry.Influences (evolve T) (T : ℤ) 0 := by
  let x : Config := fun _ => false
  let y : Config := fun j => decide (j = (T : ℤ))
  have hx : evolve T x 0 = false := by
    apply Bool.eq_false_iff.mpr
    simp [evolve_true_iff, x]
  have hy : evolve T y 0 = true := by
    apply (evolve_true_iff T y 0).mpr
    exact ⟨T, by omega, by omega, by simp [y]⟩
  refine ⟨x, y, ?_, ?_⟩
  · intro j hj; simp [x, y, hj]
  · rw [hx, hy]; decide

/-- Any geometrically radius-`r`, depth-`d` predictor must satisfy `T ≤ d*r`.
This hypothesis restricts the predictor, not just the original automaton. -/
theorem geometric_prediction_lower_bound {T d r : ℕ} {G : Config → Config}
    (hlocal : Geometry.Local (d * r) G)
    (hcorrect : ∀ x, G x 0 = evolve T x 0) : T ≤ d * r := by
  apply Geometry.geometric_depth_bound hlocal
  obtain ⟨x, y, hxy, hne⟩ := right_edge_influences T
  exact ⟨x, y, hxy, by simpa only [hcorrect] using hne⟩

theorem local_layers_prediction_lower_bound {T r : ℕ}
    (fs : List (Config → Config)) (hlocal : ∀ f ∈ fs, Geometry.Local r f)
    (hcorrect : ∀ x, Geometry.runLayers fs x 0 = evolve T x 0) : T ≤ fs.length * r :=
  geometric_prediction_lower_bound (Geometry.local_layers fs hlocal) hcorrect

end PredictionDepth.ORAutomaton
