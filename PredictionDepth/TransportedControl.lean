import PredictionDepth.Circuit
import PredictionDepth.Dynamics
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Sort

/-!
# Prediction depth with transported controls

A one-bit control and a one-bit datum occupy each site. The control moves by a
fixed velocity, and the datum is transported at a possibly different velocity
and masked by the current control at its destination. Both velocities belong
to `{0, 1}`. An observer at a fixed site sees the conjunction of one initial
datum and the distinct initial controls along its backward path.

The relative velocity changes the number of controls visited. In particular,
transporting the control makes even a no-hop data rule require unbounded depth.
-/

namespace PredictionDepth.TransportedControl

abbrev Config := Geometry.Config (Bool × Bool)

/-- Simultaneous updates. The mask is read at the destination in the old state. -/
def step (u v : Bool) (x : Config) (i : ℤ) : Bool × Bool :=
  ((x (i + u.toNat)).1, (x i).1 && (x (i + v.toNat)).2)

theorem step_local (u v : Bool) : Geometry.Local 1 (step u v) := by
  intro x y i h
  have hu : (u.toNat : ℤ) ≤ 1 := by cases u <;> decide
  have hv : (v.toNat : ℤ) ≤ 1 := by cases v <;> decide
  unfold step
  rw [h (i + u.toNat) (by omega) (by omega), h i (by omega) (by omega),
    h (i + v.toNat) (by omega) (by omega)]

theorem iterate_control (u v : Bool) (T : ℕ) (x : Config) (i : ℤ) :
    (((step u v)^[T] x) i).1 = (x (i + (T : ℤ) * u.toNat)).1 := by
  induction T generalizing i with
  | zero => simp
  | succ T ih =>
    rw [Function.iterate_succ_apply']
    cases u <;> simp [step, ih, add_left_comm, add_comm]

/-- The path from the observation back to the initial datum meets one control
at each step. The control met after `s` backward data steps started at the
offset `(T - 1 - s) * u.toNat + s * v.toNat`. -/
theorem iterate_data_true_iff (u v : Bool) (T : ℕ) (x : Config) (i : ℤ) :
    (((step u v)^[T] x) i).2 = true ↔
      (x (i + (T : ℤ) * v.toNat)).2 = true ∧
        ∀ s : ℕ, s < T →
          (x (i + ((T - 1 - s : ℕ) : ℤ) * u.toNat + (s : ℤ) * v.toNat)).1 = true := by
  induction T generalizing i with
  | zero => simp
  | succ T ih =>
    rw [Function.iterate_succ_apply']
    simp only [step, Bool.and_eq_true, iterate_control, ih, Nat.add_sub_cancel,
      Nat.cast_succ, add_mul, one_mul]
    have hdata : i + (v.toNat : ℤ) + (T : ℤ) * v.toNat =
        i + ((T : ℤ) * v.toNat + v.toNat) := by ac_rfl
    have hnext (s : ℕ) : i + (v.toNat : ℤ) + ((T - 1 - s : ℕ) : ℤ) * u.toNat +
          (s : ℤ) * v.toNat =
        i + ((T - (s + 1) : ℕ) : ℤ) * u.toNat + ((s : ℤ) + 1) * v.toNat := by
      rw [show T - 1 - s = T - (s + 1) by omega, add_mul, one_mul]
      ac_rfl
    rw [hdata]
    constructor
    · rintro ⟨hfirst, hdata, hrest⟩
      refine ⟨hdata, ?_⟩
      intro s hs
      cases s with
      | zero => simpa using hfirst
      | succ s => simpa only [hnext, Nat.cast_succ] using hrest s (by omega)
    · rintro ⟨hdata, h⟩
      refine ⟨by simpa using h 0 (by omega), hdata, ?_⟩
      intro s hs
      simpa only [hnext, Nat.cast_succ] using h (s + 1) (by omega)

abbrev WindowWidth (T : ℕ) := (T + 1) + (T + 1)

def controlWire (T : ℕ) : Fin (T + 1) ↪ Fin (WindowWidth T) := Fin.castAddEmb _

def dataWire (T : ℕ) : Fin (T + 1) ↪ Fin (WindowWidth T) := Fin.natAddEmb _

/-- Encode controls first, then data, on the sites from the origin to `T`. -/
def sample (T : ℕ) (x : Config) : BooleanInput (WindowWidth T) :=
  Fin.addCases (fun j => (x j.val).1) (fun j => (x j.val).2)

@[simp] theorem sample_controlWire (T : ℕ) (x : Config) (j : Fin (T + 1)) :
    sample T x (controlWire T j) = (x j.val).1 := by
  simp [sample, controlWire]

@[simp] theorem sample_dataWire (T : ℕ) (x : Config) (j : Fin (T + 1)) :
    sample T x (dataWire T j) = (x j.val).2 := by
  exact Fin.addCases_right j

/-- Fill outside the explicit input window with zero cells. -/
def embed (T : ℕ) (x : BooleanInput (WindowWidth T)) (i : ℤ) : Bool × Bool :=
  if h : 0 ≤ i ∧ i ≤ (T : ℤ) then
    (x (controlWire T ⟨i.toNat, by omega⟩), x (dataWire T ⟨i.toNat, by omega⟩))
  else (false, false)

theorem sample_embed (T : ℕ) (x : BooleanInput (WindowWidth T)) : sample T (embed T x) = x := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · change sample T (embed T x) (controlWire T k) = x (controlWire T k)
    simp [embed, show (k.val : ℤ) ≤ T by omega]
  · change sample T (embed T x) (dataWire T k) = x (dataWire T k)
    simp [embed, show (k.val : ℤ) ≤ T by omega]

/-- Distinct initial control sites sampled at time `T`. -/
def controlSites (u v : Bool) (T : ℕ) : Finset (Fin (T + 1)) :=
  if T = 0 then ∅
  else if u = v then {⟨(T - 1) * v.toNat, by cases v <;> simp; omega⟩}
  else Finset.univ.map Fin.castSuccEmb

theorem controlSites_mem_iff (u v : Bool) (T : ℕ) (j : Fin (T + 1)) :
    j ∈ controlSites u v T ↔
      ∃ s : ℕ, s < T ∧ j.val = (T - 1 - s) * u.toNat + s * v.toNat := by
  by_cases h : T = 0
  · subst T
    simp [controlSites]
  have hcast : j ∈ (Finset.univ : Finset (Fin T)).map Fin.castSuccEmb ↔ j.val < T := by
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      exact k.isLt
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
  cases u <;> cases v <;>
    simp only [controlSites, h, Bool.toNat_false, Bool.toNat_true,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Finset.mem_singleton,
      Fin.ext_iff, hcast, Nat.mul_zero, Nat.mul_one, add_zero, zero_add]
  · constructor
    · intro hj
      exact ⟨0, by omega, hj⟩
    · rintro ⟨s, _, hj⟩
      exact hj
  · constructor
    · intro hj
      exact ⟨j.val, hj, rfl⟩
    · rintro ⟨s, hs, hj⟩
      omega
  · constructor
    · intro hj
      exact ⟨T - 1 - j.val, by omega, by omega⟩
    · rintro ⟨s, hs, hj⟩
      omega
  · constructor
    · intro hj
      exact ⟨0, by omega, by omega⟩
    · rintro ⟨s, hs, hj⟩
      omega

def terminalSite (v : Bool) (T : ℕ) : Fin (T + 1) :=
  ⟨T * v.toNat, by cases v <;> simp⟩

/-- The support is a disjoint union of control wires and the terminal data wire. -/
def predictionSupport (u v : Bool) (T : ℕ) : Finset (Fin (WindowWidth T)) :=
  insert (dataWire T (terminalSite v T)) ((controlSites u v T).map (controlWire T))

def supportCount (u v : Bool) (T : ℕ) : ℕ :=
  if T = 0 then 1 else if u = v then 2 else T + 1

theorem predictionSupport_card (u v : Bool) (T : ℕ) :
    (predictionSupport u v T).card = supportCount u v T := by
  have hterminal : dataWire T (terminalSite v T) ∉ (controlSites u v T).map (controlWire T) := by
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
    have he := congrArg Fin.val hj
    change j.val = T + 1 + (terminalSite v T).val at he
    omega
  rw [predictionSupport, Finset.card_insert_of_notMem hterminal, Finset.card_map]
  unfold controlSites supportCount
  split_ifs <;> simp

/-- Every infinite configuration with the same sampled window has the same
answer at the origin. This formula also discards the nonessential window bits. -/
theorem iterate_at_origin_true_iff (u v : Bool) (T : ℕ) (x : Config) :
    (((step u v)^[T] x) 0).2 = true ↔
      ∀ j ∈ predictionSupport u v T, sample T x j = true := by
  rw [iterate_data_true_iff]
  simp only [predictionSupport, Finset.forall_mem_insert, Finset.forall_mem_map,
    sample_controlWire, sample_dataWire, terminalSite, Nat.cast_mul, zero_add]
  apply and_congr_right
  intro _
  constructor
  · intro h j hj
    obtain ⟨s, hs, he⟩ := (controlSites_mem_iff u v T j).mp hj
    simpa only [he, Nat.cast_add, Nat.cast_mul] using h s hs
  · intro h s hs
    let j : Fin (T + 1) := ⟨(T - 1 - s) * u.toNat + s * v.toNat, by
      cases u <;> cases v <;> simp <;> omega⟩
    have hj := h j ((controlSites_mem_iff u v T j).mpr ⟨s, hs, rfl⟩)
    simpa [j, Nat.cast_add, Nat.cast_mul] using hj

def prediction (u v : Bool) (T : ℕ) (x : BooleanInput (WindowWidth T)) : Bool :=
  (((step u v)^[T] (embed T x)) 0).2

theorem prediction_true_iff (u v : Bool) (T : ℕ) (x : BooleanInput (WindowWidth T)) :
    prediction u v T x = true ↔ ∀ j ∈ predictionSupport u v T, x j = true := by
  simpa only [prediction, sample_embed] using iterate_at_origin_true_iff u v T (embed T x)

theorem prediction_sample (u v : Bool) (T : ℕ) (x : Config) :
    prediction u v T (sample T x) = (((step u v)^[T] x) 0).2 := by
  apply Bool.eq_iff_iff.mpr
  rw [prediction_true_iff, iterate_at_origin_true_iff]

/-- The path description is exact even at the level of individual input wires. -/
theorem essential_prediction_iff (u v : Bool) (T : ℕ) (j : Fin (WindowWidth T)) :
    Essential (prediction u v T) j ↔ j ∈ predictionSupport u v T := by
  constructor
  · rintro ⟨x, y, hagree, hne⟩
    by_contra hj
    apply hne
    apply Bool.eq_iff_iff.mpr
    simp only [prediction_true_iff]
    constructor <;> intro h i hi
    · rw [← hagree i (fun he => hj (he ▸ hi))]
      exact h i hi
    · rw [hagree i (fun he => hj (he ▸ hi))]
      exact h i hi
  · intro hj
    refine ⟨fun _ => true, fun i => decide (i ≠ j), ?_, ?_⟩
    · intro i hi
      simp [hi]
    · have ht : prediction u v T (fun _ => true) = true :=
        (prediction_true_iff u v T _).mpr (by simp)
      rw [ht]
      intro h
      simpa using (prediction_true_iff u v T _).mp h.symm j hj

theorem prediction_essential_count (u v : Bool) (T : ℕ) :
    (essentialInputs (prediction u v T)).card = supportCount u v T := by
  classical
  have h : essentialInputs (prediction u v T) = predictionSupport u v T := by
    ext j
    simp [essentialInputs, essential_prediction_iff]
  rw [h, predictionSupport_card]

/-- Dualizing the truth tables and constants computes the Boolean dual
without adding layers or gates. In particular it turns the OR tree into AND. -/
private def dual {n d : ℕ} : BoundedCircuit 2 n d → BoundedCircuit 2 n d
  | .input i => .input i
  | .constant a => .constant (!a)
  | .gate op args => .gate (fun w => !(op fun j => !(w j))) (fun j => dual (args j))

private theorem dual_eval {n d : ℕ} (c : BoundedCircuit 2 n d) (x : BooleanInput n) :
    (dual c).eval x = !(c.eval fun i => !(x i)) := by
  induction c with
  | input i => simp [dual, BoundedCircuit.eval]
  | constant a => rfl
  | gate op args ih => simp [dual, BoundedCircuit.eval, ih]

private theorem dual_gateCount {n d : ℕ} (c : BoundedCircuit 2 n d) :
    (dual c).gateCount = c.gateCount := by
  induction c with
  | input i => rfl
  | constant a => rfl
  | gate op args ih => simp [dual, BoundedCircuit.gateCount, ih]

/-- A balanced binary AND tree on the distinct essential wires. -/
def optimalCircuit (u v : Bool) (T : ℕ) :
    BoundedCircuit 2 (WindowWidth T) (Nat.clog 2 (supportCount u v T)) :=
  dual (BoundedCircuit.orTree _ (predictionSupport u v T).sort)

theorem optimalCircuit_correct (u v : Bool) (T : ℕ) :
    (optimalCircuit u v T).eval = prediction u v T := by
  funext x
  rw [optimalCircuit, dual_eval, BoundedCircuit.orTree_eval]
  · apply Bool.eq_iff_iff.mpr
    simp [prediction_true_iff]
  · rw [Finset.length_sort, predictionSupport_card]
    exact Nat.le_pow_clog (by decide) _

theorem optimalCircuit_size (u v : Bool) (T : ℕ) :
    (optimalCircuit u v T).gateCount ≤ 2 * supportCount u v T := by
  rw [optimalCircuit, dual_gateCount, BoundedCircuit.orTree_gateCount, ← orCircuit_gateCount]
  exact orCircuit_linear_size _

/-- Time zero has depth zero. At positive times equal velocities have depth
one and unequal velocities have depth `⌈log₂(T+1)⌉`, with a linear-size witness. -/
theorem exact_prediction_depth (u v : Bool) (T : ℕ) :
    IsLeast {d | ∃ c : BoundedCircuit 2 (WindowWidth T) d, c.eval = prediction u v T}
      (Nat.clog 2 (supportCount u v T)) := by
  constructor
  · exact ⟨optimalCircuit u v T, optimalCircuit_correct u v T⟩
  · rintro d ⟨c, hc⟩
    simpa only [hc, prediction_essential_count] using c.essential_depth_lower_bound (by decide)

theorem network_prediction_lower_bound {u v : Bool} {T d : ℕ}
    (N : LayeredNetwork 2 (WindowWidth T) d) (h : N.eval = prediction u v T) :
    Nat.clog 2 (supportCount u v T) ≤ d := by
  simpa only [h, prediction_essential_count] using N.essential_depth_lower_bound (by decide)

/-- A single depth bound works for all times exactly when the velocities agree. -/
theorem constant_depth_iff (u v : Bool) :
    (∃ D : ℕ, ∀ T, ∃ d ≤ D, ∃ c : BoundedCircuit 2 (WindowWidth T) d,
      c.eval = prediction u v T) ↔ u = v := by
  constructor
  · rintro ⟨D, h⟩
    by_contra huv
    obtain ⟨d, hd, c, hc⟩ := h (2 ^ D)
    have hl := (exact_prediction_depth u v (2 ^ D)).2 ⟨c, hc⟩
    have hp := (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mp (hl.trans hd)
    simp [supportCount, huv] at hp
  · intro huv
    refine ⟨1, fun T => ⟨_, ?_, optimalCircuit u v T, optimalCircuit_correct u v T⟩⟩
    cases T with
    | zero => simp [supportCount]
    | succ T => simp [supportCount, huv]; decide

end PredictionDepth.TransportedControl
