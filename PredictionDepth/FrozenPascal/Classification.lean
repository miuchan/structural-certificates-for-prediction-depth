import PredictionDepth.FrozenPascal.LowerBound
import PredictionDepth.FrozenPascal.HomogeneousPascal

/-!
# Depth regimes for the frozen-control rule family

A rule with no hops reads only the origin. A rule with hops always on and
stays always off is a pure shift. A varying hop forces a logarithmic lower
bound. Even on an input supported at the far edge of the cone, every hop
along the path must be enabled. For a fixed enabled hop and a varying stay,
the parity restriction supplies the lower bound instead.
-/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open Linear (F₂)
open scoped BigOperators

private theorem iterate_noHop (stay hop : Q → Bool) (hHop : ∀ a, hop a = false)
    (T : ℕ) (x : Config Q) (i : ℤ) :
    ((step stay hop)^[T + 1] x).2 i = bit (stay (x.1 i)) * x.2 i := by
  induction T with
  | zero => simp [step, hHop]
  | succ T ih =>
    rw [Function.iterate_succ_apply']
    simp only [step, iterate_control, hHop, bit_false, zero_mul, add_zero, ih]
    cases stay (x.1 i) <;> simp

/-- A no-hop rule reads one local control word and data bit at positive times. -/
def noHopPrediction (stay : Gates q 1) (T : ℕ) : Gates (RawWidth q (T + 1)) 1 :=
  match T with
  | 0 => wireBit (rawDataWire 0)
  | _ + 1 => conjoin (stay.comp (Circuit.wiring signature (controlWire 0)))
      (wireBit (rawDataWire 0))

theorem noHopPrediction_correct (stay hop : Gates q 1) (hHop : ∀ a, guard hop a = false)
    (T : ℕ) (x : Config (Bits q)) :
    (noHopPrediction stay T).eval interpretation (rawSample x (T + 1)) 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
  cases T with
  | zero => simp [noHopPrediction]
  | succ T =>
    rw [iterate_noHop _ _ hHop]
    apply bit_injective
    have hControl :
        rawSample x (T + 1 + 1) ∘ controlWire 0 = x.1 0 := by
      funext j
      simp
    simp [noHopPrediction, Circuit.eval_comp, Circuit.eval_wiring, hControl, guard]

theorem noHopPrediction_depth (stay : Gates q 1) (T : ℕ) :
    (noHopPrediction stay T).depth ≤ 1 + stay.depth := by
  cases T with
  | zero => simp [noHopPrediction]
  | succ T =>
    apply (conjoin_depth _ _).trans
    simp only [wireBit_depth, max_zero, Nat.add_le_add_iff_left]
    exact (Circuit.depth_comp_le _ _).trans (by simp)

theorem noHopPrediction_size (stay : Gates q 1) (T : ℕ) :
    (noHopPrediction stay T).size ≤ stay.size + 1 := by
  cases T <;> simp [noHopPrediction]

private theorem iterate_shift (stay hop : Q → Bool)
    (hStay : ∀ a, stay a = false) (hHop : ∀ a, hop a = true)
    (T : ℕ) (x : Config Q) (i : ℤ) :
    ((step stay hop)^[T] x).2 i = x.2 (i + T) := by
  induction T generalizing i with
  | zero => simp
  | succ T ih =>
    rw [Function.iterate_succ_apply']
    simp only [step, hStay, hHop, bit_false, bit_true, zero_mul, one_mul, zero_add, ih]
    rw [show i + 1 + (T : ℤ) = i + (T + 1 : ℕ) by omega]

/-- A pure shift reads the data bit at the far edge of the cone. -/
def shiftPrediction (q T : ℕ) : Gates (RawWidth q (T + 1)) 1 :=
  wireBit (rawDataWire (Fin.last T))

theorem shiftPrediction_correct (stay hop : Gates q 1)
    (hStay : ∀ a, guard stay a = false) (hHop : ∀ a, guard hop a = true)
    (T : ℕ) (x : Config (Bits q)) :
    (shiftPrediction q T).eval interpretation (rawSample x (T + 1)) 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
  rw [iterate_shift _ _ hStay hHop]
  simp [shiftPrediction]

@[simp] theorem shiftPrediction_depth (q T : ℕ) : (shiftPrediction q T).depth = 0 := by
  simp [shiftPrediction]

@[simp] theorem shiftPrediction_size (q T : ℕ) : (shiftPrediction q T).size = 0 := by
  simp [shiftPrediction]

/-- Both Boolean values occur among the outputs of this control guard. -/
def GuardVaries (g : Gates q 1) : Prop :=
  ∃ off on, guard g off = false ∧ guard g on = true

private theorem guard_cases (g : Gates q 1) :
    (∀ a, guard g a = false) ∨ (∀ a, guard g a = true) ∨ GuardVaries g := by
  classical
  by_cases hOff : ∀ a, guard g a = false
  · exact Or.inl hOff
  · by_cases hOn : ∀ a, guard g a = true
    · exact Or.inr (Or.inl hOn)
    · obtain ⟨off, hoff⟩ := not_forall.mp hOn
      obtain ⟨on, hon⟩ := not_forall.mp hOff
      exact Or.inr (Or.inr ⟨off, on, by simpa using hoff, by simpa using hon⟩)

/-- Every fixed guard pair falls into the local-only, shift, logarithmic,
or homogeneous Pascal regime, respectively. -/
theorem guard_depth_cases (stay hop : Gates q 1) :
    (∀ a, guard hop a = false) ∨
    ((∀ a, guard stay a = false) ∧ (∀ a, guard hop a = true)) ∨
    (GuardVaries hop ∨ (∀ a, guard hop a = true) ∧ GuardVaries stay) ∨
    ((∀ a, guard stay a = true) ∧ (∀ a, guard hop a = true)) := by
  rcases guard_cases hop with hHop | hHop | hHop
  · exact Or.inl hHop
  · rcases guard_cases stay with hStay | hStay | hStay
    · exact Or.inr (Or.inl ⟨hStay, hHop⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hStay, hHop⟩))
    · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨hHop, hStay⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inl hHop)))

private theorem guard_essential (g : Gates q 1) (off on : Bits q)
    (hOff : guard g off = false) (hOn : guard g on = true) :
    ∃ j, EssentialAt (guard g) j := by
  by_contra! h
  have agree (s : Finset (Fin q)) (a b : Bits q) (hab : ∀ i ∉ s, a i = b i) :
      guard g a = guard g b := by
    induction s using Finset.induction_on generalizing a b with
    | empty =>
      exact congrArg (guard g) (funext fun i => hab i (by simp))
    | @insert i s hi ih =>
      let a' := Function.update a i (b i)
      have he : guard g a = guard g a' := by
        by_contra hne
        exact h i ⟨a, a', fun j hj => by simp [a', Function.update_of_ne hj], hne⟩
      rw [he]
      apply ih
      intro j hj
      by_cases hji : j = i
      · subst j
        simp [a']
      · rw [show a' j = a j by simp [a', Function.update_of_ne hji]]
        exact hab j (by simp [hji, hj])
  have he := agree Finset.univ off on (by simp)
  simp [hOff, hOn] at he

private theorem iterate_frontierPulse (stay hop : Q → Bool) (a : ℤ → Q) (T : ℕ) :
    ((step stay hop)^[T] (a, fun i => if i = (T : ℤ) then 1 else 0)).2 0 =
      ∏ j ∈ Finset.range T, bit (hop (a (j : ℤ))) := by
  rw [iterate_data, Finset.sum_eq_single T]
  · simp [coefficient, edgeProduct_prod]
  · intro j _ hj
    simp [hj]
  · simp

private theorem controlWire_injective (q m : ℕ) :
    Function.Injective (fun p : Fin m × Fin q => controlWire p.1 p.2) := by
  intro a b hab
  apply finProdFinEquiv.injective
  exact Fin.castAdd_inj.mp hab

/-- If the hop guard varies, at time `T` an essential control bit from each of
the first `T` sites and the data bit at site `T` force logarithmic depth. -/
theorem varyingHop_prediction_depth_lower_bound (stay hop : Gates q 1)
    (off on : Bits q) (hOff : guard hop off = false) (hOn : guard hop on = true)
    {σ : Signature} (I : Interpretation σ Bool)
    (T : ℕ) (c : Circuit σ (RawWidth q (T + 1)) 1) (hFan : c.FanInAtMost 2)
    (hc : ∀ x : Config (Bits q),
      c.eval I (rawSample x (T + 1)) 0 =
        ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0)) :
    Nat.clog 2 (T + 1) ≤ c.depth := by
  obtain ⟨b, left, right, hAgree, hNe⟩ := guard_essential hop off on hOff hOn
  let es : Fin T ↪ Fin (RawWidth q (T + 1)) :=
    ⟨fun i => controlWire i.castSucc b, fun i j h => by
      have hp : (i.castSucc, b) = (j.castSucc, b) := controlWire_injective q (T + 1) h
      exact Fin.castSucc_injective _ (congrArg Prod.fst hp)⟩
  let d : Fin (RawWidth q (T + 1)) := rawDataWire (Fin.last T)
  let pulse : ℤ → F₂ := fun i => if i = (T : ℤ) then 1 else 0
  have hEnabled : c.eval I (rawSample (fun _ => on, pulse) (T + 1)) 0 = true := by
    rw [hc, iterate_frontierPulse]
    simp [hOn]
  have hControl (i : Fin T) : EssentialAt (c.eval I) (es i) := by
    let cfg (w : Bits q) : Config (Bits q) :=
      (fun j => if j = (i.val : ℤ) then w else on, pulse)
    refine ⟨rawSample (cfg left) _, rawSample (cfg right) _, ?_, ?_⟩
    · intro k hk
      refine Fin.addCases (fun p hp => ?_) (fun j _ => ?_) k hk
      · obtain ⟨⟨j, a⟩, rfl⟩ := finProdFinEquiv.surjective p
        change rawSample (cfg left) _ (controlWire j a) = rawSample (cfg right) _ (controlWire j a)
        rw [rawSample_control, rawSample_control]
        by_cases hji : j.val = i.val
        · have hj : j = i.castSucc := Fin.ext hji
          subst j
          have hab : a ≠ b := by
            intro he
            subst a
            exact hp rfl
          simpa [cfg] using hAgree a hab
        · have hne : (j.val : ℤ) ≠ (i.val : ℤ) := by exact_mod_cast hji
          simp [cfg, hne]
      · change rawSample (cfg left) _ (rawDataWire j) = rawSample (cfg right) _ (rawDataWire j)
        simp only [rawSample_data, cfg]
    · intro he
      have hOut (w : Bits q) :
          c.eval I (rawSample (cfg w) (T + 1)) 0 = guard hop w := by
        rw [hc, iterate_frontierPulse, Finset.prod_eq_single i.val]
        · simp
          cases guard hop w <;> rfl
        · intro j _ hj
          have hne : (j : ℤ) ≠ (i.val : ℤ) := by exact_mod_cast hj
          simp [hne, hOn]
        · simp [i.isLt]
      exact hNe ((hOut left).symm.trans ((congrFun he 0).trans (hOut right)))
  have hData : EssentialAt (c.eval I) d := by
    let zero : Config (Bits q) := (fun _ => on, fun _ => 0)
    refine ⟨rawSample (fun _ => on, pulse) _, rawSample zero _, ?_, ?_⟩
    · intro k hk
      refine Fin.addCases (fun _ _ => ?_) (fun j hj => ?_) k hk
      · simp only [rawSample, joinBits_left, zero]
      · have hne : j ≠ Fin.last T := fun he => hj (by subst j; rfl)
        have hjT : (j.val : ℤ) ≠ (T : ℤ) := by
          intro he
          apply hne
          exact Fin.ext (by exact_mod_cast he)
        change rawSample (fun _ => on, pulse) _ (rawDataWire j) = rawSample zero _ (rawDataWire j)
        simp [pulse, zero, hjT]
    · intro he
      have hZero : c.eval I (rawSample zero (T + 1)) 0 = false := by
        rw [hc, iterate_data]
        simp [zero]
      have hBad : true = false := hEnabled.symm.trans ((congrFun he 0).trans hZero)
      cases hBad
  let selected := Finset.univ.map es
  have hd : d ∉ selected := by
    intro hm
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hm
    have hlt := (finProdFinEquiv (i.castSucc, b)).isLt
    have he := congrArg Fin.val hi
    change (finProdFinEquiv (i.castSucc, b)).val = (T + 1) * q + T at he
    omega
  have h := c.essential_le_depth (show c.Computes I (c.eval I) from fun _ => rfl)
    (selected := insert d selected) (fun k hk => by
      rcases Finset.mem_insert.mp hk with rfl | hm
      · exact hData
      · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hm
        exact hControl i) hFan
  rw [Finset.card_insert_of_notMem hd] at h
  exact Nat.clog_le_of_le_pow (by simpa [selected] using h)

/-- Every varying-hop rule and every varying-stay rule with an always enabled
hop has a logarithmic lower bound at every time. -/
theorem varyingGuard_prediction_depth_lower_bound (stay hop : Gates q 1)
    (h : GuardVaries hop ∨ (∀ a, guard hop a = true) ∧ GuardVaries stay)
    {σ : Signature} (I : Interpretation σ Bool)
    (T : ℕ) (c : Circuit σ (RawWidth q (T + 1)) 1) (hFan : c.FanInAtMost 2)
    (hc : ∀ x : Config (Bits q),
      c.eval I (rawSample x (T + 1)) 0 =
        ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0)) :
    Nat.clog 2 (T + 1) ≤ c.depth := by
  rcases h with ⟨off, on, hOff, hOn⟩ | ⟨hHop, off, on, hOff, hOn⟩
  · exact varyingHop_prediction_depth_lower_bound stay hop off on hOff hOn I T c hFan hc
  · exact guarded_prediction_depth_lower_bound stay hop off on hOff hOn (hHop off) (hHop on)
      I T c hFan hc

/-- A family of predictors has a common constant depth bound exactly for
no-hop rules and pure shifts. -/
theorem bounded_prediction_depth_iff (stay hop : Gates q 1) :
    (∃ (D : ℕ) (c : (T : ℕ) → Gates (RawWidth q (T + 1)) 1),
      (∀ T x, (c T).eval interpretation (rawSample x (T + 1)) 0 =
        ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0)) ∧
      (∀ T, (c T).depth ≤ D)) ↔
    (∀ a, guard hop a = false) ∨
      (∀ a, guard stay a = false) ∧ (∀ a, guard hop a = true) := by
  constructor
  · rintro ⟨D, c, hc, hd⟩
    let T := 2 ^ (D + 1) - 1
    have hclog : Nat.clog 2 (T + 1) = D + 1 := by
      have hpow : 0 < (2 : ℕ) ^ (D + 1) := pow_pos (by decide) _
      rw [show T + 1 = 2 ^ (D + 1) by dsimp [T]; omega, Nat.clog_pow 2 _ (by decide)]
    rcases guard_depth_cases stay hop with h | h | h | ⟨hStay, hHop⟩
    · exact Or.inl h
    · exact Or.inr h
    · have hLower := varyingGuard_prediction_depth_lower_bound stay hop h interpretation T (c T)
        (c T).fanInAtMost_two (hc T)
      rw [hclog] at hLower
      exact False.elim ((Nat.not_succ_le_self D) (hLower.trans (hd T)))
    · have hLower := homogeneous_prediction_depth_lower_bound stay hop hStay hHop
        interpretation T (c T) (c T).fanInAtMost_two (hc T)
      change (2 ^ (D + 1) - 1 : ℕ).bitIndices.length ≤ (c T).depth at hLower
      rw [pascal_time_all_ones] at hLower
      exact False.elim ((Nat.not_succ_le_self D) (hLower.trans (hd T)))
  · rintro (hHop | ⟨hStay, hHop⟩)
    · exact ⟨1 + stay.depth, noHopPrediction stay, noHopPrediction_correct stay hop hHop,
        noHopPrediction_depth stay⟩
    · exact ⟨0, shiftPrediction q, shiftPrediction_correct stay hop hStay hHop, fun T => by simp⟩

end PredictionDepth.FrozenPascal
