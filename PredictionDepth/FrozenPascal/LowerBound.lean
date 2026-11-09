import PredictionDepth.FrozenPascal.Separation

/-! A parity restriction witnesses linearly many essential input bits. -/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open Linear (F₂)
open scoped BigOperators

def originStay (i : ℤ) : Bool × Bool := (decide (i = 0), true)

theorem originStay_count_pos (i : ℤ) (hi : 0 < i) (k : ℕ) :
    enabled Prod.fst originStay i k = 0 := by
  induction k generalizing i with
  | zero => simp [enabled, originStay, ne_of_gt hi]
  | succ k ih =>
    simp [enabled, originStay, ne_of_gt hi, ih (i + 1) (by omega)]

theorem originStay_count (k : ℕ) : enabled Prod.fst originStay 0 k = 1 := by
  cases k with
  | zero => simp [enabled, originStay]
  | succ k => simp [enabled, originStay, originStay_count_pos 1 (by omega) k]

theorem originStay_edges (i : ℤ) (k : ℕ) : edgeProduct Prod.snd originStay i k = 1 := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [edgeProduct, originStay, ih]

def restrictedInput (v : Bits m) : Bits (InputWidth m) :=
  joinBits (fun j : Fin m => decide (j.val = 0))
    (joinBits (fun _ : Fin m => true) v)

def parityConfig (v : Bits m) : Config (Bool × Bool) :=
  (originStay, fun i => bit (extendTrack v i))

theorem sample_parityConfig (v : Bits m) :
    sample Prod.fst Prod.snd (parityConfig v) m = restrictedInput v := by
  unfold sample restrictedInput
  congr 1
  · funext j
    simp [parityConfig, originStay]
  · congr 1
    funext j
    rw [show (parityConfig v).2 (j.val : ℤ) = bit (v j) by simp [parityConfig]]
    cases v j <;> rfl

def target (T : ℕ) (x : Bits (InputWidth (T + 1))) (_ : Fin 1) : Bool :=
  observe ((step Prod.fst Prod.snd)^[T] (initial x))

theorem target_restricted (T : ℕ) (v : Bits (T + 1)) :
    bit (target T (restrictedInput v) 0) = ∑ j, bit (v j) := by
  rw [target, observe, bit_ofBoolRing, ← sample_parityConfig,
    sample_prediction Prod.fst Prod.snd (parityConfig v) (Nat.lt_succ_self T), iterate_data]
  have hf : ∀ k ∈ Finset.range (T + 1),
      coefficient Prod.fst Prod.snd (parityConfig v).1 0 T k = 1 := by
    intro k hk
    have hle : k ≤ T := by have := Finset.mem_range.mp hk; omega
    simp [coefficient, parityConfig, hle, originStay_count, originStay_edges]
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => coefficient Prod.fst Prod.snd
    (parityConfig v).1 0 T k * (parityConfig v).2 (0 + k)) (T + 1)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hf j.val (Finset.mem_range.mpr j.isLt), one_mul, zero_add]
  simp [parityConfig]

theorem dataWire_injective (m : ℕ) : Function.Injective (dataWire (m := m)) := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  simpa [dataWire] using he

theorem data_essential (T : ℕ) (i : Fin (T + 1)) : EssentialAt (target T) (dataWire i) := by
  let x : Bits (T + 1) := fun _ => false
  let y : Bits (T + 1) := fun j => decide (j = i)
  refine ⟨restrictedInput x, restrictedInput y, ?_, ?_⟩
  · intro k hk
    refine Fin.addCases (fun _ _ => ?_) (fun j hj => ?_) k hk
    · simp [restrictedInput]
    · refine Fin.addCases (fun _ _ => ?_) (fun p hp => ?_) j hj
      · simp [restrictedInput]
      · have hne : p ≠ i := fun he => hp (congrArg dataWire he)
        simp only [restrictedInput, joinBits_right, x, y, decide_eq_false hne]
  · intro h
    have he := congrArg (fun v : Bits 1 => bit (v 0)) h
    change bit (target T (restrictedInput x) 0) = bit (target T (restrictedInput y) 0) at he
    rw [target_restricted, target_restricted] at he
    have hy : (∑ j : Fin (T + 1), bit (y j)) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp [y]
      · intro j _ hne
        simp [y, hne]
      · simp
    rw [hy] at he
    simp [x] at he

theorem prediction_depth_lower_bound (T : ℕ) (c : Gates (InputWidth (T + 1)) 1)
    (hc : c.Computes interpretation (target T)) : Nat.clog 2 (T + 1) ≤ c.depth := by
  let es : Fin (T + 1) ↪ Fin (InputWidth (T + 1)) :=
    ⟨dataWire, dataWire_injective _⟩
  have h := c.essential_le_depth hc (selected := Finset.univ.map es)
    (fun k hk => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hk
      exact data_essential T i) c.fanInAtMost_two
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
  simpa using h

/-- Any pair of control symbols that keeps the hop enabled and switches the
stay suffices for the lower bound on raw inputs. -/
theorem guarded_prediction_depth_lower_bound (stay hop : Gates q 1)
    (off on : Bits q) (hOff : guard stay off = false) (hOn : guard stay on = true)
    (hHopOff : guard hop off = true) (hHopOn : guard hop on = true)
    {σ : Signature} (I : Interpretation σ Bool)
    (T : ℕ) (c : Circuit σ (RawWidth q (T + 1)) 1) (hFan : c.FanInAtMost 2)
    (hc : ∀ x : Config (Bits q),
      c.eval I (rawSample x (T + 1)) 0 =
        ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0)) :
    Nat.clog 2 (T + 1) ≤ c.depth := by
  let conf (v : Bits (T + 1)) : Config (Bits q) :=
    (fun j => if j = 0 then on else off, (parityConfig v).2)
  have hsample (v : Bits (T + 1)) :
      sample (guard stay) (guard hop) (conf v) (T + 1) = restrictedInput v := by
    rw [← sample_parityConfig]
    unfold sample
    congr 1
    · funext j
      by_cases hj : j.val = 0 <;> simp [conf, parityConfig, originStay, hj, hOff, hOn]
    · congr 1
      funext j
      by_cases hj : j.val = 0 <;> simp [conf, parityConfig, originStay, hj, hHopOff, hHopOn]
  have hparity (v : Bits (T + 1)) :
      bit (c.eval I (rawSample (conf v) (T + 1)) 0) = ∑ j, bit (v j) := by
    rw [hc, bit_ofBoolRing, ← sample_prediction (guard stay) (guard hop) (conf v)
      (Nat.lt_succ_self T), hsample]
    simpa only [target, observe, bit_ofBoolRing] using target_restricted T v
  let es : Fin (T + 1) ↪ Fin (RawWidth q (T + 1)) :=
    ⟨rawDataWire, fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩
  have he (i : Fin (T + 1)) :
      EssentialAt (c.eval I) (es i) := by
    let x : Bits (T + 1) := fun _ => false
    let y : Bits (T + 1) := fun j => decide (j = i)
    refine ⟨rawSample (conf x) _, rawSample (conf y) _, ?_, ?_⟩
    · intro k hk
      refine Fin.addCases (fun j _ => ?_) (fun j hj => ?_) k hk
      · simp only [rawSample, joinBits_left, conf]
      · have hne : j ≠ i := fun h => hj (congrArg es h)
        rw [show Fin.natAdd ((T + 1) * q) j = rawDataWire j from rfl,
          rawSample_data, rawSample_data]
        simp [conf, parityConfig, x, y, hne]
    · intro h
      have hp := congrArg (fun b : Bits 1 => bit (b 0)) h
      simp only [hparity] at hp
      have hy : (∑ j : Fin (T + 1), bit (y j)) = 1 := by
        rw [Finset.sum_eq_single i]
        · simp [y]
        · intro j _ hne
          simp [y, hne]
        · simp
      rw [hy] at hp
      simp [x] at hp
  have h := c.essential_le_depth (show c.Computes I (c.eval I) from
    fun _ => rfl) (selected := Finset.univ.map es)
    (fun k hk => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hk
      exact he i) hFan
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
  simpa using h

/-- The AND/OR member satisfies the two-symbol condition. -/
def orGuard : Gates 2 1 :=
  ((Formula.input (n := 2) 0).or (.input 1)).toCircuit

theorem and_or_prediction_depth_lower_bound {σ : Signature} (I : Interpretation σ Bool)
    (T : ℕ) (c : Circuit σ (RawWidth 2 (T + 1)) 1) (hFan : c.FanInAtMost 2)
    (hc : ∀ x : Config (Bits 2),
      c.eval I (rawSample x (T + 1)) 0 =
        ofBoolRing (((step (guard andGate) (guard orGuard))^[T] x).2 0)) :
    Nat.clog 2 (T + 1) ≤ c.depth := by
  exact guarded_prediction_depth_lower_bound andGate orGuard
    (fun i => decide (i = 0)) (fun _ => true)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) I T c hFan hc

end PredictionDepth.FrozenPascal
