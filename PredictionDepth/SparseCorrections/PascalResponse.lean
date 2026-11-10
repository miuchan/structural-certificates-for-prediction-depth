import PredictionDepth.SparseCorrections.ConeLayout
import PredictionDepth.SparseCorrections.Response
import PredictionDepth.FrozenPascal.CoefficientUniform

/-!
# Forced Pascal response

The reference reads a site and its right neighbor by XOR. Its impulse
coefficients are Pascal parities, with the horizontal offset adjusted for
the shrinking cone. The full circuit includes every initial and forcing bit.
-/

namespace PredictionDepth.SparseCorrections.Pascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity Turing.MultiTapeTM
open Linear (F₂)
open FrozenPascal (bit chooseParity)
open scoped BigOperators

abbrev Width (T : ℕ) := coneWidth 1 1 T
abbrev M (T : ℕ) := Cone.eventCount 1 1 T
abbrev V (T : ℕ) := Cone.stateCount 1 1 T
abbrev N (T : ℕ) := M T + Width T 0

/-- The same coordinate convention applies to either XOR or OR. -/
def applyNeighbors (f : Bool → Bool → Bool) (x : Cone.Config 1) : Cone.Config 1 :=
  fun i a => f (x i a) (x (i + 1) a)

def rule : Cone.Config 1 → Cone.Config 1 := applyNeighbors Bool.xor

theorem applyNeighbors_local (f : Bool → Bool → Bool) : Geometry.Local 1 (applyNeighbors f) := by
  intro x y i h
  funext a
  change f (x i a) (x (i + 1) a) = f (y i a) (y (i + 1) a)
  rw [h i (by omega) (by omega), h (i + 1) (by omega) (by omega)]

/-- In left-to-right layer coordinates, a successor at `j` reads
predecessors at `j+1` and `j+2`. -/
def predecessor {T t : ℕ} (ht : t < T) (j : Fin (Width T (t + 1))) (d : Fin 2) :
    Fin (Width T t) :=
  ⟨j.val + 1 + d.val, by
    have hj := j.isLt
    have hd := d.isLt
    simp only [coneWidth, one_mul, mul_one] at hj ⊢
    omega⟩

private theorem encode_val {T t : ℕ} (i : ℤ) (hi : Cone.InWindow 1 T t i) :
    (Cone.encodeBit 1 1 T t i hi 0).val = (i + (T - t : ℕ)).toNat := by
  change 0 + 1 * (i + (1 * (T - t) : ℕ)).toNat = _
  simp

theorem transition_applyNeighbors {T t : ℕ} (ht : t < T) (f : Bool → Bool → Bool)
    (u : Layer (Width T) t) (j : Fin (Width T (t + 1))) :
    Cone.transition 1 T (applyNeighbors f) t u j =
      f (u (predecessor ht j 0)) (u (predecessor ht j 1)) := by
  obtain ⟨i, hi, a, rfl⟩ := Cone.exists_encodeBit j
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  have hleft := Cone.predecessor_in_window ht hi (j := i) (by omega) (by omega)
  have hright := Cone.predecessor_in_window ht hi (j := i + 1) (by omega) (by omega)
  rw [Cone.transition, Cone.restrict_encodeBit]
  simp only [applyNeighbors, Cone.extend, hleft, hright, dite_true]
  congr 2
  all_goals
    apply Fin.ext
    simp only [predecessor, encode_val, Fin.val_zero, Fin.val_one, Nat.add_zero]
    simp only [Cone.InWindow, Cone.radius, one_mul] at hi
    omega

/-- Coefficient from local position `p` at time `s` to `j` at time `t`.
The left endpoint moves one site per layer. -/
def coefficient (s p t j : ℕ) : Bool :=
  decide (s ≤ t ∧ j + (t - s) ≤ p) && chooseParity (t - s) (p - (j + (t - s)))

private def weight (s p t j : ℕ) : F₂ :=
  if s ≤ t ∧ j + (t - s) ≤ p then (Nat.choose (t - s) (p - (j + (t - s))) : F₂)
  else 0

private theorem coefficient_weight (s p t j : ℕ) : bit (coefficient s p t j) = weight s p t j := by
  unfold coefficient weight
  by_cases h : s ≤ t ∧ j + (t - s) ≤ p
  · simpa [h] using (FrozenPascal.chooseParity_correct (t - s) (p - (j + (t - s)))).symm
  · simp [h, FrozenPascal.bit_false]

private theorem weight_zero (s p j : ℕ) :
    weight s p 0 j = bit (decide (s = 0 ∧ p = j)) := by
  by_cases hs : s = 0
  · subst s
    by_cases hp : p = j
    · simp [weight, hp, FrozenPascal.bit_true]
    · by_cases h : j ≤ p
      · simp [weight, h, hp, Nat.choose_eq_zero_of_lt (show 0 < p - j by omega),
          FrozenPascal.bit_false]
      · simp [weight, h, hp, FrozenPascal.bit_false]
  · simp [weight, hs, FrozenPascal.bit_false]

private theorem weight_succ (s p t j : ℕ) :
    weight s p (t + 1) j =
      weight s p t (j + 1) + weight s p t (j + 2) + bit (decide (s = t + 1 ∧ p = j)) := by
  by_cases hs : s ≤ t
  · let n := t - s
    have h₁ : t + 1 - s = n + 1 := by dsimp [n]; omega
    have h₂ : j + 1 + (t - s) = j + (n + 1) := by dsimp [n]; omega
    have h₃ : j + 2 + (t - s) = j + (n + 1) + 1 := by dsimp [n]; omega
    have hlt : s ≠ t + 1 := by omega
    unfold weight
    rw [h₁, h₂, h₃]
    -- The lower endpoint is a stay-only path. Above it Pascal's identity applies.
    by_cases hp : j + (n + 1) ≤ p
    · by_cases hb : j + (n + 1) + 1 ≤ p
      · have hdiff : p - (j + (n + 1)) = (p - (j + (n + 1) + 1)) + 1 := by omega
        simp only [hs, Nat.le_succ_of_le hs, hp, hb, true_and, ite_true, hlt, false_and,
          decide_false, FrozenPascal.bit_false, add_zero]
        change ((Nat.choose (n + 1) (p - (j + (n + 1))) : ℕ) : F₂) =
          (Nat.choose n (p - (j + (n + 1))) : F₂) + (Nat.choose n (p - (j + (n + 1) + 1)) : F₂)
        rw [hdiff, Nat.choose_succ_succ, Nat.cast_add, add_comm]
      · have hdiff : p - (j + (n + 1)) = 0 := by omega
        simp [hs, Nat.le_succ_of_le hs, hp, hb, hlt, hdiff, n, FrozenPascal.bit_false]
    · have hb : ¬ j + (n + 1) + 1 ≤ p := by omega
      simp [hs, Nat.le_succ_of_le hs, hp, hb, hlt, FrozenPascal.bit_false]
  · by_cases h : s = t + 1
    · subst s
      simp only [weight, hs, false_and, ite_false, zero_add, Nat.le_refl, Nat.sub_self, Nat.add_zero,
        true_and]
      by_cases hp : p = j
      · simp [hp, FrozenPascal.bit_true]
      · by_cases h : j ≤ p
        · simp [h, hp, Nat.choose_eq_zero_of_lt (show 0 < p - j by omega), FrozenPascal.bit_false]
        · simp [h, hp, FrozenPascal.bit_false]
    · simp [weight, hs, h, show ¬s ≤ t + 1 by omega, FrozenPascal.bit_false]

/-- The forcing inputs precede the initial layer. For a forcing input,
the source time is its update time plus one. -/
def sourceTime (T k : ℕ) : ℕ :=
  if k < M T then Cone.layerOf 1 1 (T - 1) k + 1 else 0

def sourcePosition (T k : ℕ) : ℕ :=
  if k < M T then k - Cone.offset 1 1 (T - 1) (sourceTime T k - 1) else k - M T

def coefficients (T r k : ℕ) : Bool :=
  let t := Cone.layerOf 1 1 T r
  coefficient (sourceTime T k) (sourcePosition T k) t (r - Cone.offset 1 1 T t)

def circuit (T : ℕ) : Gates (N T) (V T) :=
  LinearResponse.circuit (N T) (V T) (coefficients T)

theorem sourceTime_event {T : ℕ} (v : Event (Width T) T) :
    sourceTime T (Cone.eventIndex 1 1 T v).val = v.1.val + 1 := by
  rcases v with ⟨t, i⟩
  rw [sourceTime, ite_eq_left (Cone.eventIndex 1 1 T ⟨t, i⟩).isLt,
    Cone.layerOf_eventIndex 1 1 T (by decide)]

theorem sourcePosition_event {T : ℕ} (v : Event (Width T) T) :
    sourcePosition T (Cone.eventIndex 1 1 T v).val = v.2.val := by
  rcases v with ⟨t, i⟩
  rw [sourcePosition, ite_eq_left (Cone.eventIndex 1 1 T ⟨t, i⟩).isLt, sourceTime_event,
    Cone.eventIndex_val]
  simp

private theorem sourceTime_initial {T : ℕ} (i : Fin (Width T 0)) :
    sourceTime T (Fin.natAdd (M T) i).val = 0 := by
  simp [sourceTime]

private theorem sourcePosition_initial {T : ℕ} (i : Fin (Width T 0)) :
    sourcePosition T (Fin.natAdd (M T) i).val = i.val := by
  simp [sourcePosition]

private theorem sourceTime_position_injective {T : ℕ} {a b : Fin (N T)}
    (ht : sourceTime T a = sourceTime T b)
    (hp : sourcePosition T a = sourcePosition T b) : a = b := by
  apply Fin.ext
  by_cases ha : a.val < M T <;> by_cases hb : b.val < M T
  · have hbase (k : Fin (N T)) (hk : k.val < M T) :
        Cone.offset 1 1 (T - 1) (sourceTime T k - 1) ≤ k.val := by
      let v := (Cone.eventIndex 1 1 T).symm ⟨k.val, hk⟩
      have he : (Cone.eventIndex 1 1 T v).val = k.val := by
        simp [v]
      rw [← he, sourceTime_event]
      rcases v with ⟨t, i⟩
      simp only [Cone.eventIndex_val, Nat.add_sub_cancel]
      omega
    have ha' := hbase a ha
    have hb' := hbase b hb
    rw [ht] at ha'
    simp only [sourcePosition, ha, hb, ite_true, ht] at hp
    omega
  · simp [sourceTime, ha, hb] at ht
  · simp [sourceTime, ha, hb] at ht
  · simp only [sourcePosition, ha, hb, ite_false] at hp
    omega

private theorem fold_xor_to_sum (xs : List Bool) :
    bit (xs.foldr (· ^^ ·) false) = (xs.map bit).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [FrozenPascal.bit_xor, ih]

private theorem read_circuit {T : ℕ} (t : Fin (T + 1)) (j : Fin (Width T t.val))
    (x : Fin (N T) → Bool) :
    bit ((circuit T).eval interpretation x (Cone.stateIndex 1 1 T ⟨t, j⟩)) =
      ∑ k : Fin (N T), weight (sourceTime T k) (sourcePosition T k) t j * bit (x k) := by
  rw [circuit, LinearResponse.circuit_eval, fold_xor_to_sum, List.map_ofFn, List.sum_ofFn]
  have htime := Cone.layerOf_stateIndex 1 1 T (by decide) t j
  rw [Cone.stateIndex_val] at htime
  apply Finset.sum_congr rfl
  intro k _
  simp only [Function.comp_apply, coefficients, Cone.stateIndex_val, htime, Nat.add_sub_cancel_left,
    FrozenPascal.bit_and, coefficient_weight]

private theorem read_delta {T : ℕ} (k : Fin (N T)) (x : Fin (N T) → Bool) :
    (∑ a : Fin (N T),
      bit (decide (sourceTime T a = sourceTime T k ∧ sourcePosition T a = sourcePosition T k)) *
        bit (x a)) = bit (x k) := by
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
  · simp [FrozenPascal.bit_true]
  · intro a _ hne
    have h : ¬ (sourceTime T a = sourceTime T k ∧ sourcePosition T a = sourcePosition T k) :=
      fun ⟨ht, hp⟩ => hne (sourceTime_position_injective ht hp)
    simp [h, FrozenPascal.bit_false]

set_option maxHeartbeats 500000 in
theorem circuit_correct (T : ℕ) (u : Layer (Width T) 0) (e : Fin (M T) → Bool)
    (t : Fin (T + 1)) (j : Fin (Width T t.val)) :
    (circuit T).eval interpretation (Fin.append e u) (Cone.stateIndex 1 1 T ⟨t, j⟩) =
      forcedTrajectory (Cone.transition 1 T rule) u (e ∘ Cone.eventIndex 1 1 T) t j := by
  let x := Fin.append e u
  induction t using Fin.induction with
  | zero =>
    apply FrozenPascal.bit_injective
    rw [read_circuit]
    simp only [Fin.val_zero, weight_zero, forcedTrajectory_zero]
    let k : Fin (N T) := Fin.natAdd (M T) j
    have h := read_delta k x
    rw [show sourceTime T k = 0 from sourceTime_initial (T := T) j,
      show sourcePosition T k = j.val from sourcePosition_initial (T := T) j] at h
    have hx : x k = u j := Fin.append_right e u j
    rw [hx] at h
    exact h
  | succ t ih =>
    let l := predecessor t.isLt j 0
    let r := predecessor t.isLt j 1
    let k := Fin.castAdd (Width T 0) (Cone.eventIndex 1 1 T ⟨t, j⟩)
    apply FrozenPascal.bit_injective
    rw [read_circuit, forcedTrajectory_succ]
    have hstep : Cone.transition 1 T rule t.val
        (forcedTrajectory (Cone.transition 1 T rule) u (e ∘ Cone.eventIndex 1 1 T) t.castSucc) j =
        Bool.xor
          (forcedTrajectory (Cone.transition 1 T rule) u (e ∘ Cone.eventIndex 1 1 T) t.castSucc l)
          (forcedTrajectory (Cone.transition 1 T rule) u (e ∘ Cone.eventIndex 1 1 T) t.castSucc r) :=
      transition_applyNeighbors t.isLt Bool.xor _ j
    rw [hstep]
    change (∑ a : Fin (N T), weight (sourceTime T a) (sourcePosition T a) (t.val + 1) j *
      bit (x a)) = bit (Bool.xor (Bool.xor _ _) _)
    simp only [FrozenPascal.bit_xor]
    rw [← ih l, ← ih r, read_circuit, read_circuit, ← Finset.sum_add_distrib]
    have h := read_delta k x
    have he : bit ((e ∘ Cone.eventIndex 1 1 T) ⟨t, j⟩) = bit (x k) := by
      simp [k, x]
    rw [he, ← h, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [weight_succ, add_mul, k, Fin.val_castAdd, sourceTime_event, sourcePosition_event]
    rfl

theorem circuit_size (T : ℕ) :
    (circuit T).size ≤ V T * (2 * (N T + 1) * (FrozenPascal.xorGate.size + 3) + N T) :=
  LinearResponse.circuit_size _ _ _

theorem circuit_depth (T : ℕ) :
    (circuit T).depth ≤ 3 + Nat.clog 2 (N T) * (FrozenPascal.xorGate.depth + 1) :=
  LinearResponse.circuit_depth _ _ _

theorem inputCount_eq (T : ℕ) : N T = (T + 1) ^ 2 := by
  change Cone.eventCount 1 1 T + coneWidth 1 1 T 0 = _
  rw [Cone.eventCount_eq]
  cases T with
  | zero => rfl
  | succ T =>
    simp only [coneWidth, Nat.sub_zero, one_mul, mul_one, Nat.succ_sub_one]
    ring

theorem inputCount_eq_stateCount (T : ℕ) : N T = V T := by
  change N T = Cone.stateCount 1 1 T
  simp [inputCount_eq, Cone.stateCount_eq, pow_two]

theorem circuit_size_quadratic (T : ℕ) :
    (circuit T).size ≤ 17 * (V T + 1) ^ 2 :=
  (circuit_size T).trans (by
    rw [inputCount_eq_stateCount, FrozenPascal.xorGate_size]
    nlinarith)

theorem circuit_depth_logarithmic (T : ℕ) :
    (circuit T).depth ≤ 3 + 8 * Nat.clog 2 (T + 1) :=
  (circuit_depth T).trans (by
    rw [inputCount_eq, FrozenPascal.xorGate_depth]
    have hc := clog_power_bound (b := 2) (n := T + 1) (by decide) 2
    have h := Nat.mul_le_mul_right 4 hc
    omega)

private theorem width_logspace : ComputableInLogSpace N encUnary encUnary :=
  (Cone.eventCount_logspace 1 1).unaryAdd (inputWidth_logspace 1 1)

private abbrev encTimeWire := encPair encUnary encUnary

theorem sourceTime_logspace :
    ComputableInLogSpace (fun p : ℕ × ℕ => sourceTime p.1 p.2) encTimeWire encUnary := by
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have hk := ComputableInLogSpace.snd encUnary encUnary
  have hm := (Cone.eventCount_logspace 1 1).comp hT
  have ht := (Cone.layerOf_logspace 1 1).comp
    ((hT.unarySub (ComputableInLogSpace.const 1)).pair hk)
  exact ((hk.unaryLt hm).ite (ht.unaryAdd (ComputableInLogSpace.const 1))
    (ComputableInLogSpace.const 0)).congr_fun (fun _ => by simp [sourceTime])

theorem sourcePosition_logspace :
    ComputableInLogSpace (fun p : ℕ × ℕ => sourcePosition p.1 p.2) encTimeWire encUnary := by
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have hk := ComputableInLogSpace.snd encUnary encUnary
  have hm := (Cone.eventCount_logspace 1 1).comp hT
  have hbase := (Cone.offset_logspace 1 1).comp
    ((hT.unarySub (ComputableInLogSpace.const 1)).pair
      (sourceTime_logspace.unarySub (ComputableInLogSpace.const 1)))
  exact ((hk.unaryLt hm).ite (hk.unarySub hbase) (hk.unarySub hm)).congr_fun
    (fun _ => by simp [sourcePosition])

theorem coefficients_logspace :
    ComputableInLogSpace (fun p : (ℕ × ℕ) × ℕ => coefficients p.1.1 p.1.2 p.2)
      (encPair encTimeWire encUnary) encBool := by
  have hp := ComputableInLogSpace.fst encTimeWire encUnary
  have hk := ComputableInLogSpace.snd encTimeWire encUnary
  have hT := (ComputableInLogSpace.fst encUnary encUnary).comp hp
  have hr := (ComputableInLogSpace.snd encUnary encUnary).comp hp
  have hs := sourceTime_logspace.comp (hT.pair hk)
  have hpos := sourcePosition_logspace.comp (hT.pair hk)
  have ht := (Cone.layerOf_logspace 1 1).comp hp
  have hj := hr.unarySub ((Cone.offset_logspace 1 1).comp (hT.pair ht))
  have hd := ht.unarySub hs
  have hb := hj.unaryAdd hd
  have hchoose := FrozenPascal.chooseParity_logspace hd (hpos.unarySub hb)
  exact (((hs.unaryLe ht).bool_and (hb.unaryLe hpos)).bool_and hchoose).congr_fun (fun p => by
    unfold coefficients coefficient
    by_cases hs : sourceTime p.1.1 p.2 ≤ Cone.layerOf 1 1 p.1.1 p.1.2 <;>
      simp [hs])

theorem circuit_code_logspace :
    ComputableInLogSpace (fun T => (circuit T).code) encUnary encCode :=
  LinearResponse.circuit_code_logspace width_logspace (Cone.stateCount_logspace 1 1)
    coefficients_logspace

end PredictionDepth.SparseCorrections.Pascal
