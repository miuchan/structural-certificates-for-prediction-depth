import PredictionDepth.FrozenPascal.CoefficientBits
import PredictionDepth.FrozenPascal.GuardRules
import Mathlib.Combinatorics.Colex

/-! When both guards are constantly true, the odd entries of Pascal's
triangle describe the exact support and control the depth at each time. -/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open Linear (F₂)
open scoped BigOperators

private theorem chooseParity_eq_true_iff (T k : ℕ) :
    chooseParity T k = true ↔ Finset.equivBitIndices k ⊆ Finset.equivBitIndices T := by
  simp only [chooseParity, List.all_eq_true, Finset.equivBitIndices_apply,
    Finset.subset_iff, List.mem_toFinset, Nat.mem_bitIndices]
  constructor
  · intro h i hi
    have hik : i < k := Nat.lt_two_pow_self.trans_le (Nat.ge_two_pow_of_testBit hi)
    simpa [hi] using h i (List.mem_range.mpr (by omega : i < max T k + 1))
  · intro h i _
    cases hi : k.testBit i with
    | false => simp
    | true => simp [h hi]

/-- The data coordinates with odd binomial coefficient in row `T`. -/
def pascalSupport (T : ℕ) : Finset (Fin (T + 1)) :=
  Finset.univ.filter fun i => chooseParity T i.val = true

/-- Each odd entry corresponds to a subset of the set bits of `T`. -/
theorem pascalSupport_card (T : ℕ) : (pascalSupport T).card = 2 ^ T.bitIndices.length := by
  let e : Fin (T + 1) ↪ Finset ℕ :=
    ⟨fun i => Finset.equivBitIndices i.val, fun _ _ h => Fin.ext (Finset.equivBitIndices.injective h)⟩
  have hmap : (pascalSupport T).map e = (Finset.equivBitIndices T).powerset := by
    ext s
    rw [Finset.mem_map, Finset.mem_powerset]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (chooseParity_eq_true_iff T i.val).mp (Finset.mem_filter.mp hi).2
    · intro hs
      let k := Finset.equivBitIndices.symm s
      have hle : k ≤ T := by
        change Finset.equivBitIndices.symm s ≤ T
        rw [← Finset.sum_toFinset_bitIndices_two_pow T, Finset.equivBitIndices_symm_apply]
        exact Finset.sum_le_sum_of_subset hs
      have he : Finset.equivBitIndices k = s := Finset.equivBitIndices.apply_symm_apply s
      refine ⟨⟨k, Nat.lt_succ_of_le hle⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
      exact (chooseParity_eq_true_iff T k).mpr (he ▸ hs)
  rw [← Finset.card_map e, hmap, Finset.card_powerset]
  simp [List.toFinset_card_of_nodup]

/-- When both guards are constantly true, the answer is the parity of the
data coordinates in the odd support of Pascal row `T`. -/
theorem homogeneous_prediction_sum (stay hop : Gates q 1)
    (hs : ∀ a, guard stay a = true) (hh : ∀ a, guard hop a = true)
    (T : ℕ) (x : Config (Bits q)) :
    ((step (guard stay) (guard hop))^[T] x).2 0 =
      ∑ i ∈ pascalSupport T, bit (rawSample x (T + 1) (rawDataWire i)) := by
  have hstay (j : ℤ) (k : ℕ) : enabled (guard stay) x.1 j k = k + 1 := by
    induction k generalizing j with
    | zero => simp [enabled, hs]
    | succ k ih => simp [enabled, hs, ih, Nat.add_comm 1]
  have hhop (j : ℤ) (k : ℕ) : edgeProduct (guard hop) x.1 j k = 1 := by
    induction k generalizing j with
    | zero => rfl
    | succ k ih => simp [edgeProduct, hh, ih]
  rw [iterate_data, ← Fin.sum_univ_eq_sum_range (fun k =>
    coefficient (guard stay) (guard hop) x.1 0 T k * x.2 (0 + k))]
  rw [pascalSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have hi := Nat.le_of_lt_succ i.isLt
  have hsum : i.val + 1 + (T - i.val) - 1 = T := by omega
  simp only [coefficient, hi, ite_true, hstay, hhop, one_mul, Nat.multichoose_eq, hsum,
    Nat.choose_symm hi, chooseParity_correct, zero_add, rawSample_data, bit_ofBoolRing]
  cases chooseParity T i.val <;> simp

/-- The number of set bits of `T` lower-bounds the depth of every predictor
with fan-in at most two, even with arbitrary Boolean gates and sharing. -/
theorem homogeneous_prediction_depth_lower_bound (stay hop : Gates q 1)
    (hs : ∀ a, guard stay a = true) (hh : ∀ a, guard hop a = true)
    {σ : Signature} (I : Interpretation σ Bool)
    (T : ℕ) (c : Circuit σ (RawWidth q (T + 1)) 1) (hFan : c.FanInAtMost 2)
    (hc : ∀ x : Config (Bits q),
      c.eval I (rawSample x (T + 1)) 0 =
        ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0)) :
    T.bitIndices.length ≤ c.depth := by
  let e : Fin (T + 1) ↪ Fin (RawWidth q (T + 1)) :=
    ⟨rawDataWire, fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩
  have hsum (u : Bits (RawWidth q (T + 1))) :
      bit (c.eval I u 0) = ∑ j ∈ pascalSupport T, bit (u (e j)) := by
    calc
      _ = ((step (guard stay) (guard hop))^[T] (decodeRaw u)).2 0 := by
        simpa only [rawSample_decodeRaw, bit_ofBoolRing] using congrArg bit (hc (decodeRaw u))
      _ = _ := by
        rw [homogeneous_prediction_sum stay hop hs hh, rawSample_decodeRaw]
        rfl
  have he (i : Fin (T + 1)) (hi : i ∈ pascalSupport T) : EssentialAt (c.eval I) (e i) := by
    let u : Bits (RawWidth q (T + 1)) := fun _ => false
    let v : Bits (RawWidth q (T + 1)) := fun j => decide (j = e i)
    refine ⟨u, v, fun j hj => by simp [u, v, hj], ?_⟩
    intro h
    have hp := congrArg (fun b : Bits 1 => bit (b 0)) h
    change bit (c.eval I u 0) = bit (c.eval I v 0) at hp
    have hv : (∑ j ∈ pascalSupport T, bit (v (e j))) = 1 := by
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [v]
      · intro j _ hji
        simp [v, hji, e.injective.eq_iff]
    rw [hsum u, hsum v, hv] at hp
    simp [u] at hp
  have h := c.essential_le_depth (show c.Computes I (c.eval I) from fun _ => rfl)
    (selected := (pascalSupport T).map e)
    (fun k hk => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
      exact he i hi) hFan
  rw [Finset.card_map, pascalSupport_card] at h
  rw [← Nat.clog_pow 2 T.bitIndices.length (by decide)]
  apply (Nat.clog_le_iff_le_pow (b := 2) (by decide)).mpr
  simpa using h

private def pascalWires (σ : Signature) (q T : ℕ) :
    List (Circuit σ (RawWidth q (T + 1)) 1) :=
  ((pascalSupport T).sort (· ≤ ·)).map fun i => Circuit.wiring σ (fun _ => rawDataWire i)

/-- A balanced parity circuit on just the data wires that contribute. -/
def homogeneousPrediction (q T : ℕ) : Gates (RawWidth q (T + 1)) 1 :=
  parity (pascalWires signature q T)

theorem homogeneousPrediction_correct (stay hop : Gates q 1)
    (hs : ∀ a, guard stay a = true) (hh : ∀ a, guard hop a = true)
    (T : ℕ) (x : Config (Bits q)) :
    (homogeneousPrediction q T).eval interpretation (rawSample x (T + 1)) 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
  apply bit_injective
  rw [bit_ofBoolRing, homogeneous_prediction_sum stay hop hs hh, homogeneousPrediction,
    parity_eval]
  simp only [pascalWires, List.map_map]
  rw [← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rfl

private theorem pascalWires_length (σ : Signature) (q T : ℕ) :
    (pascalWires σ q T).length = 2 ^ T.bitIndices.length := by
  rw [pascalWires, List.length_map, Finset.length_sort, pascalSupport_card]

private theorem pascalWires_ne_nil (σ : Signature) (q T : ℕ) : pascalWires σ q T ≠ [] := by
  rw [← List.length_pos_iff, pascalWires_length]
  exact pow_pos (by decide) _

/-- Each level of the balanced parity tree costs at most three De Morgan layers. -/
theorem homogeneousPrediction_depth (q T : ℕ) :
    (homogeneousPrediction q T).depth ≤ 3 * T.bitIndices.length := by
  have hd := Circuit.depth_balanced_le xorGate (constBit (RawWidth q (T + 1)) false)
    (D := 0) (l := pascalWires signature q T)
    (fun c hc => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      simp)
    (fun he => (pascalWires_ne_nil signature q T he).elim)
  simpa [homogeneousPrediction, parity, pascalWires_length, Nat.clog_pow 2 _ (by decide)] using hd

theorem homogeneousPrediction_size (q T : ℕ) :
    (homogeneousPrediction q T).size = 5 * (2 ^ T.bitIndices.length - 1) := by
  rw [homogeneousPrediction, parity, Circuit.size_balanced _ _ (pascalWires_ne_nil signature q T),
    pascalWires_length, xorGate_size]
  have hsum : ((pascalWires signature q T).map Circuit.size).sum = 0 := by
    simp only [pascalWires, List.map_map]
    change (List.map (fun i => (wireBit (rawDataWire (q := q) i)).size) _).sum = 0
    rw [List.map_congr_left (g := fun _ => 0) (fun i _ => wireBit_size (rawDataWire i))]
    simp
  rw [hsum, zero_add, Nat.mul_comm]

private def nativeXor : Circuit (fullSignature 2 Bool) 2 1 :=
  Circuit.oneGate (.fn fun u => u 0 ^^ u 1) id

/-- Balanced reduction of the odd-coefficient inputs with one native XOR per merge. -/
def homogeneousNativeXorPrediction (q T : ℕ) : Circuit (fullSignature 2 Bool)
    (RawWidth q (T + 1)) 1 :=
  Circuit.balanced nativeXor (Circuit.oneGate (.con false) Fin.elim0)
    (pascalWires (fullSignature 2 Bool) q T)

theorem homogeneousNativeXorPrediction_correct (stay hop : Gates q 1)
    (hs : ∀ a, guard stay a = true) (hh : ∀ a, guard hop a = true)
    (T : ℕ) (x : Config (Bits q)) :
    (homogeneousNativeXorPrediction q T).eval fullInterpretation (rawSample x (T + 1)) 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
  apply bit_injective
  rw [bit_ofBoolRing, homogeneous_prediction_sum stay hop hs hh,
    homogeneousNativeXorPrediction, Circuit.eval_balanced]
  have hxor (a b : Bits 1) :
      bit (nativeXor.eval fullInterpretation (Fin.append a b) 0) = bit (a 0) + bit (b 0) :=
    bit_xor _ _
  rw [List.balancedFold_hom (fun u : Bits 1 => bit (u 0)) hxor]
  change (pascalWires (fullSignature 2 Bool) q T).balancedFold (· + ·) (0 : F₂)
    (fun c => bit (c.eval fullInterpretation (rawSample x (T + 1)) 0)) = _
  rw [List.balancedFold_eq_foldr]
  change ((pascalWires (fullSignature 2 Bool) q T).map
    (fun c => bit (c.eval fullInterpretation (rawSample x (T + 1)) 0))).sum = _
  simp only [pascalWires, List.map_map]
  rw [← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rfl

/-- The native XOR predictor attains the lower bound for all fan-in-two predictors. -/
theorem homogeneousNativeXorPrediction_depth (stay hop : Gates q 1)
    (hs : ∀ a, guard stay a = true) (hh : ∀ a, guard hop a = true) (T : ℕ) :
    (homogeneousNativeXorPrediction q T).depth = T.bitIndices.length := by
  apply le_antisymm
  · have hxor : nativeXor.depth = 1 := Circuit.depth_oneGate _ _
    have hd := Circuit.depth_balanced_le nativeXor
      (Circuit.oneGate (σ := fullSignature 2 Bool) (.con false) Fin.elim0)
      (D := 0) (l := pascalWires (fullSignature 2 Bool) q T)
      (fun c hc => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
        simp)
      (fun he => (pascalWires_ne_nil (fullSignature 2 Bool) q T he).elim)
    simpa [homogeneousNativeXorPrediction, hxor, pascalWires_length,
      Nat.clog_pow 2 _ (by decide)] using hd
  · apply homogeneous_prediction_depth_lower_bound stay hop hs hh fullInterpretation T _
    · apply Program.fanInAtMost_iff.mpr
      intro j
      cases (homogeneousNativeXorPrediction q T).program.lines j |>.op <;> simp [fullSignature]
    · exact homogeneousNativeXorPrediction_correct stay hop hs hh T

/-- At powers of two just two data inputs contribute, so a single XOR suffices. -/
theorem homogeneousPrediction_depth_two_pow (q r : ℕ) :
    (homogeneousPrediction q (2 ^ r)).depth ≤ 3 := by
  simpa using homogeneousPrediction_depth q (2 ^ r)

/-- Times whose binary representation consists of `r` ones have a depth
lower bound of `r` by `homogeneous_prediction_depth_lower_bound`. -/
theorem pascal_time_all_ones (r : ℕ) : (2 ^ r - 1 : ℕ).bitIndices.length = r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : (2 ^ (r + 1) - 1 : ℕ) = 2 * (2 ^ r - 1) + 1 := by
      rw [pow_succ]
      have : 0 < (2 : ℕ) ^ r := pow_pos (by decide) _
      omega
    simp [h, ih]

end PredictionDepth.FrozenPascal
