import PredictionDepth.FrozenPascal.Decoder
import Mathlib.Tactic.Linarith

/-! Finite resource bounds for the explicit frozen-control predictor. -/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := n)).le

theorem matchWord_depth (v : FastComposition.Bits w) :
    (matchWord v).depth ≤ 1 + Nat.clog 2 w := by
  apply conjunction_depth_fin _ _ (by decide)
  intro j
  unfold matchingBit
  split
  · simp
  · exact (Circuit.depth_comp_le _ _).trans (by simp [notGate])

theorem matchWord_size (v : FastComposition.Bits w) : (matchWord v).size ≤ 1 + 2 * w := by
  rw [show 1 + 2 * w = 1 + w * (1 + 1) by omega]
  apply conjunction_size_fin
  intro j
  unfold matchingBit
  split <;> simp [notGate]

theorem row_depth (u : Fin m) (k : ℕ) (s : Fin (k + 2)) :
    (row u k s).depth ≤ 2 + countWidth k := by
  unfold row
  split
  · have h := conjoin_depth (wireBit (Fin.castAdd (countWidth k) u))
      ((matchWord (countWord s)).comp (Circuit.wiring signature (Fin.natAdd m)))
    have hw := Circuit.depth_comp_le (matchWord (countWord s))
      (Circuit.wiring signature (Fin.natAdd m))
    have hm := matchWord_depth (countWord s)
    simp only [Circuit.depth_wiring, Nat.add_zero] at hw
    simp only [wireBit_depth, zero_max] at h
    have := clog_le_self (countWidth k)
    omega
  · simp; omega

theorem row_size (u : Fin m) (k : ℕ) (s : Fin (k + 2)) :
    (row u k s).size ≤ 2 + 2 * countWidth k := by
  unfold row
  split
  · have h := matchWord_size (countWord s)
    simp only [conjoin_size, wireBit_size, Circuit.size_comp, Circuit.size_wiring, zero_add]
    omega
  · simp; omega

theorem lookup_depth (m k : ℕ) :
    (lookup m k).depth ≤ 2 + 4 * countWidth k + 3 * Nat.clog 2 m := by
  have h (u : Fin m) :
      (parity (List.ofFn (row u k))).depth ≤ 2 + 4 * countWidth k := by
    have hb := parity_depth_fin (row u k) (2 + countWidth k) (by omega) (row_depth u k)
    change _ ≤ 2 + countWidth k + 3 * countWidth k at hb
    omega
  exact parity_depth_fin _ _ (by omega) h

theorem lookup_size (m k : ℕ) :
    (lookup m k).size ≤ 1 + m * (6 + (k + 2) * (7 + 2 * countWidth k)) := by
  have h (u : Fin m) :
      (parity (List.ofFn (row u k))).size ≤ 1 + (k + 2) * (7 + 2 * countWidth k) := by
    have hb := parity_size_fin (row u k) (2 + 2 * countWidth k) (row_size u k)
    rw [show 2 + 2 * countWidth k + 5 = 7 + 2 * countWidth k by omega] at hb
    exact hb
  have hb := parity_size_fin _ _ h
  rw [show 1 + (k + 2) * (7 + 2 * countWidth k) + 5 =
    6 + (k + 2) * (7 + 2 * countWidth k) by omega] at hb
  exact hb

theorem count_depth (k : Fin m) : (count k).depth ≤ 1 + 19 * countWidth k.val := by
  apply (Circuit.depth_comp_le _ _).trans
  simpa only [Circuit.depth_wiring, Nat.add_zero] using depth_weightCircuit_le (k.val + 1)

theorem lookupInputs_depth (k : Fin m) :
    (lookupInputs k).depth ≤ 1 + 19 * countWidth k.val := by
  apply (Circuit.depth_append_le _ _).trans
  simpa only [Circuit.depth_wiring, zero_max] using count_depth k

theorem edge_depth (k : Fin m) : (edge k).depth ≤ 1 + Nat.clog 2 k.val := by
  exact conjunction_depth_fin _ 1 (by decide) (fun _ => by simp)

theorem edge_size (k : Fin m) : (edge k).size ≤ 1 + k.val := by
  simpa [edge] using conjunction_size_fin (fun j : Fin k.val =>
    wireBit (trackWire (hopWire (Fin.castLE k.isLt.le j)))) 0 (fun _ => by simp)

theorem term_depth (k : Fin m) : (term k).depth ≤ 5 + 26 * Nat.clog 2 (m + 1) := by
  let l := Nat.clog 2 (m + 1)
  have hw : countWidth k.val ≤ l := Nat.clog_mono_right 2 (by have := k.isLt; omega)
  have hm : Nat.clog 2 m ≤ l := Nat.clog_mono_right 2 (by omega)
  have hk : Nat.clog 2 k.val ≤ l := Nat.clog_mono_right 2 (by have := k.isLt; omega)
  let c := (lookup m k.val).comp (lookupInputs k)
  have hc : c.depth ≤ 3 + 26 * l := by
    have hl := lookup_depth m k.val
    have hi := lookupInputs_depth k
    have hb := Circuit.depth_comp_le (lookup m k.val) (lookupInputs k)
    change c.depth ≤ _ at hb
    omega
  have he : (edge k).depth ≤ 3 + 26 * l := by
    have := edge_depth k
    omega
  have hfirst := (conjoin_depth c (edge k)).trans
    (Nat.add_le_add_left (max_le hc he) 1)
  have h := conjoin_depth (conjoin c (edge k)) (wireBit (trackWire (dataWire k)))
  simp only [wireBit_depth, max_zero] at h
  exact h.trans (by omega)

theorem decoder_depth (m : ℕ) : (decoder m).depth ≤ 5 + 29 * Nat.clog 2 (m + 1) := by
  have h := parity_depth_fin (term (m := m)) (5 + 26 * Nat.clog 2 (m + 1))
    (by omega) term_depth
  have hm := Nat.clog_mono_right 2 (show m ≤ m + 1 by omega)
  exact h.trans (by omega)

theorem term_size (k : Fin m) : (term k).size ≤ 81 * (m + 1) ^ 3 := by
  let b := m + 1
  let w := countWidth k.val
  have hb : 1 ≤ b := by omega
  have hk : k.val + 2 ≤ b := by have := k.isLt; omega
  have hw : w ≤ b := (clog_le_self _).trans hk
  have h2 : b ≤ b ^ 2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb (by decide : 1 ≤ 2)
  have h3 : b ^ 2 ≤ b ^ 3 := Nat.pow_le_pow_right hb (by decide : 2 ≤ 3)
  have hl : (lookup m k.val).size ≤ 16 * b ^ 3 := by
    have h := lookup_size m k.val
    have hrow : 7 + 2 * w ≤ 9 * b := by omega
    have hs := Nat.mul_le_mul hk hrow
    have ht : 6 + (k.val + 2) * (7 + 2 * w) ≤ 15 * b ^ 2 := by
      change _ ≤ _ at hs
      nlinarith
    have hmul := Nat.mul_le_mul (show m ≤ b by omega) ht
    nlinarith
  have hc : (lookupInputs k).size ≤ 62 * b ^ 2 := by
    have h := size_weightCircuit_le (k.val + 1)
    change (weightCircuit (k.val + 1)).size ≤ max 1 (k.val + 1) +
      (k.val + 1) * (40 * w) + w * (20 * w + 1) at h
    have hmax : max 1 (k.val + 1) ≤ b := max_le hb (by omega)
    have hm := Nat.mul_le_mul (show k.val + 1 ≤ b by omega)
      (Nat.mul_le_mul_left 40 hw)
    have hn := Nat.mul_le_mul hw (show 20 * w + 1 ≤ 21 * b by omega)
    simp only [lookupInputs, count, Circuit.size_append, Circuit.size_wiring,
      Circuit.size_comp, zero_add]
    nlinarith
  have he := edge_size k
  have hek : 1 + k.val ≤ b := by have := k.isLt; omega
  change (term k).size ≤ 81 * b ^ 3
  simp only [term, conjoin_size, wireBit_size, Circuit.size_comp, add_zero]
  nlinarith

theorem decoder_size (m : ℕ) : (decoder m).size ≤ 87 * (m + 1) ^ 4 := by
  let b := m + 1
  have hb : 1 ≤ b := by omega
  have h3 : 1 ≤ b ^ 3 := Nat.one_le_pow _ _ hb
  have h4 : 1 ≤ b ^ 4 := Nat.one_le_pow _ _ hb
  have h := parity_size_fin (term (m := m)) (81 * b ^ 3) term_size
  change (decoder m).size ≤ _ at h
  have hm := Nat.mul_le_mul (show m ≤ b by omega)
    (show 81 * b ^ 3 + 5 ≤ 86 * b ^ 3 by omega)
  change (decoder m).size ≤ 87 * b ^ 4
  nlinarith

end PredictionDepth.FrozenPascal
