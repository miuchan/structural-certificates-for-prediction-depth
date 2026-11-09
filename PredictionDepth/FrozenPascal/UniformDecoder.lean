import PredictionDepth.FrozenPascal.UniformReducers
import PredictionDepth.FrozenPascal.Resources
import CslibFrontier.Foundations.Data.BitString.Binary

/-! A decoder layout assembled from uniformly generated scalar circuit banks. -/

namespace PredictionDepth.FrozenPascal.UniformDecoder

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open scoped BigOperators

def literal (w s j : ℕ) : Gates w 1 :=
  if hj : j < w then matchingBit ⟨j, hj⟩ (s.testBit j) else constBit w false

def matchCount (k s : ℕ) : Gates (countWidth k) 1 :=
  reduceBank allFamily (fun j : Fin (countWidth k) => literal (countWidth k) s j.val)

theorem matchCount_eval {k : ℕ} (s : Fin (k + 2)) (v : Bits (countWidth k)) :
    (matchCount k s.val).eval interpretation v 0 = (matchWord (countWord s)).eval interpretation v 0 := by
  rw [matchCount, allBank_eval, matchWord]
  congr 3
  funext j
  simp only [literal, dite_eq_left j.isLt, countWord, BitString.equivFin_symm_apply, Fin.val_castLE]

theorem literal_depth (w s j : ℕ) : (literal w s j).depth ≤ 1 := by
  unfold literal
  split
  · unfold matchingBit
    split
    · simp
    · exact (Circuit.depth_comp_le _ _).trans (by simp [notGate])
  · simp

def paddedMatch (m k s : ℕ) : Gates (m + countWidth k) 1 :=
  (matchCount k s).comp (Circuit.wiring signature (Fin.natAdd m))

def lookupEntry (m k u s : ℕ) : Gates (m + countWidth k) 1 :=
  if hu : u < m ∧ tableBit u k s = true then
    conjoin (wireBit (Fin.castAdd (countWidth k) (⟨u, hu.1⟩ : Fin m))) (paddedMatch m k s)
  else constBit _ false

theorem lookupEntry_eval (u : Fin m) (k : ℕ) (s : Fin (k + 2))
    (v : Bits (m + countWidth k)) :
    (lookupEntry m k u.val s.val).eval interpretation v 0 =
      (row u k s).eval interpretation v 0 := by
  cases h : tableBit u.val k s.val <;>
    simp [lookupEntry, row, u.isLt, h, paddedMatch, Circuit.eval_comp, matchCount_eval]

def lookupSlice (W : WeightBasis) (m k u : ℕ) : Gates (m + countWidth k) 1 :=
  reduceBank (parityFamily W) (fun s : Fin (k + 2) => lookupEntry m k u s.val)

def lookup (W : WeightBasis) (m k : ℕ) : Gates (m + countWidth k) 1 :=
  reduceBank (parityFamily W) (fun u : Fin m => lookupSlice W m k u.val)

theorem lookup_eval (W : WeightBasis) (m k : ℕ) (v : Bits (m + countWidth k)) :
    (lookup W m k).eval interpretation v 0 =
      (FrozenPascal.lookup m k).eval interpretation v 0 := by
  apply bit_injective
  simp only [lookup, FrozenPascal.lookup, parityBank_eval, parity_eval_fin]
  apply Finset.sum_congr rfl
  intro u _
  simp only [lookupSlice, parityBank_eval, parity_eval_fin, lookupEntry_eval]

def count (W : WeightBasis) (k : Fin m) : Gates (RegisterWidth m) (countWidth k.val) :=
  (W.circuit (k.val + 1)).comp (Circuit.wiring signature (countInputs k))

theorem count_eval (W : WeightBasis) (k : Fin m) (x : Bits (RegisterWidth m)) :
    (count W k).eval interpretation x = (FrozenPascal.count k).eval interpretation x := by
  unfold count FrozenPascal.count
  simp only [Circuit.eval_comp]
  apply (BitString.equivFin _).injective
  apply Fin.ext
  rw [W.value, val_eval_weightCircuit]

def lookupInputs (W : WeightBasis) (k : Fin m) : Gates (RegisterWidth m) (m + countWidth k.val) :=
  (Circuit.wiring signature timeWire).append (count W k)

def hopInput (m j : ℕ) : Gates (RegisterWidth m) 1 :=
  if hj : j < m then wireBit (trackWire (hopWire ⟨j, hj⟩)) else constBit _ false

def edge (k : Fin m) : Gates (RegisterWidth m) 1 :=
  reduceBank allFamily (fun j : Fin k.val => hopInput m j.val)

theorem edge_eval (k : Fin m) (x : Bits (RegisterWidth m)) :
    (edge k).eval interpretation x 0 = (FrozenPascal.edge k).eval interpretation x 0 := by
  rw [edge, allBank_eval, FrozenPascal.edge]
  congr 3
  funext j
  simp [hopInput, j.isLt.trans k.isLt]
  rfl

def term (W : WeightBasis) (k : Fin m) : Gates (RegisterWidth m) 1 :=
  conjoin (conjoin ((lookup W m k.val).comp (lookupInputs W k)) (edge k))
    (wireBit (trackWire (dataWire k)))

theorem term_eval (W : WeightBasis) (k : Fin m) (x : Bits (RegisterWidth m)) :
    (term W k).eval interpretation x 0 = (FrozenPascal.term k).eval interpretation x 0 := by
  simp [term, FrozenPascal.term, Circuit.eval_comp, lookup_eval, edge_eval,
    lookupInputs, FrozenPascal.lookupInputs, count_eval]

def decoder (W : WeightBasis) (m : ℕ) : Gates (RegisterWidth m) 1 :=
  reduceBank (parityFamily W) (term W)

theorem decoder_eval (W : WeightBasis) (x : Bits (RegisterWidth m)) :
    (decoder W m).eval interpretation x 0 = (FrozenPascal.decoder m).eval interpretation x 0 := by
  apply bit_injective
  simp [decoder, FrozenPascal.decoder, parityBank_eval, parity_eval_fin, term_eval]

theorem decoder_depth (W : WeightBasis) (m : ℕ) :
    (decoder W m).depth ≤ (10 + 4 * W.depthFactor) * (Nat.clog 2 (m + 2) + 1) := by
  let L := Nat.clog 2 (m + 2) + 1
  let P := (W.depthFactor + 1) * L
  have hL : 1 ≤ L := by dsimp only [L]; omega
  have hlog (j : ℕ) (hj : j ≤ m + 2) : Nat.clog 2 j + 1 ≤ L :=
    Nat.add_le_add_right (Nat.clog_mono_right 2 hj) 1
  have hpar (j : ℕ) (hj : j ≤ m + 1) : (parityFamily W j).depth ≤ P :=
    (parityFamily_depth W j).trans (Nat.mul_le_mul_left _ (hlog (j + 1) (by omega)))
  have hterm (k : Fin m) : (term W k).depth ≤ 2 + 5 * L + 2 * P + W.depthFactor * L := by
    have hk := k.isLt
    have hw : countWidth k.val + 1 ≤ L := hlog (k.val + 2) (by omega)
    have hmatch (s : ℕ) : (paddedMatch m k.val s).depth ≤ 4 + countWidth k.val := by
      have ha := reduceBank_depth allFamily
        (fun j : Fin (countWidth k.val) => literal (countWidth k.val) s j.val)
        (fun j => literal_depth (countWidth k.val) s j.val)
      have hb := allFamily_depth (countWidth k.val)
      have hc := clog_le_self (countWidth k.val)
      have hd := Circuit.depth_comp_le (matchCount k.val s)
        (Circuit.wiring signature (Fin.natAdd m))
      simp only [Circuit.depth_wiring, add_zero] at hd
      change (paddedMatch m k.val s).depth ≤ _ at hd
      change (matchCount k.val s).depth ≤ _ at ha
      omega
    have hrow (u s : ℕ) : (lookupEntry m k.val u s).depth ≤ 5 * L := by
      unfold lookupEntry
      split_ifs with hu
      · have he := conjoin_depth (wireBit (Fin.castAdd (countWidth k.val) (⟨u, hu.1⟩ : Fin m)))
          (paddedMatch m k.val s)
        simp only [wireBit_depth, zero_max] at he
        have := hmatch s
        omega
      · simp only [constBit_depth]
        omega
    have hslice (u : ℕ) : (lookupSlice W m k.val u).depth ≤ P + 5 * L :=
      (reduceBank_depth _ _ (fun s => hrow u s.val)).trans
        (Nat.add_le_add_right (hpar (k.val + 2) (by omega)) _)
    have hlu : (lookup W m k.val).depth ≤ 2 * P + 5 * L := by
      have h := reduceBank_depth (parityFamily W) (fun u : Fin m => lookupSlice W m k.val u.val)
        (fun u => hslice u.val)
      change (lookup W m k.val).depth ≤ _ at h
      have := hpar m (by omega)
      omega
    have hcount : (count W k).depth ≤ W.depthFactor * L := by
      have hc := (W.depth (k.val + 1)).trans (Nat.mul_le_mul_left _ hw)
      exact (Circuit.depth_comp_le _ _).trans (by
        simpa only [Circuit.depth_wiring, add_zero] using hc)
    have hinputs : (lookupInputs W k).depth ≤ W.depthFactor * L :=
      (Circuit.depth_append_le _ _).trans (by simpa only [Circuit.depth_wiring, zero_max] using hcount)
    let c := (lookup W m k.val).comp (lookupInputs W k)
    have hc : c.depth ≤ 5 * L + 2 * P + W.depthFactor * L := by
      have he := (Circuit.depth_comp_le _ _).trans (Nat.add_le_add hlu hinputs)
      exact he.trans (by omega)
    have hed : (edge k).depth ≤ 5 * L := by
      have ha := reduceBank_depth allFamily (fun j : Fin k.val => hopInput m j.val) (D := 1)
        (fun j => by unfold hopInput; split <;> simp)
      change (edge k).depth ≤ _ at ha
      have hb := allFamily_depth k.val
      have hh := hlog k.val (by omega)
      omega
    have ha := conjoin_depth c (edge k)
    have hb := max_le hc (hed.trans (by omega))
    have hfinal := conjoin_depth (conjoin c (edge k)) (wireBit (trackWire (dataWire k)))
    simp only [wireBit_depth, max_zero] at hfinal
    exact hfinal.trans (by omega)
  have h := reduceBank_depth (parityFamily W) (term W (m := m)) hterm
  have hp := hpar m (by omega)
  change (decoder W m).depth ≤ (10 + 4 * W.depthFactor) * L
  change (decoder W m).depth ≤ _ at h
  dsimp only [P] at h hp
  simp only [Nat.add_mul, Nat.one_mul] at h hp ⊢
  rw [Nat.mul_assoc]
  omega

end PredictionDepth.FrozenPascal.UniformDecoder
