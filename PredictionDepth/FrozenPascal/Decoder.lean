import PredictionDepth.FrozenPascal.BooleanCircuits

/-!
# Logarithmic-depth decoding

A register has one time tag per possible exponent and three bit tracks. For
each displacement, one carry-save circuit counts the enabled stays in the
prefix. A Boolean table reads that count and the time tag. A product reads
the enabled edges, and a final balanced parity circuit adds all contributions.
-/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open Linear (F₂)
open scoped BigOperators

abbrev InputWidth (m : ℕ) := m + (m + m)
abbrev RegisterWidth (m : ℕ) := m + InputWidth m

def stayWire (j : Fin m) : Fin (InputWidth m) := Fin.castAdd (m + m) j
def hopWire (j : Fin m) : Fin (InputWidth m) := Fin.natAdd m (Fin.castAdd m j)
def dataWire (j : Fin m) : Fin (InputWidth m) := Fin.natAdd m (Fin.natAdd m j)
def timeWire (j : Fin m) : Fin (RegisterWidth m) := Fin.castAdd (InputWidth m) j
def trackWire (j : Fin (InputWidth m)) : Fin (RegisterWidth m) := Fin.natAdd m j

def timeTag (m u : ℕ) : Bits m := fun j => decide (j.val = u)

def register (m u : ℕ) (x : Bits (InputWidth m)) : Bits (RegisterWidth m) :=
  joinBits (timeTag m u) x

@[simp] theorem register_time (x : Bits (InputWidth m)) (j : Fin m) :
    register m u x (timeWire j) = decide (j.val = u) := by
  simp [register, timeWire, timeTag]

@[simp] theorem register_track (x : Bits (InputWidth m)) (j : Fin (InputWidth m)) :
    register m u x (trackWire j) = x j := by
  simp [register, trackWire]

def notGate : Gates 1 1 := Circuit.oneGate (σ := signature) .not id

def matchingBit (i : Fin w) (b : Bool) : Gates w 1 :=
  if b then wireBit i else notGate.comp (wireBit i)

@[simp] theorem matchingBit_eval (i : Fin w) (b : Bool) (x : Bits w) :
    (matchingBit i b).eval interpretation x 0 = decide (x i = b) := by
  cases b <;> cases h : x i <;> simp [matchingBit, notGate, interpretation, h]

def matchWord (v : Bits w) : Gates w 1 :=
  conjunction (List.ofFn fun j => matchingBit j (v j))

theorem matchWord_bit (v x : Bits w) :
    bit ((matchWord v).eval interpretation x 0) = if x = v then 1 else 0 := by
  rw [matchWord, conjunction_eval_fin]
  simp only [matchingBit_eval]
  by_cases h : x = v
  · subst x
    simp
  · have hdiff : ∃ j, x j ≠ v j := by
      by_contra hn
      apply h
      funext j
      by_contra hj
      exact hn ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hdiff
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

abbrev countWidth (k : ℕ) : ℕ := Nat.clog 2 (k + 2)

def countWord (s : Fin (k + 2)) : Bits (countWidth k) :=
  (BitString.equivFin (countWidth k)).symm
    (Fin.castLE (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (k + 2)) s)

theorem countWord_eq_iff (s : Fin (k + 2)) (x : Bits (countWidth k)) :
    x = countWord s ↔ (BitString.equivFin (countWidth k) x).val = s.val := by
  rw [countWord, Equiv.eq_symm_apply]
  exact Fin.ext_iff

def tableBit (u k s : ℕ) : Bool :=
  if k ≤ u then ofBoolRing (Nat.multichoose s (u - k) : F₂) else false

def row (u : Fin m) (k : ℕ) (s : Fin (k + 2)) : Gates (m + countWidth k) 1 :=
  if tableBit u.val k s.val then
    conjoin (wireBit (Fin.castAdd (countWidth k) u))
      ((matchWord (countWord s)).comp (Circuit.wiring signature (Fin.natAdd m)))
  else constBit _ false

theorem row_eval (u : Fin m) (k : ℕ) (s : Fin (k + 2))
    (tag : Bits m) (v : Bits (countWidth k)) :
    bit ((row u k s).eval interpretation (joinBits tag v) 0) =
      bit (tag u) * (if (BitString.equivFin (countWidth k) v).val = s.val then 1 else 0) *
        bit (tableBit u.val k s.val) := by
  cases h : tableBit u.val k s.val
  · simp [row, h]
  · simp only [row, h, ↓reduceIte, conjoin_eval, wireBit_eval, joinBits_left, bit_and,
      Circuit.eval_comp, Circuit.eval_wiring, bit_true, mul_one]
    have he : joinBits tag v ∘ Fin.natAdd m = v := by
      funext j
      simp
    rw [he, matchWord_bit]
    simp only [countWord_eq_iff]

def lookup (m k : ℕ) : Gates (m + countWidth k) 1 :=
  parity (List.ofFn fun u : Fin m => parity (List.ofFn (row u k)))

theorem lookup_eval (u : Fin m) (k : ℕ) (s : Fin (k + 2))
    (v : Bits (countWidth k)) (hv : (BitString.equivFin (countWidth k) v).val = s.val) :
    bit ((lookup m k).eval interpretation (joinBits (timeTag m u.val) v) 0) =
      bit (tableBit u.val k s.val) := by
  rw [lookup, parity_eval_fin]
  simp only [parity_eval_fin, row_eval, hv, timeTag]
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single s]
    · simp
    · intro j _ hj
      have hne : s.val ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp [hne]
    · simp
  · intro j _ hj
    have hne : j.val ≠ u.val := fun h => hj (Fin.ext h)
    simp [hne]
  · simp

def countInputs (k : Fin m) : Fin (k.val + 1) → Fin (RegisterWidth m) :=
  fun j => trackWire (stayWire (Fin.castLE k.isLt j))

def count (k : Fin m) : Gates (RegisterWidth m) (countWidth k.val) :=
  (weightCircuit (k.val + 1)).comp (Circuit.wiring signature (countInputs k))

def lookupInputs (k : Fin m) : Gates (RegisterWidth m) (m + countWidth k.val) :=
  (Circuit.wiring signature timeWire).append (count k)

def edge (k : Fin m) : Gates (RegisterWidth m) 1 :=
  conjunction (List.ofFn fun j : Fin k.val =>
    wireBit (trackWire (hopWire (Fin.castLE k.isLt.le j))))

def term (k : Fin m) : Gates (RegisterWidth m) 1 :=
  conjoin (conjoin ((lookup m k.val).comp (lookupInputs k)) (edge k))
    (wireBit (trackWire (dataWire k)))

def decoder (m : ℕ) : Gates (RegisterWidth m) 1 :=
  parity (List.ofFn (term (m := m)))

def extendTrack (track : Fin m → Bool) (i : ℤ) : Bool :=
  if h : 0 ≤ i ∧ i < (m : ℤ) then track ⟨i.toNat, by omega⟩ else false

@[simp] theorem extendTrack_fin (track : Fin m → Bool) (j : Fin m) :
    extendTrack track (j.val : ℤ) = track j := by
  simp [extendTrack, show (j.val : ℤ) < (m : ℤ) by omega]

def initial (x : Bits (InputWidth m)) : Config (Bool × Bool) :=
  (fun i => (extendTrack (x ∘ stayWire) i, extendTrack (x ∘ hopWire) i),
    fun i => bit (extendTrack (x ∘ dataWire) i))

theorem enabled_sum (stay : Q → Bool) (a : ℤ → Q) (i : ℤ) (k : ℕ) :
    enabled stay a i k = ∑ j ∈ Finset.range (k + 1), (stay (a (i + j))).toNat := by
  induction k generalizing i with
  | zero => simp [enabled]
  | succ k ih =>
    rw [enabled, ih, Finset.sum_range_succ'
      (f := fun j : ℕ => (stay (a (i + j))).toNat) (n := k + 1)]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    have h (j : ℕ) : i + 1 + (j : ℤ) = i + ((j : ℤ) + 1) := by omega
    simp only [h]
    omega

theorem edgeProduct_prod (hop : Q → Bool) (a : ℤ → Q) (i : ℤ) (k : ℕ) :
    edgeProduct hop a i k = ∏ j ∈ Finset.range k, bit (hop (a (i + j))) := by
  induction k generalizing i with
  | zero => simp [edgeProduct]
  | succ k ih =>
    rw [edgeProduct, ih, Finset.prod_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    have h (j : ℕ) : i + 1 + (j : ℤ) = i + ((j : ℤ) + 1) := by omega
    simp only [h]
    ac_rfl

theorem count_eval (x : Bits (InputWidth m)) (u : ℕ) (k : Fin m) :
    (BitString.equivFin (countWidth k.val)
      ((count k).eval interpretation (register m u x))).val =
      enabled Prod.fst (initial x).1 0 k.val := by
  rw [count, Circuit.eval_comp, val_eval_weightCircuit, enabled_sum,
    BitString.weight_eq_sum_toNat, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have he := extendTrack_fin (x ∘ stayWire) (Fin.castLE k.isLt j)
  simpa only [initial, countInputs, Circuit.eval_wiring, Function.comp_apply,
    register_track, zero_add, Fin.val_castLE] using congrArg Bool.toNat he.symm

theorem edge_eval (x : Bits (InputWidth m)) (u : ℕ) (k : Fin m) :
    bit ((edge k).eval interpretation (register m u x) 0) =
      edgeProduct Prod.snd (initial x).1 0 k.val := by
  rw [edge, conjunction_eval_fin, edgeProduct_prod, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  have he := extendTrack_fin (x ∘ hopWire) (Fin.castLE k.isLt.le j)
  simpa only [initial, wireBit_eval, register_track, Function.comp_apply,
    zero_add, Fin.val_castLE] using congrArg bit he.symm

theorem term_eval (x : Bits (InputWidth m)) (u k : Fin m) :
    bit ((term k).eval interpretation (register m u.val x) 0) =
      coefficient Prod.fst Prod.snd (initial x).1 0 u.val k.val * (initial x).2 k.val := by
  let s : Fin (k.val + 2) := ⟨enabled Prod.fst (initial x).1 0 k.val,
    Nat.lt_succ_of_le (enabled_le _ _ _ _)⟩
  have hl : (lookupInputs k).eval interpretation (register m u.val x) =
      joinBits (timeTag m u.val) ((count k).eval interpretation (register m u.val x)) := by
    rw [lookupInputs, Circuit.eval_append, Circuit.eval_wiring]
    have he : register m u.val x ∘ timeWire = timeTag m u.val := by
      funext j
      simp [timeTag]
    rw [he]
    rfl
  rw [term, conjoin_eval, conjoin_eval, bit_and, bit_and, Circuit.eval_comp, hl,
    lookup_eval u k.val s _ (count_eval x u.val k), edge_eval, wireBit_eval, register_track]
  unfold coefficient
  dsimp [s, tableBit]
  split_ifs with h
  · rw [bit_ofBoolRing]
    simp only [initial, extendTrack_fin]
    ac_rfl
  · simp

theorem decoder_eval (x : Bits (InputWidth m)) (u : Fin m) :
    bit ((decoder m).eval interpretation (register m u.val x) 0) =
      ((step Prod.fst Prod.snd)^[u.val] (initial x)).2 0 := by
  rw [decoder, parity_eval_fin, iterate_data]
  simp only [term_eval, zero_add]
  rw [show (∑ j : Fin m, coefficient Prod.fst Prod.snd (initial x).1 0 u.val j.val *
      (initial x).2 (j.val : ℤ)) =
    (∑ j ∈ Finset.range m, coefficient Prod.fst Prod.snd (initial x).1 0 u.val j *
      (initial x).2 (j : ℤ)) from Fin.sum_univ_eq_sum_range
        (fun j : ℕ => coefficient Prod.fst Prod.snd (initial x).1 0 u.val j * (initial x).2 (j : ℤ)) m]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hku
  rw [Finset.mem_range] at hk
  simp only [Finset.mem_range] at hku
  simp [coefficient_of_lt Prod.fst Prod.snd (initial x).1 0 (show u.val < k by omega)]

end PredictionDepth.FrozenPascal
