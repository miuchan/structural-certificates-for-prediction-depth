import PredictionDepth.FrozenPascal.UniformWeightDefinitions
import PredictionDepth.FrozenPascal.UniformWeightPrimitives

/-! Regular fixed-width carry-save banks, with exact packed-value semantics. -/
namespace PredictionDepth.FrozenPascal.UniformWeight
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition

def packed {w P : ℕ} (v : Fin P → Pair w) : BitString (P * (w + w)) :=
  fun q => v (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

@[simp] theorem packed_pair {w P : ℕ} (v : Fin P → Pair w) (e : Fin P) (i : Fin (w + w)) :
    packed v (finProdFinEquiv (e, i)) = v e i := by simp [packed]

def readFlat {N : ℕ} (x : BitString N) (j : ℕ) : Bool :=
  if h : j < N then x ⟨j, h⟩ else false

theorem readFlat_block {w P : ℕ} (v : Fin P → Pair w) (e : ℕ) (i : Fin (w + w)) :
    readFlat (packed v) (e * (w + w) + i.val) = extend v e i := by
  have hB : 0 < w + w := by have := i.isLt; omega
  by_cases he : e < P
  · have hj : e * (w + w) + i.val < P * (w + w) := by have := i.isLt; nlinarith
    simp only [readFlat, dite_eq_left hj, extend, dite_eq_left he]
    have hidx : (⟨e * (w + w) + i.val, hj⟩ : Fin (P * (w + w))) =
        finProdFinEquiv (⟨e, he⟩, i) := by
      apply Fin.ext
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
    rw [hidx, packed_pair]
  · have hj : ¬e * (w + w) + i.val < P * (w + w) := by nlinarith
    simp [readFlat, extend, hj, he, zero]

def initialEntry (n w q : ℕ) : Circuit signature n 1 :=
  if h : q / (w + w) < n ∧ q % (w + w) = 0 then
    Circuit.wiring signature (fun _ => ⟨q / (w + w), h.1⟩)
  else Circuit.oneGate (.const false) Fin.elim0

def initial (n w P : ℕ) : Circuit signature n (P * (w + w)) :=
  Circuit.pi (fun q => initialEntry n w q.val)

theorem bitPair_lane (n w : ℕ) (j : Fin n) (i : Fin (w + w)) (x : BitString n) :
    (bitPairCircuit n w j).eval interpretation x i = if i.val = 0 then x j else false := by
  induction i using Fin.addCases with
  | left i =>
    by_cases h : i.val = 0 <;>
      simp [bitPairCircuit, h, interpretation, -Fin.natAdd_eq_addNat]
  | right i =>
    have hw : w ≠ 0 := by have := i.isLt; omega
    simp [bitPairCircuit, hw, interpretation, -Fin.natAdd_eq_addNat]

theorem leaves_lane (n w P : ℕ) (x : BitString n) (e : Fin P) (i : Fin (w + w)) :
    leaves n w P x e i =
      if h : e.val < n ∧ i.val = 0 then x ⟨e.val, h.1⟩ else false := by
  by_cases he : e.val < n
  · simp only [leaves, dite_eq_left he, bitPair_lane]
    by_cases hi : i.val = 0 <;> simp [he, hi]
  · simp [leaves, he, zero]

theorem initial_eval (n w P : ℕ) (x : BitString n) :
    (initial n w P).eval interpretation x = packed (leaves n w P x) := by
  funext q
  rw [initial, Circuit.eval_pi]
  simp only [packed, leaves_lane, finProdFinEquiv_symm_apply, Fin.divNat, Fin.modNat]
  unfold initialEntry
  split <;> simp [Circuit.eval_wiring, interpretation]

theorem initial_depth (n w P : ℕ) : (initial n w P).depth ≤ 1 := by
  apply Circuit.depth_pi_le
  intro q
  unfold initialEntry
  split <;> simp

/-- A pair of child blocks, with absent blocks replaced by one shared false wire. -/
def paddedInputWires (w P e : ℕ) : Fin ((w + w) + (w + w)) → Fin (P * (w + w) + 1) :=
  fun i => if h : e * ((w + w) + (w + w)) + i.val < P * (w + w) then
      Fin.castAdd 1 ⟨e * ((w + w) + (w + w)) + i.val, h⟩
    else Fin.natAdd (P * (w + w)) 0

def paddedInput (w P e : ℕ) : Circuit signature (P * (w + w)) ((w + w) + (w + w)) :=
  (Circuit.wiring signature (paddedInputWires w P e)).comp
    ((Circuit.id signature (P * (w + w))).append (Circuit.oneGate (.const false) Fin.elim0))

theorem paddedInput_eval_flat (w P e : ℕ) (x : BitString (P * (w + w)))
    (i : Fin ((w + w) + (w + w))) :
    (paddedInput w P e).eval interpretation x i =
      readFlat x (e * ((w + w) + (w + w)) + i.val) := by
  simp only [paddedInput, Circuit.eval_comp, Circuit.eval_wiring, Circuit.eval_append,
    Function.comp_apply]
  unfold paddedInputWires readFlat
  split_ifs with h
  · change Fin.append x (fun _ : Fin 1 => false)
      (Fin.castAdd 1 ⟨e * ((w + w) + (w + w)) + i.val, h⟩) = _
    exact Fin.append_left _ _ _
  · change Fin.append x (fun _ : Fin 1 => false) (Fin.natAdd (P * (w + w)) 0) = false
    exact Fin.append_right _ _ 0

theorem paddedInput_eval {w P : ℕ} (v : Fin P → Pair w) (e : ℕ) :
    (paddedInput w P e).eval interpretation (packed v) =
      Fin.append (extend v (2 * e)) (extend v (2 * e + 1)) := by
  funext i
  rw [paddedInput_eval_flat]
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    have he : e * ((w + w) + (w + w)) + (Fin.castAdd (w + w) i).val =
        (2 * e) * (w + w) + i.val := by simp; ring
    rw [he, readFlat_block]
  | right i =>
    rw [Fin.append_right]
    have he : e * ((w + w) + (w + w)) + (Fin.natAdd (w + w) i).val =
        (2 * e + 1) * (w + w) + i.val := by simp; ring
    rw [he, readFlat_block]

theorem paddedInput_depth (w P e : ℕ) : (paddedInput w P e).depth ≤ 1 := by
  apply (Circuit.depth_comp_le _ _).trans
  have h := Circuit.depth_append_le (Circuit.id signature (P * (w + w)))
    (Circuit.oneGate (σ := signature) (.const false) (n := P * (w + w)) Fin.elim0)
  simpa only [Circuit.depth_wiring, Circuit.depth_oneGate, Nat.zero_add, Nat.zero_max] using h

def mergeEntry (w P : ℕ) (q : Fin (P * (w + w))) : Circuit signature (P * (w + w)) 1 :=
  (Circuit.wiring signature (fun _ : Fin 1 => (finProdFinEquiv.symm q).2)).comp
    ((csa4to2 w).comp (paddedInput w P (finProdFinEquiv.symm q).1.val))

def mergeBank (w P : ℕ) : Circuit signature (P * (w + w)) (P * (w + w)) :=
  Circuit.pi (mergeEntry w P)

theorem mergeBank_eval (w P : ℕ) (v : Fin P → Pair w) :
    (mergeBank w P).eval interpretation (packed v) = packed (mergeValues v) := by
  funext q
  simp only [mergeBank, Circuit.eval_pi, mergeEntry, Circuit.eval_comp, Circuit.eval_wiring,
    Function.comp_apply, paddedInput_eval, packed, mergeValues, combine]

theorem mergeBank_depth (w P : ℕ) : (mergeBank w P).depth ≤ 13 := by
  apply Circuit.depth_pi_le
  intro q
  have hinner := (Circuit.depth_comp_le (csa4to2 w)
    (paddedInput w P (finProdFinEquiv.symm q).1.val)).trans
      (Nat.add_le_add (depth_csa4to2_le w) (paddedInput_depth _ _ _))
  exact (Circuit.depth_comp_le _ _).trans (by
    simpa only [Circuit.depth_wiring, Nat.zero_add] using hinner)

end PredictionDepth.FrozenPascal.UniformWeight
