import PredictionDepth.FrozenPascal.Decoder
import PredictionDepth.Complexity.CodeLogspaceFamilies
import PredictionDepth.Complexity.NCReductionUniform

/-! Composition of uniform scalar banks and their Boolean reductions. -/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open Linear (F₂)
open Turing.MultiTapeTM
open StandardComplexity
open scoped BigOperators

namespace Code

variable {α : Type} {enc : α ↪ List Bool}

theorem wiring {n m : α → ℕ} {f : ∀ a, Fin (m a) → Fin (n a)}
    {g : α × ℕ → ℕ}
    (hm : ComputableInLogSpace m enc encUnary)
    (hg : ComputableInLogSpace g (encPair enc encUnary) encNat)
    (he : ∀ a j, (f a j).val = g (a, j.val)) :
    ComputableInLogSpace (fun a => (Circuit.wiring signature (f a)).code) enc encCode := by
  exact ((ComputableInLogSpace.const ([] : List (Op × List ℕ))).pair
    (CodeLogspace.map_range hm hg)).congr_fun fun a =>
      Circuit.code_wiring_eq_map (he a)

theorem wire {n : α → ℕ} {f : ∀ a, Fin (n a)} {g : α → ℕ}
    (hg : ComputableInLogSpace g enc encNat) (he : ∀ a, (f a).val = g a) :
    ComputableInLogSpace (fun a => (wireBit (f a)).code) enc encCode := by
  apply wiring (ComputableInLogSpace.const 1)
    (hg.comp (ComputableInLogSpace.fst enc encUnary))
  intro a _
  exact he a

theorem constant {n : α → ℕ} (hn : ComputableInLogSpace n enc encUnary) (b : Bool) :
    ComputableInLogSpace (fun a => (constBit (n a) b).code) enc encCode := by
  have hg : ComputableInLogSpace (fun _ : α => ([(Op.const b, [])] : List (Op × List ℕ)))
      enc (encList encGate) := ComputableInLogSpace.const _
  exact (hg.pair (ComputableInLogSpace.listSingleton.comp hn.unaryToBinary)).congr_fun
    (fun _ => rfl)

theorem conjoin {n : α → ℕ} {c d : ∀ a, Gates (n a) 1}
    (hn : ComputableInLogSpace n enc encUnary)
    (hc : ComputableInLogSpace (fun a => (c a).code) enc encCode)
    (hd : ComputableInLogSpace (fun a => (d a).code) enc encCode) :
    ComputableInLogSpace (fun a => (FrozenPascal.conjoin (c a) (d a)).code) enc encCode :=
  CodeLogspace.circuit_comp_logspace hn (CodeLogspace.circuit_append_logspace hn hc hd)
    (ComputableInLogSpace.const andGate.code)

/-- Generate a bank from a worker defined on natural indices. Out-of-range
indices are masked by the indexed-bank constructor. -/
theorem bank {n m : α → ℕ} {c : ∀ a, ℕ → Gates (n a) 1}
    (hn : ComputableInLogSpace n enc encUnary)
    (hm : ComputableInLogSpace m enc encUnary)
    (hc : ComputableInLogSpace (fun p : α × ℕ => (c p.1 p.2).code)
      (encPair enc encUnary) encCode) :
    ComputableInLogSpace
      (fun a => (Circuit.pi (fun j : Fin (m a) => c a j.val)).code) enc encCode := by
  apply CodeLogspaceFamilies.circuit_pi_of_indexed_logspace hn hm
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  exact ((hj.unaryLt (hm.comp hp)).ite hc (ComputableInLogSpace.const ([], []))).congr_fun
    fun p => by simp only [decide_eq_true_eq, Function.comp_apply]; split_ifs <;> rfl

end Code

def negateBank (n : ℕ) : Gates n n :=
  Circuit.pi fun j => notGate.comp (wireBit j)

def allFamily (n : ℕ) : Gates n 1 :=
  notGate.comp ((UniformOROptimal.family n).comp (negateBank n))

theorem allFamily_eval (v : Bits n) :
    bit ((allFamily n).eval interpretation v 0) = ∏ j, bit (v j) := by
  have hn (j : Fin n) : (negateBank n).eval interpretation v j = !v j := by
    simp [negateBank, Circuit.eval_comp, notGate, interpretation]
  have he : (allFamily n).eval interpretation v 0 = true ↔ ∀ j, v j = true := by
    rw [allFamily, Circuit.eval_comp, Circuit.eval_comp]
    change (!((UniformOROptimal.family n).eval interpretation
      ((negateBank n).eval interpretation v) 0)) = true ↔ _
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    change (¬ ((UniformOROptimal.family n).eval interpretation
      ((negateBank n).eval interpretation v) 0 = true)) ↔ _
    rw [UniformOROptimal.family_true_iff]
    simp [hn]
  by_cases h : ∀ j, v j = true
  · rw [he.mpr h]
    simp [h]
  · have hf : ∃ j, v j = false := by
      by_contra hn
      apply h
      intro j
      cases hj : v j
      · exact False.elim (hn ⟨j, hj⟩)
      · rfl
    obtain ⟨j, hj⟩ := hf
    rw [Bool.eq_false_iff.mpr (fun ht => h (he.mp ht)), bit_false]
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm

theorem allFamily_depth (n : ℕ) :
    (allFamily n).depth ≤ 3 + Nat.clog 2 n := by
  have hneg : (negateBank n).depth ≤ 1 := by
    apply Circuit.depth_pi_le
    intro j
    exact (Circuit.depth_comp_le _ _).trans (by simp [notGate])
  have hor : (UniformOROptimal.family n).depth ≤ 1 + Nat.clog 2 n := by
    by_cases hn : 0 < n
    · exact (UniformOROptimal.family_depth n hn).trans (by omega)
    · simp [UniformOROptimal.family, hn]
  have hmid := (Circuit.depth_comp_le (UniformOROptimal.family n) (negateBank n)).trans
    (Nat.add_le_add hor hneg)
  have h := Circuit.depth_comp_le notGate ((UniformOROptimal.family n).comp (negateBank n))
  simp only [notGate, Circuit.depth_oneGate] at h
  exact h.trans (by omega)

theorem allFamily_code_logspace :
    ComputableInLogSpace (fun n => (allFamily n).code) encUnary encCode := by
  have hid : ComputableInLogSpace (fun n : ℕ => n) encUnary encUnary :=
    ComputableInLogSpace.id
  have hp := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  have hwire : ComputableInLogSpace (fun p : ℕ × ℕ => (([], [p.2]) : CodeLogspace.RawCode))
      (encPair encUnary encUnary) encCode :=
    (ComputableInLogSpace.const []).pair (ComputableInLogSpace.listSingleton.comp hj.unaryToBinary)
  have hnot : ComputableInLogSpace (fun _ : ℕ × ℕ => notGate.code)
      (encPair encUnary encUnary) encCode := ComputableInLogSpace.const _
  have hlocal := CodeLogspace.compCode_logspace hp hnot hwire
    (fun p => by simp [CodeLogspace.BoundedReferences, notGate, Circuit.oneGate, Circuit.code,
      Program.code, Line.code, Wire.toNat])
  have hbank : ComputableInLogSpace (fun n => (negateBank n).code) encUnary encCode := by
    apply CodeLogspaceFamilies.circuit_pi_of_indexed_logspace hid hid
    refine ((hj.unaryLt hp).ite hlocal (ComputableInLogSpace.const ([], []))).congr_fun ?_
    intro p
    simp only [decide_eq_true_eq]
    split_ifs
    · rw [← compCode_code, wireBit, Circuit.code_wiring]
      rfl
    · rfl
  exact CodeLogspace.circuit_comp_logspace hid
    (CodeLogspace.circuit_comp_logspace hid hbank UniformOROptimal.family_code_logspace)
    (ComputableInLogSpace.const notGate.code)

/-- A weight primitive with an actual unary-indexed generator. The numerical
semantics fixes the bit order independently of the chosen circuit layout. -/
structure WeightBasis where
  circuit : ∀ n, Gates n (Nat.clog 2 (n + 1))
  value : ∀ n (x : Bits n),
    (BitString.equivFin _ ((circuit n).eval interpretation x)).val = BitString.weight x
  depthFactor : ℕ
  depth : ∀ n, (circuit n).depth ≤ depthFactor * (Nat.clog 2 (n + 1) + 1)
  uniform : ComputableInLogSpace (fun n => (circuit n).code) encUnary encCode

private theorem bit_toNat (b : Bool) : (b.toNat : F₂) = bit b := by cases b <;> rfl

private theorem bit_low (v : Bits (w + 1)) :
    bit (v 0) = ((BitString.equivFin (w + 1) v).val : F₂) := by
  have hz : (2 : F₂) = 0 := rfl
  rw [BitString.val_equivFin_eq_sum, Nat.cast_sum, Fin.sum_univ_succ]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Fin.val_zero, pow_zero, mul_one, bit_toNat]
  have he (j : Fin w) : (2 : F₂) ^ (j.val + 1) = 0 := by
    rw [hz]
    exact zero_pow (Nat.succ_ne_zero _)
  simp [he]

def parityFamily (W : WeightBasis) (n : ℕ) : Gates n 1 :=
  if hn : 0 < n then
    (wireBit (⟨0, Nat.clog_pos (by decide : 1 < (2 : ℕ)) (by omega)⟩ :
      Fin (Nat.clog 2 (n + 1)))).comp (W.circuit n)
  else constBit n false

theorem parityFamily_eval (W : WeightBasis) (v : Bits n) :
    bit ((parityFamily W n).eval interpretation v 0) = ∑ j, bit (v j) := by
  unfold parityFamily
  split_ifs with hn
  · rw [Circuit.eval_comp, wireBit_eval]
    have he (k : ℕ) (hk : 0 < k) (u : Bits k) :
        bit (u ⟨0, hk⟩) = ((BitString.equivFin k u).val : F₂) := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact bit_low u
    rw [he, W.value, BitString.weight_eq_sum_toNat, Nat.cast_sum]
    simp only [bit_toNat]
  · have : n = 0 := by omega
    subst n
    simp

theorem parityFamily_depth (W : WeightBasis) (n : ℕ) :
    (parityFamily W n).depth ≤ (W.depthFactor + 1) * (Nat.clog 2 (n + 1) + 1) := by
  unfold parityFamily
  split_ifs
  · apply (Circuit.depth_comp_le _ _).trans
    simp only [wireBit_depth, zero_add]
    exact (W.depth n).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
  · simp only [constBit_depth, Nat.add_mul, one_mul]
    omega

theorem parityFamily_code_logspace (W : WeightBasis) :
    ComputableInLogSpace (fun n => (parityFamily W n).code) encUnary encCode := by
  have hid : ComputableInLogSpace (fun n : ℕ => n) encUnary encUnary := ComputableInLogSpace.id
  have hz : ComputableInLogSpace (fun _ : ℕ => (([], [0]) : CodeLogspace.RawCode))
      encUnary encCode := ComputableInLogSpace.const _
  have hp := CodeLogspace.compCode_logspace hid hz W.uniform
    (fun _ => by simp [CodeLogspace.BoundedReferences])
  have ht := (ComputableInLogSpace.const (0 : ℕ) (encIn := encUnary)).unaryLt hid
  exact (ht.ite hp (Code.constant hid false)).congr_fun fun n => by
    simp only [decide_eq_true_eq, parityFamily]
    split_ifs
    · rw [← compCode_code, wireBit, Circuit.code_wiring]
      rfl
    · rfl

def reduceBank (F : BooleanCircuitFamily) (cs : Fin m → Gates n 1) : Gates n 1 :=
  (F m).comp (Circuit.pi cs)

theorem allBank_eval (cs : Fin m → Gates n 1) (x : Bits n) :
    (reduceBank allFamily cs).eval interpretation x 0 =
      (conjunction (List.ofFn cs)).eval interpretation x 0 := by
  apply bit_injective
  rw [reduceBank, Circuit.eval_comp, allFamily_eval, conjunction_eval_fin]
  simp only [Circuit.eval_pi]

theorem parityBank_eval (W : WeightBasis) (cs : Fin m → Gates n 1) (x : Bits n) :
    (reduceBank (parityFamily W) cs).eval interpretation x 0 =
      (parity (List.ofFn cs)).eval interpretation x 0 := by
  apply bit_injective
  rw [reduceBank, Circuit.eval_comp, parityFamily_eval, parity_eval_fin]
  simp only [Circuit.eval_pi]

theorem reduceBank_depth (F : BooleanCircuitFamily) (cs : Fin m → Gates n 1) {D : ℕ}
    (hd : ∀ j, (cs j).depth ≤ D) : (reduceBank F cs).depth ≤ (F m).depth + D :=
  (Circuit.depth_comp_le _ _).trans (Nat.add_le_add_left (Circuit.depth_pi_le _ hd) _)

theorem Code.reduceBank {α : Type} {enc : α ↪ List Bool} {F : BooleanCircuitFamily}
    {n m : α → ℕ} {c : ∀ a, ℕ → Gates (n a) 1}
    (hF : ComputableInLogSpace (fun n => (F n).code) encUnary encCode)
    (hn : ComputableInLogSpace n enc encUnary)
    (hm : ComputableInLogSpace m enc encUnary)
    (hc : ComputableInLogSpace (fun p : α × ℕ => (c p.1 p.2).code)
      (encPair enc encUnary) encCode) :
    ComputableInLogSpace
      (fun a => (FrozenPascal.reduceBank F (fun j : Fin (m a) => c a j.val)).code) enc encCode :=
  CodeLogspace.circuit_comp_logspace hn (Code.bank hn hm hc) (hF.comp hm)

end PredictionDepth.FrozenPascal
