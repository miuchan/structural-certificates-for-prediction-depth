import PredictionDepth.SparseCorrections.Reduction
import PredictionDepth.FrozenPascal.UniformReducers

/-!
# Uniform linear response from an indexed coefficient table

Each row is a parity of selected inputs. The coefficient routine is used by
the circuit generator; it contributes no gates to the evaluated circuit.
-/

namespace PredictionDepth.SparseCorrections.LinearResponse

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity Turing.MultiTapeTM
open FrozenPascal (Gates wireBit constBit xorGate reduceBank)

def term (n : ℕ) (selected : Bool) (j : ℕ) : Gates n 1 :=
  if h : j < n then
    if selected then wireBit ⟨j, h⟩ else constBit n false
  else constBit n false

def row (n : ℕ) (coefficient : ℕ → Bool) : Gates n 1 :=
  reduceBank (BooleanReduction.xorReduce) (fun j : Fin n => term n (coefficient j) j)

def circuit (n V : ℕ) (coefficient : ℕ → ℕ → Bool) : Gates n V :=
  Circuit.pi fun i => row n (coefficient i)

@[simp] theorem term_eval (n : ℕ) (x : Fin n → Bool) (selected : Bool) (j : Fin n) :
    (term n selected j).eval interpretation x 0 = (selected && x j) := by
  cases selected <;> simp [term, j.isLt]

theorem circuit_eval (n V : ℕ) (coefficient : ℕ → ℕ → Bool) (x : Fin n → Bool) (i : Fin V) :
    (circuit n V coefficient).eval interpretation x i =
      (List.ofFn (fun j : Fin n => coefficient i j && x j)).foldr (· ^^ ·) false := by
  simp only [circuit, Circuit.eval_pi, row, reduceBank, Circuit.eval_comp,
    BooleanReduction.xorReduce_eval, term_eval]

theorem circuit_depth (n V : ℕ) (coefficient : ℕ → ℕ → Bool) :
    (circuit n V coefficient).depth ≤ 3 + Nat.clog 2 n * (xorGate.depth + 1) := by
  apply Circuit.depth_pi_le
  intro i
  have hrow := FrozenPascal.reduceBank_depth BooleanReduction.xorReduce
    (fun j : Fin n => term n (coefficient i j) j) (D := 1) (fun j => by
      unfold term
      split_ifs <;> simp)
  exact hrow.trans (by
    have h := BooleanReduction.reduce_depth xorGate false n
    unfold BooleanReduction.xorReduce
    omega)

theorem circuit_size (n V : ℕ) (coefficient : ℕ → ℕ → Bool) :
    (circuit n V coefficient).size ≤ V * (2 * (n + 1) * (xorGate.size + 3) + n) := by
  rw [circuit, Circuit.size_pi]
  calc
    _ ≤ ∑ _ : Fin V, (2 * (n + 1) * (xorGate.size + 3) + n) := by
      apply Finset.sum_le_sum
      intro i _
      rw [row, reduceBank, Circuit.size_comp, Circuit.size_pi]
      have hterm : (∑ j : Fin n, (term n (coefficient i j) j).size) ≤ n := by
        calc
          _ ≤ ∑ _ : Fin n, 1 := by
            apply Finset.sum_le_sum
            intro j _
            unfold term
            split_ifs <;> simp
          _ = _ := by simp
      exact Nat.add_le_add hterm (BooleanReduction.reduce_size xorGate false n) |>.trans
        (by omega)
    _ = _ := by simp [Nat.mul_comm]

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
theorem circuit_code_logspace {α : Type} {enc : α ↪ List Bool} {n V : α → ℕ}
    {coefficient : α → ℕ → ℕ → Bool}
    (hn : ComputableInLogSpace n enc encUnary) (hV : ComputableInLogSpace V enc encUnary)
    (hcoeff : ComputableInLogSpace (fun p : (α × ℕ) × ℕ => coefficient p.1.1 p.1.2 p.2)
      (encPair (encPair enc encUnary) encUnary) encBool) :
    ComputableInLogSpace (fun a => (circuit (n a) (V a) (coefficient a)).code)
      enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hq := ComputableInLogSpace.fst (encPair enc encUnary) encUnary
  have hj := ComputableInLogSpace.snd (encPair enc encUnary) encUnary
  have hw : ComputableInLogSpace (fun p : (α × ℕ) × ℕ => (([], [p.2]) : CodeLogspace.RawCode))
      (encPair (encPair enc encUnary) encUnary) encCode :=
    (ComputableInLogSpace.const []).pair (ComputableInLogSpace.listSingleton.comp hj.unaryToBinary)
  have hin := hn.comp hp
  have ht : ComputableInLogSpace (fun p : (α × ℕ) × ℕ =>
      (term (n p.1.1) (coefficient p.1.1 p.1.2 p.2) p.2).code)
      (encPair (encPair enc encUnary) encUnary) encCode := by
    have ht := ((hj.unaryLt (hin.comp hq)).bool_and hcoeff).ite hw
      (FrozenPascal.Code.constant (hin.comp hq) false)
    refine ht.congr_fun ?_
    intro p
    change (term (n p.1.1) (coefficient p.1.1 p.1.2 p.2) p.2).code =
      if decide (p.2 < n p.1.1) && coefficient p.1.1 p.1.2 p.2
      then ([], [p.2]) else (constBit (n p.1.1) false).code
    by_cases h : p.2 < n p.1.1
    · rw [term, dite_eq_left h]
      simp only [h, decide_true, Bool.true_and]
      cases coefficient p.1.1 p.1.2 p.2 <;> rfl
    · rw [term, dite_eq_right h]
      simp [h]
  have hxor : ComputableInLogSpace (fun k => (BooleanReduction.xorReduce k).code)
      encUnary encCode := by
    unfold BooleanReduction.xorReduce
    exact BooleanReduction.reduce_code_logspace xorGate false
  have hrow : ComputableInLogSpace (fun p : α × ℕ => (row (n p.1) (coefficient p.1 p.2)).code)
      (encPair enc encUnary) encCode := by
    unfold row
    exact FrozenPascal.Code.reduceBank
      (enc := encPair enc encUnary) (F := BooleanReduction.xorReduce)
      (n := fun p => n p.1) (m := fun p => n p.1)
      (c := fun p j => term (n p.1) (coefficient p.1 p.2 j) j)
      hxor hin hin ht
  unfold circuit
  exact FrozenPascal.Code.bank (c := fun a i => row (n a) (coefficient a i)) hn hV hrow

end PredictionDepth.SparseCorrections.LinearResponse
