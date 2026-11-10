import PredictionDepth.Complexity.BlockSummary
import PredictionDepth.FrozenPascal.BooleanCircuits

/-! Logspace-uniform balanced reductions over single Boolean bits. -/

namespace PredictionDepth.SparseCorrections.BooleanReduction

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition (Bits)
open FrozenPascal (Gates wireBit constBit andGate xorGate)
open StandardComplexity CodeLogspace CodeLogspaceFamilies Turing.MultiTapeTM

def orGate : Gates 2 1 := Circuit.oneGate (σ := signature) .or id

@[simp] theorem orGate_eval (x : Bits 2) :
    orGate.eval interpretation x 0 = (x 0 || x 1) := rfl
@[simp] theorem orGate_depth : orGate.depth = 1 := Circuit.depth_oneGate _ _
@[simp] theorem orGate_size : orGate.size = 1 := rfl

private def initialEntry (neutral : Bool) (m : ℕ) (j : Fin (BlockSummary.paddedCount m * 1)) :
    Gates m 1 :=
  if h : j.val < m then wireBit ⟨j.val, h⟩ else constBit m neutral

private def initial (neutral : Bool) (m : ℕ) : Gates m (BlockSummary.paddedCount m * 1) :=
  Circuit.pi (initialEntry neutral m)

private def emptyCircuit (m : ℕ) : Gates m 0 := Circuit.wiring signature Fin.elim0

def reduce (merge : Gates 2 1) (neutral : Bool) (m : ℕ) : Gates m 1 :=
  BlockSummary.compile merge (BlockSummary.paddingDepth m) (initial neutral m)
    (emptyCircuit m) (Circuit.id signature 1)

structure BoolLaws (op : Bool → Bool → Bool) (neutral : Bool) : Prop where
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
  leftId : ∀ a, op neutral a = a
  rightId : ∀ a, op a neutral = a

private theorem combine_apply (merge : Gates 2 1) {op : Bool → Bool → Bool}
    (hmerge : ∀ x, merge.eval interpretation x 0 = op (x 0) (x 1)) (a b : Bits 1) :
    BlockSummary.combine merge a b 0 = op (a 0) (b 0) := by
  rw [BlockSummary.combine, hmerge]
  rfl

private theorem summarize_apply (merge : Gates 2 1) (neutral : Bool)
    {op : Bool → Bool → Bool}
    (hmerge : ∀ x, merge.eval interpretation x 0 = op (x 0) (x 1))
    (l : List (Bits 1)) :
    BlockSummary.summarize (BlockSummary.combine merge) (fun _ => neutral) l 0 =
      (l.map fun a => a 0).foldr op neutral := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [BlockSummary.summarize, List.foldr_cons, combine_apply merge hmerge,
      List.map_cons, List.foldr_cons, ← ih]; rfl

theorem reduce_eval (merge : Gates 2 1) (neutral : Bool) (x : Bits m)
    {op : Bool → Bool → Bool} (laws : BoolLaws op neutral)
    (hmerge : ∀ x, merge.eval interpretation x 0 = op (x 0) (x 1)) :
    (reduce merge neutral m).eval interpretation x 0 = (List.ofFn x).foldr op neutral := by
  have h : BlockSummary.Laws (BlockSummary.combine (w := 1) merge) (fun _ => neutral) := by
    constructor
    · intro a b c
      funext i
      rw [Fin.eq_zero i]
      simp only [combine_apply merge hmerge, laws.assoc]
    · intro a
      funext i
      rw [Fin.eq_zero i, combine_apply merge hmerge, laws.leftId]
    · intro a
      funext i
      rw [Fin.eq_zero i, combine_apply merge hmerge, laws.rightId]
  unfold reduce
  refine (congrFun (BlockSummary.compile_eval (w := 1) (k := 0) merge h
    (BlockSummary.paddingDepth m) (initial neutral m) (emptyCircuit m)
    (Circuit.id signature 1) x) 0).trans ?_
  change BlockSummary.summarize (BlockSummary.combine (w := 1) merge) (fun _ => neutral)
    (List.ofFn (BlockSummary.unpack ((initial neutral m).eval interpretation x))) 0 = _
  have hinit : BlockSummary.unpack ((initial neutral m).eval interpretation x) =
      (fun j : Fin (BlockSummary.paddedCount m) =>
        if hj : j.val < m then (fun _ => x ⟨j.val, hj⟩) else (fun _ => neutral)) := by
    funext j i
    rw [Fin.eq_zero i]
    by_cases hj : j.val < m <;> simp [BlockSummary.unpack, initial, initialEntry, hj]
  rw [hinit]
  refine (congrFun (BlockSummary.summarize_pad_le h (fun j _ => x j)
    (BlockSummary.le_paddedCount m)) 0).trans ?_
  rw [summarize_apply merge neutral hmerge, List.map_ofFn]
  rfl

theorem reduce_depth (merge : Gates 2 1) (neutral : Bool) (m : ℕ) :
    (reduce merge neutral m).depth ≤ 2 + Nat.clog 2 m * (merge.depth + 1) := by
  have hi : (initial neutral m).depth ≤ 1 := by
    apply Circuit.depth_pi_le
    intro j
    unfold initialEntry
    split <;> simp
  have h := BlockSummary.compile_depth merge (BlockSummary.paddingDepth m)
    (initial neutral m) (emptyCircuit m) (Circuit.id signature 1)
  simp only [BlockSummary.paddingDepth_eq_clog, Circuit.id, Nat.add_zero,
    emptyCircuit, Circuit.depth_wiring, Nat.max_eq_left (Nat.zero_le _)] at h
  exact h.trans (Nat.add_le_add_right (Nat.add_le_add_right hi 1) _)

theorem reduce_size (merge : Gates 2 1) (neutral : Bool) (m : ℕ) :
    (reduce merge neutral m).size ≤ 2 * (m + 1) * (merge.size + 3) := by
  have hi : (initial neutral m).size ≤ BlockSummary.paddedCount m := by
    rw [initial, Circuit.size_pi]
    calc
      _ ≤ ∑ _ : Fin (BlockSummary.paddedCount m * 1), 1 := by
        apply Finset.sum_le_sum
        intro j _
        unfold initialEntry
        split <;> simp
      _ = _ := by simp
  have h := BlockSummary.compile_size merge (BlockSummary.paddingDepth m)
    (initial neutral m) (emptyCircuit m) (Circuit.id signature 1)
  simp only [Nat.mul_one, Nat.one_mul, emptyCircuit, Circuit.size_wiring, Circuit.id,
    Nat.add_zero] at h
  apply h.trans
  let P := BlockSummary.paddedCount m
  change (initial neutral m).size + P + (P - 1) * (merge.size + 1) ≤ _
  have h₁ := Nat.mul_le_mul_right (merge.size + 1) (Nat.sub_le P 1)
  have h₂ := Nat.mul_le_mul_right (merge.size + 3) (BlockSummary.paddedCount_le m)
  change P * (merge.size + 3) ≤ _ at h₂
  apply le_trans _ h₂
  calc
    _ ≤ P + P + P * (merge.size + 1) := by omega
    _ = P * (merge.size + 3) := by ring

set_option maxHeartbeats 600000 in
theorem reduce_code_logspace (merge : Gates 2 1) (neutral : Bool) :
    ComputableInLogSpace (fun m => (reduce merge neutral m).code) encUnary encCode := by
  have hp := BlockSummary.paddedCount_logspace
  have hm : ComputableInLogSpace (fun m : ℕ => m) encUnary encUnary := ComputableInLogSpace.id
  have hinit : ComputableInLogSpace (fun m => (initial neutral m).code) encUnary encCode := by
    apply circuit_pi_of_indexed_logspace hm (hp.unaryMulConst 1)
    have hx := ComputableInLogSpace.fst encUnary encUnary
    have hj := ComputableInLogSpace.snd encUnary encUnary
    have hwire : ComputableInLogSpace (fun p : ℕ × ℕ => (([], [p.2]) : RawCode))
        (encPair encUnary encUnary) encCode :=
      (ComputableInLogSpace.const []).pair (ComputableInLogSpace.listSingleton.comp hj.unaryToBinary)
    have hconst : ComputableInLogSpace
        (fun p : ℕ × ℕ => (([(Op.const neutral, [])], [p.1]) : RawCode))
        (encPair encUnary encUnary) encCode :=
      (ComputableInLogSpace.const _).pair (ComputableInLogSpace.listSingleton.comp hx.unaryToBinary)
    refine ((hj.unaryLt ((hp.unaryMulConst 1).comp hx)).ite
      ((hj.unaryLt hx).ite hwire hconst)
      (ComputableInLogSpace.const ([], []))).congr_fun ?_
    intro p
    simp only [decide_eq_true_eq, Function.comp_apply]
    split_ifs with hpad hj'
    · rw [initialEntry, dite_eq_left hj']; rfl
    · rw [initialEntry, dite_eq_right hj']; cases neutral <;> rfl
    · rfl
  exact BlockSummary.compile_code_logspace (w := 1) (k := 0) merge (Circuit.id signature 1)
    (initial := initial neutral) (context := emptyCircuit)
    hm BlockSummary.paddingDepth_logspace hp hinit (ComputableInLogSpace.const ([], []))

def andReduce (m : ℕ) : Gates m 1 := reduce andGate true m
def orReduce (m : ℕ) : Gates m 1 := reduce orGate false m
def xorReduce (m : ℕ) : Gates m 1 := reduce xorGate false m

theorem andReduce_true_iff (x : Bits m) :
    (andReduce m).eval interpretation x 0 = true ↔ ∀ i, x i = true := by
  rw [andReduce, reduce_eval andGate true x
    ⟨Bool.and_assoc, Bool.true_and, Bool.and_true⟩ FrozenPascal.andGate_eval]
  have aux (l : List Bool) : l.foldr (· && ·) true = true ↔ ∀ b ∈ l, b = true := by
    induction l <;> simp [*]
  simp [aux]

theorem orReduce_true_iff (x : Bits m) :
    (orReduce m).eval interpretation x 0 = true ↔ ∃ i, x i = true := by
  rw [orReduce, reduce_eval orGate false x
    ⟨Bool.or_assoc, Bool.false_or, Bool.or_false⟩ orGate_eval]
  have aux (l : List Bool) : l.foldr (· || ·) false = true ↔ ∃ b ∈ l, b = true := by
    induction l <;> simp [*]
  simp [aux]

theorem xorReduce_eval (x : Bits m) :
    (xorReduce m).eval interpretation x 0 = (List.ofFn x).foldr (· ^^ ·) false :=
  reduce_eval xorGate false x ⟨Bool.xor_assoc, Bool.false_xor, Bool.xor_false⟩
    FrozenPascal.xorGate_eval

end PredictionDepth.SparseCorrections.BooleanReduction
