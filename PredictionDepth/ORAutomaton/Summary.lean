import PredictionDepth.ORAutomaton
import PredictionDepth.Complexity.UniformOROptimal
import PredictionDepth.Complexity.BlockSummary

/-! One-bit ordered summaries for the existing radius-one OR automaton. -/

namespace PredictionDepth.ORAutomaton

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity Turing.MultiTapeTM
open StandardComplexity.CodeLogspace

def summaryMerge (left right : Fin 1 → Bool) : Fin 1 → Bool :=
  fun _ => left 0 || right 0

def summaryEmpty : Fin 1 → Bool := fun _ => false

private def summaryBit (b : Bool) : Fin 1 → Bool := fun _ => b

/-- Recognize the one-bit template from the local OR evaluator. -/
def recognizeSummary :=
  BlockSummary.recognize? (· || ·) false summaryBit summaryBit id (fun x => x 0)
    summaryMerge summaryEmpty

theorem summary_recognized : recognizeSummary.isSome = true := by
  decide

theorem summaryLaws : BlockSummary.Laws summaryMerge summaryEmpty :=
  (recognizeSummary.get summary_recognized).down.1

def summaryMergeCircuit : Circuit signature 2 1 :=
  Circuit.oneGate .or id

theorem summaryMergeCircuit_eval (left right : Fin 1 → Bool) :
    summaryMergeCircuit.eval interpretation (Fin.append left right) =
      summaryMerge left right := by
  funext i
  rw [Fin.eq_zero i]
  rfl

private theorem summarize_true_iff (leaves : List (Fin 1 → Bool)) :
    BlockSummary.summarize summaryMerge summaryEmpty leaves 0 = true ↔
      ∃ leaf ∈ leaves, leaf 0 = true := by
  have hl : (leaves.map (fun leaf => leaf 0)).map summaryBit = leaves := by
    rw [List.map_map]
    have h : summaryBit ∘ (fun (leaf : Fin 1 → Bool) => leaf 0) = id := by
      funext leaf j
      rw [Fin.eq_zero j]
      rfl
    rw [h, List.map_id]
  have hfold (bits : List Bool) : bits.foldr (· || ·) false = bits.any id := by
    induction bits with
    | nil => rfl
    | cons b bits ih => simp [List.foldr_cons, List.any_cons, ih]
  have h := (recognizeSummary.get summary_recognized).down.2.observe_foldr
    (leaves.map (fun leaf => leaf 0))
  change (leaves.map (fun leaf => leaf 0)).foldr (· || ·) false =
    BlockSummary.summarize summaryMerge summaryEmpty
      ((leaves.map (fun leaf => leaf 0)).map summaryBit) 0 at h
  rw [hl, hfold] at h
  rw [← h]
  simp [List.any_eq_true]

private def summaryLeaf (n j : ℕ) : Circuit signature n 1 :=
  if hj : j < n then Circuit.wiring signature (fun _ => ⟨j, hj⟩)
  else Circuit.oneGate (.const false) Fin.elim0

@[simp] private theorem summaryLeaf_eval (n j : ℕ) (x : Fin n → Bool) :
    (summaryLeaf n j).eval interpretation x 0 = if hj : j < n then x ⟨j, hj⟩ else false := by
  unfold summaryLeaf
  split <;> rfl

private theorem summaryLeaf_depth (n j : ℕ) : (summaryLeaf n j).depth ≤ 1 := by
  unfold summaryLeaf
  split
  · simp
  · exact (Circuit.depth_oneGate _ _).le

private theorem summaryLeaf_size (n j : ℕ) : (summaryLeaf n j).size ≤ 1 := by
  unfold summaryLeaf
  split <;> simp

private theorem summaryLeaf_code (n j : ℕ) :
    (summaryLeaf n j).code =
      if j < n then ([], [j]) else ([(.const false, [])], [n]) := by
  unfold summaryLeaf
  split
  · rw [Circuit.code_wiring]
    rfl
  · rfl

private theorem summaryLeaf_code_logspace :
    ComputableInLogSpace (fun p : ℕ × ℕ => (summaryLeaf p.1 p.2).code)
      (encPair encUnary encUnary) encCode := by
  have hn := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  have hwire : ComputableInLogSpace (fun p : ℕ × ℕ => (([], [p.2]) : RawCode))
      (encPair encUnary encUnary) encCode :=
    (ComputableInLogSpace.const []).pair (ComputableInLogSpace.listSingleton.comp hj.unaryToBinary)
  have hfalse : ComputableInLogSpace (fun p : ℕ × ℕ => (([(.const false, [])], [p.1]) : RawCode))
      (encPair encUnary encUnary) encCode :=
    (ComputableInLogSpace.const [(Op.const false, [])]).pair
      (ComputableInLogSpace.listSingleton.comp hn.unaryToBinary)
  exact ((hj.unaryLt hn).ite hwire hfalse).congr_fun fun p => by
    simp [summaryLeaf_code]

private def summaryInit (n : ℕ) :
    Circuit signature n (2 ^ BlockSummary.paddingDepth n * 1) :=
  BlockSummary.bank (fun j : Fin (2 ^ BlockSummary.paddingDepth n) => summaryLeaf n j.val)

private theorem summaryInit_correct (n : ℕ) (x : Fin n → Bool) :
    BlockSummary.summarize summaryMerge summaryEmpty
        (List.ofFn (BlockSummary.unpack ((summaryInit n).eval interpretation x))) 0 =
      boolOr n x := by
  apply Bool.eq_iff_iff.mpr
  simp only [summarize_true_iff, List.mem_ofFn, boolOr, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, hj⟩
    rw [summaryInit, BlockSummary.bank_eval, summaryLeaf_eval] at hj
    split at hj
    · exact ⟨_, hj⟩
    · cases hj
  · rintro ⟨j, hj⟩
    let i : Fin (2 ^ BlockSummary.paddingDepth n) :=
      ⟨j.val, j.isLt.trans_le (BlockSummary.le_paddedCount n)⟩
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simpa [summaryInit, i, j.isLt] using hj

private theorem summaryInit_code_logspace :
    ComputableInLogSpace (fun n => (summaryInit n).code) encUnary encCode := by
  apply BlockSummary.bank_code_logspace ComputableInLogSpace.id BlockSummary.paddedCount_logspace
  have hn := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  refine ((hj.unaryLt (BlockSummary.paddedCount_logspace.comp hn)).ite summaryLeaf_code_logspace
    (ComputableInLogSpace.const ([], []))).congr_fun ?_
  intro p
  simp only [decide_eq_true_eq, Function.comp_apply]
  split <;> rfl

private def summaryContext (n : ℕ) : Circuit signature n 0 :=
  Circuit.wiring signature Fin.elim0

private def summaryRead : Circuit signature (1 + 0) 1 := Circuit.id signature 1

/-- Existing OR prediction through the shared ordered-summary compiler. -/
def summaryFamily (n : ℕ) : Circuit signature n 1 :=
  BlockSummary.compile summaryMergeCircuit (BlockSummary.paddingDepth n)
    (summaryInit n) (summaryContext n) summaryRead

private theorem summary_combine : BlockSummary.combine summaryMergeCircuit = summaryMerge := by
  funext left right
  exact summaryMergeCircuit_eval left right

theorem summaryFamily_correct (n : ℕ) (x : Fin n → Bool) :
    (summaryFamily n).eval interpretation x 0 = boolOr n x := by
  have laws : BlockSummary.Laws (BlockSummary.combine summaryMergeCircuit) summaryEmpty := by
    rw [summary_combine]
    exact summaryLaws
  have h := congrFun (BlockSummary.compile_eval summaryMergeCircuit laws
    (BlockSummary.paddingDepth n) (summaryInit n) (summaryContext n) summaryRead x) 0
  change (summaryFamily n).eval interpretation x 0 =
    BlockSummary.summarize (BlockSummary.combine summaryMergeCircuit) summaryEmpty
      (List.ofFn (BlockSummary.unpack ((summaryInit n).eval interpretation x))) 0 at h
  rw [summary_combine] at h
  exact h.trans (summaryInit_correct n x)

theorem summaryFamily_predicts (T : ℕ) (x : Fin (2 * T + 1) → Bool) :
    (summaryFamily (2 * T + 1)).eval interpretation x 0 = prediction T x := by
  rw [prediction_eq_boolOr]
  exact summaryFamily_correct _ x

theorem summaryFamily_depth (n : ℕ) :
    (summaryFamily n).depth ≤ 2 + 2 * Nat.clog 2 n := by
  have h := BlockSummary.compile_depth summaryMergeCircuit (BlockSummary.paddingDepth n)
    (summaryInit n) (summaryContext n) summaryRead
  have hinit : (summaryInit n).depth ≤ 1 :=
    BlockSummary.bank_depth _ (fun j => summaryLeaf_depth n j.val)
  have hmerge : summaryMergeCircuit.depth = 1 := Circuit.depth_oneGate _ _
  have hcontext : (summaryContext n).depth = 0 := by simp [summaryContext]
  have hread : summaryRead.depth = 0 := by simp [summaryRead]
  have hp := BlockSummary.paddingDepth_eq_clog n
  unfold summaryFamily
  apply h.trans
  rw [hmerge, hcontext, hread, max_eq_left (Nat.zero_le _)]
  omega

theorem summaryFamily_size (n : ℕ) : (summaryFamily n).size ≤ 8 * (n + 1) := by
  have h := BlockSummary.compile_size summaryMergeCircuit (BlockSummary.paddingDepth n)
    (summaryInit n) (summaryContext n) summaryRead
  have hinit : (summaryInit n).size ≤ 2 ^ BlockSummary.paddingDepth n := by
    simpa only [summaryInit, Nat.mul_one] using
      BlockSummary.bank_size _ (fun j => summaryLeaf_size n j.val)
  have hcount := BlockSummary.paddedCount_le n
  change 2 ^ BlockSummary.paddingDepth n ≤ 2 * (n + 1) at hcount
  have hmerge : summaryMergeCircuit.size = 1 := rfl
  have hcontext : (summaryContext n).size = 0 := by simp [summaryContext]
  have hread : summaryRead.size = 0 := by simp [summaryRead]
  unfold summaryFamily
  apply h.trans
  rw [hmerge, hcontext, hread]
  omega

theorem summaryFamily_lower (n : ℕ) :
    Nat.clog 2 n ≤ (summaryFamily n).depth :=
  UniformOROptimal.or_depth_lower_bound _ (summaryFamily_correct n)

theorem summaryFamily_uniform : LogspaceUniform summaryFamily := by
  have hcontext : ComputableInLogSpace (fun n => (summaryContext n).code) encUnary encCode :=
    (ComputableInLogSpace.const (([], []) : RawCode)).congr_fun fun n => by
      simp [summaryContext, Circuit.code_wiring]
  have h := BlockSummary.compile_code_logspace summaryMergeCircuit summaryRead
    ComputableInLogSpace.id BlockSummary.paddingDepth_logspace
    BlockSummary.paddedCount_logspace summaryInit_code_logspace hcontext
  exact ((ComputableInLogSpace.id : ComputableInLogSpace (fun n : ℕ => n) encUnary encUnary).pair
    h).congr (fun _ => rfl)

end PredictionDepth.ORAutomaton
