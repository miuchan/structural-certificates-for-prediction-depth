import PredictionDepth.FrozenPascal.UniformWeightCode
import PredictionDepth.FrozenPascal.UniformWeightWidths
import PredictionDepth.FrozenPascal.UniformWeightSemantics
import PredictionDepth.FrozenPascal.UniformReducers

/-! A logarithmic-depth weight basis built from regular carry-save layers. -/

namespace PredictionDepth.FrozenPascal.UniformWeight

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity.UniformComposition
open Turing.MultiTapeTM

private theorem replicateCodes_logspace {α : Type} {enc : α ↪ List Bool}
    {count width : α → ℕ} {layer : ∀ a, Gates (width a) (width a)}
    (hcount : ComputableInLogSpace count enc encUnary)
    (hlayer : ComputableInLogSpace (fun a => (layer a).code) enc encCode) :
    ComputableInLogSpace (fun a => (List.replicate (count a) (layer a)).map Circuit.code)
      enc (encList encCode) := by
  apply (StandardComplexity.CodeLogspace.map_range hcount
    (hlayer.comp (ComputableInLogSpace.fst enc encUnary))).congr_fun
  intro a
  simp [List.map_const']

private theorem normalizedChain_replicate_eval {n W : ℕ} (initial : Gates n W)
    (layer : Gates W W) (d : ℕ) (x : BitString n) :
    (normalizedChain initial (List.replicate d layer)).eval interpretation x =
      ((layer.eval interpretation)^[d]) (initial.eval interpretation x) := by
  rw [normalizedChain_eval, circuitChain_eval]
  generalize initial.eval interpretation x = v
  induction d generalizing v with
  | zero => rfl
  | succ d ih => rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]

private theorem normalizedChain_replicate_depth {n W : ℕ} (initial : Gates n W)
    (layer : Gates W W) (d : ℕ) :
    (normalizedChain initial (List.replicate d layer)).depth ≤
      initial.depth + 1 + d * (layer.depth + 1) := by
  simpa only [List.map_replicate, List.sum_replicate_nat] using
    normalizedChain_depth initial (List.replicate d layer)

private def finish (w : ℕ) : Gates (w + w) (w + w) :=
  normalizedChain (Circuit.wiring signature id) (List.replicate w (finishStep w))

private theorem finish_eval (w : ℕ) (x : Pair w) :
    (finish w).eval interpretation x = (finishCircuit w w).eval interpretation x := by
  have h (d : ℕ) : (finishCircuit w d).eval interpretation x =
      (((finishStep w).eval interpretation)^[d]) x := by
    induction d with
    | zero => rfl
    | succ d ih => rw [finishCircuit, Circuit.eval_comp, ih, Function.iterate_succ_apply']
  rw [finish, normalizedChain_replicate_eval, Circuit.eval_wiring, Function.comp_id, h]

private theorem finish_depth (w : ℕ) : (finish w).depth ≤ 1 + 8 * w := by
  have h := normalizedChain_replicate_depth (Circuit.wiring signature (id : Fin (w + w) → _))
    (finishStep w) w
  simp only [Circuit.depth_wiring, zero_add] at h
  apply h.trans
  rw [Nat.mul_comm 8 w]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (depth_finishStep_le w) 1)) _

private theorem finish_logspace :
    ComputableInLogSpace (fun w => (finish w).code) encUnary encCode := by
  have hw : ComputableInLogSpace (fun w : ℕ => w) encUnary encUnary := ComputableInLogSpace.id
  have hwidth := hw.unaryAdd hw
  exact normalizedChain_logspace hwidth hwidth (identityCode_logspace hwidth)
    (replicateCodes_logspace hw finishStep_logspace)

private def tree (n : ℕ) : Gates n (paddedCount n * (wordWidth n + wordWidth n)) :=
  normalizedChain (initial n (wordWidth n) (paddedCount n))
    (List.replicate (wordWidth n) (mergeBank (wordWidth n) (paddedCount n)))

private theorem merge_iterate_eval {w P : ℕ} (d : ℕ) (v : Fin P → Pair w) :
    (((mergeBank w P).eval interpretation)^[d]) (packed v) = packed (reduceValues d v) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', ih, mergeBank_eval, reduceValues]

private theorem tree_eval (n : ℕ) (x : BitString n) :
    (tree n).eval interpretation x =
      packed (reduceValues (wordWidth n) (leaves n (wordWidth n) (paddedCount n) x)) := by
  rw [tree, normalizedChain_replicate_eval, initial_eval, merge_iterate_eval]

private theorem tree_depth (n : ℕ) : (tree n).depth ≤ 2 + 14 * wordWidth n := by
  apply (normalizedChain_replicate_depth _ _ _).trans
  rw [Nat.mul_comm 14]
  exact Nat.add_le_add (Nat.add_le_add_right (initial_depth _ _ _) 1)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (mergeBank_depth _ _) 1))

private def rootWire (n : ℕ) (i : Fin (wordWidth n + wordWidth n)) :
    Fin (paddedCount n * (wordWidth n + wordWidth n)) :=
  finProdFinEquiv (⟨0, paddedCount_pos n⟩, i)

private def firstWord (w : ℕ) : Gates (w + w) w :=
  Circuit.wiring signature (Fin.castAdd w)

def family (n : ℕ) : Gates n (wordWidth n) :=
  (firstWord (wordWidth n)).comp ((finish (wordWidth n)).comp
    ((Circuit.wiring signature (rootWire n)).comp (tree n)))

theorem family_value (n : ℕ) (x : BitString n) :
    (BitString.equivFin _ ((family n).eval interpretation x)).val = BitString.weight x := by
  let r : Pair (wordWidth n) :=
    reduceValues (wordWidth n) (leaves n (wordWidth n) (paddedCount n) x) ⟨0, paddedCount_pos n⟩
  have hr : packed (reduceValues (wordWidth n) (leaves n (wordWidth n) (paddedCount n) x)) ∘
      rootWire n = r := by
    funext i
    exact packed_pair _ _ _
  have he : (family n).eval interpretation x =
      BitString.fstBits ((finishCircuit (wordWidth n) (wordWidth n)).eval interpretation r) := by
    simp only [family, Circuit.eval_comp, Circuit.eval_wiring, firstWord, tree_eval, hr,
      finish_eval]
    rfl
  have hv := val_fstBits_eval_finishCircuit_mod r
  rw [← he, Nat.mod_eq_of_lt (BitString.equivFin _ ((family n).eval interpretation x)).isLt] at hv
  have hz : (⟨0, paddedCount_pos n⟩ : Fin (2 ^ wordWidth n)) = 0 := Fin.ext (by simp)
  have hroot : pairVal r % 2 ^ wordWidth n = BitString.weight x % 2 ^ wordWidth n := by
    simpa only [r, paddedCount, hz] using
      leaves_root_mod (wordWidth n) n (wordWidth n) (le_paddedCount n) x
  rw [hv, hroot, Nat.mod_eq_of_lt ((BitString.weight_le_length x).trans_lt (lt_pow_wordWidth n))]

theorem family_depth (n : ℕ) : (family n).depth ≤ 22 * (wordWidth n + 1) := by
  have hr : ((Circuit.wiring signature (rootWire n)).comp (tree n)).depth ≤
      2 + 14 * wordWidth n := (Circuit.depth_comp_le _ _).trans (by simpa using tree_depth n)
  have hf := (Circuit.depth_comp_le (finish (wordWidth n)) _).trans
    (Nat.add_le_add (finish_depth (wordWidth n)) hr)
  apply (Circuit.depth_comp_le _ _).trans
  simp only [firstWord, Circuit.depth_wiring, zero_add, Nat.mul_add]
  omega

theorem family_code_logspace :
    ComputableInLogSpace (fun n => (family n).code) encUnary encCode := by
  have hw := wordWidth_logspace
  have hP := paddedCount_logspace
  have hn : ComputableInLogSpace (fun n : ℕ => n) encUnary encUnary :=
    ComputableInLogSpace.id
  have hpair := hw.unaryAdd hw
  have hbank := hP.unaryMul hpair
  have htree : ComputableInLogSpace (fun n => (tree n).code) encUnary encCode :=
    normalizedChain_logspace hn hbank (initial_logspace hn hw hP)
      (replicateCodes_logspace hw (mergeBank_logspace hw hP))
  have href := (ComputableInLogSpace.snd encUnary encUnary).unaryToBinary
  have hroot := Code.wiring (f := rootWire) hpair href
    (fun n i => by simp [rootWire, finProdFinEquiv])
  have hfirst := Code.wiring (f := fun n => Fin.castAdd (wordWidth n)) hw href
    (fun _ _ => rfl)
  exact StandardComplexity.CodeLogspace.circuit_comp_logspace hn
    (StandardComplexity.CodeLogspace.circuit_comp_logspace hn
      (StandardComplexity.CodeLogspace.circuit_comp_logspace hn htree hroot)
      (finish_logspace.comp hw)) hfirst

/-- Concrete counting basis with bounded fan-in, verified carry-save arithmetic,
and a logspace transducer for the complete circuit description. -/
def basis : WeightBasis where
  circuit := family
  value := family_value
  depthFactor := 22
  depth := family_depth
  uniform := family_code_logspace

end PredictionDepth.FrozenPascal.UniformWeight
