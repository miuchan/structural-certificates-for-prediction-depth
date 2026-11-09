import PredictionDepth.FrozenPascal.HomogeneousPascal
import PredictionDepth.FrozenPascal.CoefficientUniform
import PredictionDepth.FrozenPascal.UniformGuards
import PredictionDepth.FrozenPascal.UniformWeightWidths
import PredictionDepth.FrozenPascal.UniformXor

/-! For the homogeneous Pascal rule, a logspace writer scans the window and
emits wires only for odd binomial coefficients. A uniform parity circuit
then works on the sparse support, rather than on the full input window. -/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open Linear (F₂)
open StandardComplexity Turing.MultiTapeTM
open scoped BigOperators

private def supportList (T : ℕ) : List (Fin (T + 1)) :=
  (List.finRange (T + 1)).filter fun i => chooseParity T i.val

private theorem supportList_nodup (T : ℕ) : (supportList T).Nodup :=
  (List.nodup_finRange _).filter _

private theorem supportList_toFinset (T : ℕ) : (supportList T).toFinset = pascalSupport T := by
  ext i
  simp [supportList, pascalSupport]

private theorem supportList_length (T : ℕ) : (supportList T).length = 2 ^ T.bitIndices.length := by
  rw [← List.toFinset_card_of_nodup (supportList_nodup T), supportList_toFinset, pascalSupport_card]

private def supportWiring (q T : ℕ) : Gates (RawWidth q (T + 1)) (supportList T).length :=
  Circuit.wiring signature fun j => rawDataWire ((supportList T).get j)

private theorem supportWiring_code (q T : ℕ) :
    (supportWiring q T).code = ([], ((List.range (T + 1)).filter (chooseParity T)).map
      (fun k => (T + 1) * q + k)) := by
  rw [supportWiring, Circuit.code_wiring]
  rw [show (List.ofFn fun j => (rawDataWire (q := q) ((supportList T).get j)).val) =
      (supportList T).map (fun i => (T + 1) * q + i.val) by
    exact List.ofFn_getElem_eq_map (supportList T) (fun i => (T + 1) * q + i.val)]
  have hRange : (List.finRange (T + 1)).map Fin.val = List.range (T + 1) := by
    rw [← List.ofFn_eq_map]
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_range]
    · intro i hi hj
      simp only [List.getElem_ofFn, List.getElem_range]
  rw [← hRange, List.filter_map, List.map_map]
  rfl

private theorem supportWiring_logspace (q : ℕ) :
    ComputableInLogSpace (fun T => (supportWiring q T).code) encUnary encCode := by
  have hp := ComputableInLogSpace.fst encUnary encUnary
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have hodd := chooseParity_logspace hp hi
  have href := (((UniformRegisters.succ_logspace.comp hp).unaryMulConst q).unaryAdd hi).unaryToBinary
  have hitem := ComputableInLogSpace.listSingleton.comp href
  have hworker := hodd.ite hitem (ComputableInLogSpace.const ([] : List ℕ))
  have hout := CodeLogspaceFamilies.flatMap_range_list UniformRegisters.succ_logspace hworker
  have hgen := (ComputableInLogSpace.const (encMid := encList encGate)
    ([] : List (Op × List ℕ))).pair hout
  refine hgen.congr_fun ?_
  intro T
  rw [supportWiring_code]
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  generalize List.range (T + 1) = ks
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    cases hb : chooseParity T k <;> simp [hb, ih]

/-- An actual uniform predictor with three De Morgan layers per set bit of
the time. At time zero the single support wire already gives the result. -/
def uniformHomogeneousPrediction (q T : ℕ) : Gates (RawWidth q (T + 1)) 1 :=
  (UniformXor.reduce (supportList T).length T.bitIndices.length).comp (supportWiring q T)

theorem uniformHomogeneousPrediction_correct (stay hop : Gates q 1)
    (hs : ∀ a, guard stay a = true) (hh : ∀ a, guard hop a = true)
    (T : ℕ) (x : Config (Bits q)) :
    (uniformHomogeneousPrediction q T).eval interpretation (rawSample x (T + 1)) 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
  apply bit_injective
  rw [uniformHomogeneousPrediction, Circuit.eval_comp, UniformXor.reduce_eval (supportList_length T),
    bit_ofBoolRing, homogeneous_prediction_sum stay hop hs hh]
  simp only [supportWiring, Circuit.eval_wiring, Function.comp_apply]
  rw [← List.sum_ofFn]
  rw [show (List.ofFn fun j => bit (rawSample x (T + 1) (rawDataWire ((supportList T).get j)))) =
      (supportList T).map (fun i => bit (rawSample x (T + 1) (rawDataWire i))) from
    List.ofFn_getElem_eq_map (supportList T) (fun i => bit (rawSample x (T + 1) (rawDataWire i))),
    ← List.sum_toFinset _ (supportList_nodup T),
    supportList_toFinset]

private theorem supportList_pos (T : ℕ) : 0 < (supportList T).length := by
  rw [supportList_length]
  exact Nat.two_pow_pos _

theorem uniformHomogeneousPrediction_depth (q T : ℕ) :
    (uniformHomogeneousPrediction q T).depth ≤ 3 * T.bitIndices.length :=
  (Circuit.depth_comp_le _ _).trans (by
    simpa only [supportWiring, Circuit.depth_wiring, Nat.add_zero] using
      UniformXor.reduce_depth (supportList T).length T.bitIndices.length (supportList_pos T))

theorem uniformHomogeneousPrediction_size (q T : ℕ) :
    (uniformHomogeneousPrediction q T).size = 5 * 2 ^ T.bitIndices.length * T.bitIndices.length := by
  have hw : (supportWiring q T).size = 0 := rfl
  rw [uniformHomogeneousPrediction, Circuit.size_comp, hw, Nat.zero_add,
    UniformXor.reduce_size _ _ (supportList_pos T), supportList_length]

theorem uniformHomogeneousPrediction_code_logspace (q : ℕ) :
    ComputableInLogSpace (fun T => (uniformHomogeneousPrediction q T).code)
      encUnary encCode := by
  have hwidth := UniformGuards.rawWidth_succ_logspace q
  have hw := supportWiring_logspace q
  have hcount : ComputableInLogSpace (fun T => (supportList T).length) encUnary encUnary :=
    (ComputableInLogSpace.listLength.comp hw.snd').congr_fun
      (fun T => by simp [supportWiring, Circuit.code])
  have hdepth : ComputableInLogSpace (fun T => T.bitIndices.length) encUnary encUnary := by
    refine (UniformWeight.wordWidth_logspace.comp
      (hcount.unarySub (ComputableInLogSpace.const 1))).congr_fun ?_
    intro T
    simp only [Function.comp_apply, UniformWeight.wordWidth, supportList_length]
    rw [Nat.sub_add_cancel (Nat.two_pow_pos _), Nat.clog_pow 2 _ (by decide)]
  exact CodeLogspace.circuit_comp_logspace hwidth hw (UniformXor.reduce_code_logspace hcount hdepth)

end PredictionDepth.FrozenPascal
