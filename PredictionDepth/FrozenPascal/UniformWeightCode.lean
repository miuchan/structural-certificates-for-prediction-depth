import PredictionDepth.FrozenPascal.UniformWeightCircuits

/-! Genuine logspace serializers for the regular carry-save counting banks. -/
namespace PredictionDepth.FrozenPascal.UniformWeight
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM
open StandardComplexity CodeLogspace CodeLogspaceFamilies

variable {α : Type} {enc : α ↪ List Bool} {n w P e : α → ℕ}

theorem initialEntry_logspace (hn : ComputableInLogSpace n enc encUnary)
    (hw : ComputableInLogSpace w enc encUnary) :
    ComputableInLogSpace (fun p : α × ℕ => (initialEntry (n p.1) (w p.1) p.2).code)
      (encPair enc encUnary) encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hq := ComputableInLogSpace.snd enc encUnary
  have hB := (hw.unaryAdd hw).comp hp
  have hrow := hq.unaryDiv hB
  have hlane := hq.unaryMod hB
  have ht := (hrow.unaryLt (hn.comp hp)).bool_and
    (hlane.unaryEq (ComputableInLogSpace.const 0))
  have hwire := (ComputableInLogSpace.const (encMid := encList encGate)
    ([] : List (Op × List ℕ))).pair (ComputableInLogSpace.listSingleton.comp hrow.unaryToBinary)
  have hfalse := constant_logspace (hn.comp hp) false
  exact (ht.ite hwire hfalse).congr_fun fun p => by
    simp only [Bool.and_eq_true, decide_eq_true_eq, Function.comp_apply]
    unfold initialEntry
    split <;> simp [Circuit.code_wiring]

theorem initial_logspace (hn : ComputableInLogSpace n enc encUnary)
    (hw : ComputableInLogSpace w enc encUnary) (hP : ComputableInLogSpace P enc encUnary) :
    ComputableInLogSpace (fun a => (initial (n a) (w a) (P a)).code) enc encCode := by
  have hm := hP.unaryMul (hw.unaryAdd hw)
  have hp := ComputableInLogSpace.fst enc encUnary
  have hq := ComputableInLogSpace.snd enc encUnary
  have hc := initialEntry_logspace hn hw
  apply circuit_pi_of_indexed_logspace hn hm
  exact ((hq.unaryLt (hm.comp hp)).ite hc (ComputableInLogSpace.const ([], []))).congr_fun
    fun p => by simp only [decide_eq_true_eq, Function.comp_apply]; split_ifs <;> rfl

theorem paddedInputWires_val (w P e : ℕ) (i : Fin ((w + w) + (w + w))) :
    (paddedInputWires w P e i).val =
      if e * ((w + w) + (w + w)) + i.val < P * (w + w)
      then e * ((w + w) + (w + w)) + i.val else P * (w + w) := by
  unfold paddedInputWires
  split <;> rfl

theorem paddedInput_logspace (hw : ComputableInLogSpace w enc encUnary)
    (hP : ComputableInLogSpace P enc encUnary) (he : ComputableInLogSpace e enc encUnary) :
    ComputableInLogSpace (fun a => (paddedInput (w a) (P a) (e a)).code) enc encCode := by
  have hB := hw.unaryAdd hw
  have hW := hP.unaryMul hB
  have h2B := hB.unaryAdd hB
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  have hidx := ((he.comp hp).unaryMul (h2B.comp hp)).unaryAdd hj
  have hword := hW.comp hp
  have href := ((hidx.unaryLt hword).ite hidx hword).unaryToBinary
  have hwire := wiring_logspace (f := fun a => paddedInputWires (w a) (P a) (e a)) h2B href
    (fun a i => by simpa only [decide_eq_true_eq, Function.comp_apply] using
      paddedInputWires_val (w a) (P a) (e a) i)
  have hinput := CodeLogspace.circuit_append_logspace hW
    (UniformComposition.identityCode_logspace hW) (constant_logspace hW false)
  exact CodeLogspace.circuit_comp_logspace hW hinput hwire

private theorem selector_bound {N B : ℕ} (c : Circuit signature N B) (q : ℕ) :
    BoundedReferences (c.code.2.length + ([] : List (Op × List ℕ)).length)
      ([], [min (q % B) B]) := by
  have hout : c.code.2.length = B := by simp [Circuit.code]
  rw [hout]
  constructor
  · intro g hg
    cases hg
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact Nat.min_le_right _ _

/-- Each entry is a selected output of one carry-save reducer on padded child
blocks. Out-of-range queries are masked before any code is emitted. -/
theorem mergeBank_logspace (hw : ComputableInLogSpace w enc encUnary)
    (hP : ComputableInLogSpace P enc encUnary) :
    ComputableInLogSpace (fun a => (mergeBank (w a) (P a)).code) enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hq := ComputableInLogSpace.snd enc encUnary
  have hB := hw.unaryAdd hw
  have hW := hP.unaryMul hB
  have hB' := hB.comp hp
  have hrow := hq.unaryDiv hB'
  have hlane := (hq.unaryMod hB').unaryMin hB'
  have hpad := paddedInput_logspace (hw.comp hp) (hP.comp hp) hrow
  have hcsa := CodeLogspace.circuit_comp_logspace (hW.comp hp) hpad (csa4to2_logspace.comp (hw.comp hp))
  have hselect := (ComputableInLogSpace.const (encMid := encList encGate)
    ([] : List (Op × List ℕ))).pair (ComputableInLogSpace.listSingleton.comp hlane.unaryToBinary)
  have hselected := compCode_logspace (hW.comp hp) hselect hcsa (fun p =>
    selector_bound ((csa4to2 (w p.1)).comp (paddedInput (w p.1) (P p.1) (p.2 / (w p.1 + w p.1)))) p.2)
  have hmask := (hq.unaryLt (hW.comp hp)).ite hselected (ComputableInLogSpace.const ([], []))
  apply circuit_pi_of_indexed_logspace hW hW
  refine hmask.congr_fun ?_
  intro p
  simp only [decide_eq_true_eq, Function.comp_apply]
  split_ifs with hqW
  · have hBpos : 0 < w p.1 + w p.1 := by
      have hne : w p.1 + w p.1 ≠ 0 := by
        intro hz
        rw [hz, Nat.mul_zero] at hqW
        omega
      omega
    have hmod := Nat.mod_lt p.2 hBpos
    rw [mergeEntry, ← compCode_code, Circuit.code_wiring]
    simp only [finProdFinEquiv_symm_apply, Fin.divNat, Fin.modNat, List.ofFn_succ, List.ofFn_zero,
      Nat.min_eq_left hmod.le]
  · rfl

end PredictionDepth.FrozenPascal.UniformWeight
