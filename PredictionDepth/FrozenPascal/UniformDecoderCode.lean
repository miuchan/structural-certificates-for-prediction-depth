import PredictionDepth.FrozenPascal.UniformDecoder
import PredictionDepth.FrozenPascal.CoefficientUniform

/-! Logarithmic-workspace generation of the decoder's nested scalar banks. -/

namespace PredictionDepth.FrozenPascal.UniformDecoder

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM
open StandardComplexity

variable {α : Type} {enc : α ↪ List Bool}

theorem size_logspace {f : α → ℕ} (hf : ComputableInLogSpace f enc encUnary) :
    ComputableInLogSpace (fun a => (f a).size) enc encUnary := by
  have hb : ComputableInLogSpace (fun a => (f a).bits) enc encBits :=
    hf.unaryToBinary.congr fun _ => rfl
  exact (CodeLogspace.bitsLength.comp hb).congr_fun fun a => (Nat.size_eq_bits_len (f a)).symm

theorem countWidth_logspace {k : α → ℕ} (hk : ComputableInLogSpace k enc encUnary) :
    ComputableInLogSpace (fun a => countWidth (k a)) enc encUnary := by
  exact (size_logspace (hk.unaryAdd (ComputableInLogSpace.const 1))).congr_fun fun a => by
    rw [RegularReduction.size_eq_clog_succ]

private theorem rawWire {f : α → ℕ} (hf : ComputableInLogSpace f enc encUnary) :
    ComputableInLogSpace (fun a => (([], [f a]) : CodeLogspace.RawCode)) enc encCode :=
  (ComputableInLogSpace.const []).pair (ComputableInLogSpace.listSingleton.comp hf.unaryToBinary)

theorem literal_code_logspace {w s j : α → ℕ}
    (hw : ComputableInLogSpace w enc encUnary)
    (hs : ComputableInLogSpace s enc encUnary)
    (hj : ComputableInLogSpace j enc encUnary) :
    ComputableInLogSpace (fun a => (literal (w a) (s a) (j a)).code) enc encCode := by
  have hwire := rawWire hj
  have hnot : ComputableInLogSpace (fun _ : α => notGate.code) enc encCode :=
    ComputableInLogSpace.const _
  have hneg := CodeLogspace.compCode_logspace hw hnot hwire
    (fun _ => by rw [Circuit.length_code_fst]; exact CodeLogspace.circuit_boundedReferences notGate)
  have hbit := testBit_logspace hs hj
  refine ((hj.unaryLt hw).ite (hbit.ite hwire hneg) (Code.constant hw false)).congr_fun ?_
  intro a
  by_cases h : j a < w a
  · cases hb : (s a).testBit (j a)
    · simp only [decide_eq_true_eq, h, dite_eq_left, ite_eq_left, hb, Bool.false_eq_true,
        ite_false, literal, matchingBit]
      rw [← compCode_code, wireBit, Circuit.code_wiring]
      rfl
    · simp [literal, matchingBit, h, hb, wireBit, Circuit.code_wiring]
  · simp [literal, h]

theorem matchCount_code_logspace {k s : α → ℕ}
    (hk : ComputableInLogSpace k enc encUnary) (hs : ComputableInLogSpace s enc encUnary) :
    ComputableInLogSpace (fun a => (matchCount (k a) (s a)).code) enc encCode := by
  have hw := countWidth_logspace hk
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  exact Code.reduceBank allFamily_code_logspace hw hw
    (literal_code_logspace (hw.comp hp) (hs.comp hp) hj)

theorem paddedMatch_code_logspace {m k s : α → ℕ}
    (hm : ComputableInLogSpace m enc encUnary)
    (hk : ComputableInLogSpace k enc encUnary)
    (hs : ComputableInLogSpace s enc encUnary) :
    ComputableInLogSpace (fun a => (paddedMatch (m a) (k a) (s a)).code) enc encCode := by
  have hw := countWidth_logspace hk
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  have hwire : ComputableInLogSpace
      (fun a => (Circuit.wiring signature (Fin.natAdd (m a) :
        Fin (countWidth (k a)) → Fin (m a + countWidth (k a)))).code) enc encCode :=
    Code.wiring hw ((hm.comp hp).unaryAdd hj).unaryToBinary (fun _ _ => rfl)
  exact CodeLogspace.circuit_comp_logspace (hm.unaryAdd hw) hwire
    (matchCount_code_logspace hk hs)

theorem lookupEntry_code_logspace {m k u s : α → ℕ}
    (hm : ComputableInLogSpace m enc encUnary)
    (hk : ComputableInLogSpace k enc encUnary)
    (hu : ComputableInLogSpace u enc encUnary)
    (hs : ComputableInLogSpace s enc encUnary) :
    ComputableInLogSpace (fun a => (lookupEntry (m a) (k a) (u a) (s a)).code)
      enc encCode := by
  have hn := hm.unaryAdd (countWidth_logspace hk)
  have hwire := rawWire hu
  have hmatch := paddedMatch_code_logspace hm hk hs
  have hpair := CodeLogspace.appendCode_logspace hn hwire hmatch (fun a => by
    rw [Circuit.length_code_fst]
    exact CodeLogspace.circuit_boundedReferences (paddedMatch (m a) (k a) (s a)))
  have hand : ComputableInLogSpace (fun _ : α => andGate.code) enc encCode :=
    ComputableInLogSpace.const _
  have hjoin := CodeLogspace.compCode_logspace hn hand hpair (fun a => by
    have hh : (appendCode (m a + countWidth (k a)) ([], [u a])
        (paddedMatch (m a) (k a) (s a)).code).2.length = 2 := by
      simp only [appendCode, List.length_append, List.length_singleton, List.length_map]
      change 1 + (List.ofFn _).length = 2
      rw [List.length_ofFn]
    rw [hh, Circuit.length_code_fst]
    exact CodeLogspace.circuit_boundedReferences andGate)
  have ht := (hu.unaryLt hm).bool_and (tableBit_logspace hu hk hs)
  exact (ht.ite hjoin (Code.constant hn false)).congr_fun fun a => by
    simp only [Bool.and_eq_true, decide_eq_true_eq, lookupEntry]
    split_ifs
    · rw [conjoin, ← compCode_code, ← appendCode_code, wireBit, Circuit.code_wiring]
      rfl
    · rfl

theorem lookupSlice_code_logspace (W : WeightBasis) {m k u : α → ℕ}
    (hm : ComputableInLogSpace m enc encUnary)
    (hk : ComputableInLogSpace k enc encUnary)
    (hu : ComputableInLogSpace u enc encUnary) :
    ComputableInLogSpace (fun a => (lookupSlice W (m a) (k a) (u a)).code) enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  exact Code.reduceBank (parityFamily_code_logspace W) (hm.unaryAdd (countWidth_logspace hk))
    (hk.unaryAdd (ComputableInLogSpace.const 2))
    (lookupEntry_code_logspace (hm.comp hp) (hk.comp hp) (hu.comp hp) hj)

theorem lookup_code_logspace (W : WeightBasis) {m k : α → ℕ}
    (hm : ComputableInLogSpace m enc encUnary) (hk : ComputableInLogSpace k enc encUnary) :
    ComputableInLogSpace (fun a => (lookup W (m a) (k a)).code) enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  exact Code.reduceBank (parityFamily_code_logspace W) (hm.unaryAdd (countWidth_logspace hk)) hm
    (lookupSlice_code_logspace W (hm.comp hp) (hk.comp hp) hj)

theorem registerWidth_logspace {m : α → ℕ} (hm : ComputableInLogSpace m enc encUnary) :
    ComputableInLogSpace (fun a => RegisterWidth (m a)) enc encUnary :=
  hm.unaryAdd (hm.unaryAdd (hm.unaryAdd hm))

theorem hopInput_code_logspace {m j : α → ℕ}
    (hm : ComputableInLogSpace m enc encUnary) (hj : ComputableInLogSpace j enc encUnary) :
    ComputableInLogSpace (fun a => (hopInput (m a) (j a)).code) enc encCode := by
  have hwire := rawWire (hm.unaryAdd (hm.unaryAdd hj))
  exact ((hj.unaryLt hm).ite hwire (Code.constant (registerWidth_logspace hm) false)).congr_fun
    fun a => by
      simp only [decide_eq_true_eq, hopInput]
      split_ifs
      · rw [wireBit, Circuit.code_wiring]
        rfl
      · rfl

theorem count_code_logspace (W : WeightBasis) {m : α → ℕ} {k : ∀ a, Fin (m a)}
    (hm : ComputableInLogSpace m enc encUnary)
    (hk : ComputableInLogSpace (fun a => (k a).val) enc encUnary) :
    ComputableInLogSpace (fun a => (count W (k a)).code) enc encCode := by
  have hs := hk.unaryAdd (ComputableInLogSpace.const 1)
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  have hwire : ComputableInLogSpace
      (fun a => (Circuit.wiring signature (countInputs (k a))).code) enc encCode :=
    Code.wiring hs ((hm.comp hp).unaryAdd hj).unaryToBinary (fun _ _ => rfl)
  exact CodeLogspace.circuit_comp_logspace (registerWidth_logspace hm) hwire (W.uniform.comp hs)

set_option maxHeartbeats 1000000 in
theorem term_code_logspace (W : WeightBasis) {m : α → ℕ} {k : ∀ a, Fin (m a)}
    (hm : ComputableInLogSpace m enc encUnary)
    (hk : ComputableInLogSpace (fun a => (k a).val) enc encUnary) :
    ComputableInLogSpace (fun a => (term W (k a)).code) enc encCode := by
  have hn := registerWidth_logspace hm
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  have htag : ComputableInLogSpace
      (fun a => (Circuit.wiring signature (timeWire (m := m a))).code) enc encCode :=
    Code.wiring hm hj.unaryToBinary (fun _ _ => rfl)
  have hc := count_code_logspace W (k := k) hm hk
  have hlookup := CodeLogspace.circuit_comp_logspace hn
    (c := fun a => lookupInputs W (k a)) (d := fun a => lookup W (m a) (k a).val)
    (CodeLogspace.circuit_append_logspace hn htag hc) (lookup_code_logspace W hm hk)
  have hedge : ComputableInLogSpace (fun a => (edge (k a)).code) enc encCode :=
    Code.reduceBank allFamily_code_logspace hn hk (hopInput_code_logspace (hm.comp hp) hj)
  have hdata : ComputableInLogSpace
      (fun a => (wireBit (trackWire (dataWire (k a)))).code) enc encCode :=
    Code.wire (hm.unaryAdd (hm.unaryAdd (hm.unaryAdd hk))).unaryToBinary (fun _ => rfl)
  exact Code.conjoin hn (Code.conjoin hn hlookup hedge) hdata

theorem decoder_succ_code_logspace (W : WeightBasis) :
    ComputableInLogSpace (fun H => (decoder W (H + 1)).code) encUnary encCode := by
  have hid : ComputableInLogSpace (fun n : ℕ => n) encUnary encUnary :=
    ComputableInLogSpace.id
  have hm : ComputableInLogSpace (fun H : ℕ => H + 1) encUnary encUnary :=
    hid.unaryAdd (ComputableInLogSpace.const 1)
  have hp := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  let bounded (p : ℕ × ℕ) : Fin (p.1 + 1) := ⟨min p.2 p.1, by omega⟩
  let c (H j : ℕ) : Gates (RegisterWidth (H + 1)) 1 := term W (bounded (H, j))
  have hc : ComputableInLogSpace (fun p : ℕ × ℕ => (c p.1 p.2).code)
      (encPair encUnary encUnary) encCode :=
    term_code_logspace W (m := fun p : ℕ × ℕ => p.1 + 1) (k := bounded)
      (hm.comp hp) (hj.unaryMin hp)
  have h : ComputableInLogSpace
      (fun H : ℕ => (reduceBank (parityFamily W) (fun j : Fin (H + 1) => c H j.val)).code)
      encUnary encCode :=
    Code.reduceBank (F := parityFamily W)
      (n := fun H : ℕ => RegisterWidth (H + 1)) (m := fun H => H + 1)
      (c := c) (parityFamily_code_logspace W) (registerWidth_logspace hm) hm hc
  refine h.congr_fun ?_
  intro H
  have he : (fun j : Fin (H + 1) => term W (bounded (H, j.val))) = term W := by
    funext j
    have hh : bounded (H, j.val) = j :=
      Fin.ext (Nat.min_eq_left (by have := j.isLt; omega))
    exact congrArg (fun q : Fin (H + 1) => term W q) hh
  exact congrArg
    (fun terms : Fin (H + 1) → Gates (RegisterWidth (H + 1)) 1 =>
      (reduceBank (parityFamily W) terms).code) he.symm

end PredictionDepth.FrozenPascal.UniformDecoder
