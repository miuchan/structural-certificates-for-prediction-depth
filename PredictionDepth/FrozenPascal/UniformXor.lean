import PredictionDepth.Complexity.UniformComposition
import PredictionDepth.FrozenPascal.UniformReducers

/-! A complete parity tree with three De Morgan layers per tree level.
The final OR gates of each merge layer are consecutive, allowing the
ordinary streaming chain compiler without an additional copy layer. Each
layer keeps its initial width. Pair indices may wrap in outputs outside the
active reduction blocks, which are ignored by the root computation. -/
namespace PredictionDepth.FrozenPascal.UniformXor

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open Linear (F₂)
open StandardComplexity Turing.MultiTapeTM
open scoped BigOperators

private def termGate (right : Bool) : Gates 2 1 :=
  if right then ((Formula.input (n := 2) 0).and ((Formula.input 1).not)).toCircuit
  else (((Formula.input (n := 2) 0).not).and (Formula.input 1)).toCircuit

private theorem termGate_eval (right : Bool) (x : Bits 2) :
    (termGate right).eval interpretation x 0 =
      (if right then x 0 && !x 1 else !x 0 && x 1) := by
  cases right <;> simp [termGate]

private theorem termGate_depth (right : Bool) : (termGate right).depth = 2 := by
  cases right <;> decide +kernel

private theorem termGate_size (right : Bool) : (termGate right).size = 2 := by
  cases right <;> decide +kernel

private def termEntry (n j : ℕ) : Gates n 1 :=
  if hn : 0 < n then (termGate (j % 2 = 1)).comp
    (Circuit.wiring signature (fun k : Fin 2 => ⟨(2 * (j / 2) + k.val) % n, Nat.mod_lt _ hn⟩))
  else constBit n false

private def termBank (n : ℕ) : Gates n (2 * n) :=
  Circuit.pi fun j => termEntry n j.val

private def orEntry (n j : ℕ) : Gates (2 * n) 1 :=
  if h : j < n then Circuit.oneGate .or (fun k => ⟨2 * j + k.val, by have hk : k.val < 2 := k.isLt; omega⟩)
  else constBit (2 * n) false

private def orBank (n : ℕ) : Gates (2 * n) n :=
  Circuit.pi fun j => orEntry n j.val

private def layer (n : ℕ) : Gates n n := (orBank n).comp (termBank n)

private theorem layer_size (n : ℕ) : (layer n).size = 5 * n := by
  have hterm (j : Fin (2 * n)) : (termEntry n j.val).size = 2 := by
    have h : 0 < n := by have := j.isLt; omega
    simp [termEntry, h, termGate_size]
  simp [layer, orBank, termBank, orEntry, hterm]
  omega

private theorem layer_depth (n : ℕ) : (layer n).depth ≤ 3 := by
  have hterm : (termBank n).depth ≤ 2 := by
    apply Circuit.depth_pi_le
    intro j
    unfold termEntry
    split
    · exact (Circuit.depth_comp_le _ _).trans (by simp [termGate_depth])
    · simp
  have hor : (orBank n).depth ≤ 1 := by
    apply Circuit.depth_pi_le
    intro j
    simp [orEntry, j.isLt, Circuit.depth_oneGate]
  exact (Circuit.depth_comp_le _ _).trans (Nat.add_le_add hor hterm)

private theorem layer_eval (x : Bits n) (j : Fin n) (h : 2 * j.val + 1 < n) :
    bit ((layer n).eval interpretation x j) =
      bit (x ⟨2 * j.val, by omega⟩) + bit (x ⟨2 * j.val + 1, h⟩) := by
  have hn : 0 < n := by omega
  simp only [layer, Circuit.eval_comp, orBank, Circuit.eval_pi, orEntry, j.isLt, ↓reduceDIte]
  change bit ((termBank n).eval interpretation x ⟨2 * j.val, by omega⟩ ||
    (termBank n).eval interpretation x ⟨2 * j.val + 1, by omega⟩) = _
  simp only [termBank, Circuit.eval_pi, termEntry, hn, ↓reduceDIte,
    Circuit.eval_comp, Circuit.eval_wiring, termGate_eval, Function.comp_apply,
    Fin.val_zero, Fin.val_one]
  simp only [Nat.mul_div_cancel_left j.val (by decide : 0 < 2), Nat.mul_mod_right,
    Nat.zero_ne_one, Nat.add_zero, Nat.mul_add_div (by decide : 0 < 2),
    Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega : 1 < 2),
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega : 2 * j.val < n), Nat.div_eq_of_lt (by decide : 1 < 2)]
  cases x ⟨2 * j.val, by omega⟩ <;> cases x ⟨2 * j.val + 1, h⟩ <;> rfl

private def stages (n : ℕ) : ℕ → Gates n n
  | 0 => Circuit.wiring signature id
  | d + 1 => (layer n).comp (stages n d)

private theorem stages_depth (n d : ℕ) : (stages n d).depth ≤ 3 * d := by
  induction d with
  | zero => simp [stages]
  | succ d ih =>
    exact (Circuit.depth_comp_le _ _).trans (by
      have := layer_depth n
      omega)

private theorem stages_size (n d : ℕ) : (stages n d).size = 5 * n * d := by
  induction d with
  | zero => simp [stages]
  | succ d ih =>
    simp [stages, layer_size, ih]
    ring

private def blockSum (x : Bits n) (d j : ℕ) : F₂ :=
  ∑ k ∈ Finset.range (2 ^ d), if h : 2 ^ d * j + k < n then bit (x ⟨_, h⟩) else 0

private theorem stages_eval (x : Bits n) (d : ℕ) (j : Fin n) (h : 2 ^ d * (j.val + 1) ≤ n) :
    bit ((stages n d).eval interpretation x j) = blockSum x d j.val := by
  induction d generalizing j with
  | zero => simp [stages, Circuit.eval_wiring, blockSum, j.isLt]
  | succ d ih =>
    have hp := Nat.two_pow_pos d
    rw [pow_succ] at h
    have hj : 2 * j.val + 1 < n := by nlinarith
    have hleft : 2 ^ d * (2 * j.val + 1) ≤ n := by nlinarith
    have hright : 2 ^ d * (2 * j.val + 1 + 1) ≤ n := by nlinarith
    rw [stages, Circuit.eval_comp, layer_eval _ j hj, ih _ hleft, ih _ hright]
    simp only [blockSum, pow_succ, Nat.mul_two, Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have he : 2 ^ d * (2 * j.val) + k = (2 ^ d + 2 ^ d) * j.val + k := by ring
      simp [he]
    · apply Finset.sum_congr rfl
      intro k hk
      have he : 2 ^ d * (2 * j.val + 1) + k =
          (2 ^ d + 2 ^ d) * j.val + (2 ^ d + k) := by ring
      simp [he]

private def orGateCode (j : ℕ) : Op × List ℕ := (.or, [2 * j, 2 * j + 1])

private theorem orBank_code (n : ℕ) :
    (orBank n).code = ((List.range n).map orGateCode, (List.range n).map (2 * n + ·)) := by
  rw [orBank, CircuitWriter.pi_inputGate_code _ (fun i : Fin n => orGateCode i.val)]
  · simp only [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map, Function.comp_def]
  · intro j
    simp only [orEntry, j.isLt, ↓reduceDIte]
    rfl
  · intro j i hi
    simp only [orGateCode, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> have := j.isLt <;> omega

private theorem layer_consecutive (n : ℕ) :
    UniformComposition.Consecutive n n (layer n).code := by
  have hs : (orBank n).size = n := by
    simp [orBank, orEntry]
  constructor
  · rw [Circuit.length_code_fst, layer, Circuit.size_comp, hs]
    omega
  · rw [Circuit.length_code_fst, layer, Circuit.size_comp, hs, ← compCode_code, orBank_code]
    simp only [compCode, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro j _
    have hlen : (termBank n).code.2.length = 2 * n := by simp [Circuit.code]
    rw [compCodeWire, hlen, ite_eq_right (by omega : ¬ 2 * n + j < 2 * n),
      Circuit.length_code_fst]
    omega

private theorem termEntry_logspace :
    ComputableInLogSpace (fun p : ℕ × ℕ => (termEntry p.1 p.2).code)
      (encPair encUnary encUnary) encCode := by
  let enc := encPair encUnary encUnary
  have hn := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  have hhalf := hj.unaryDiv (ComputableInLogSpace.const 2)
  have hrem := hj.unaryMod (ComputableInLogSpace.const 2)
  have hb := hrem.unaryEq (ComputableInLogSpace.const 1)
  have hterm := hb.ite (ComputableInLogSpace.const (encMid := encCode) (termGate true).code)
    (ComputableInLogSpace.const (encMid := encCode) (termGate false).code)
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hwire := (((hhalf.unaryMulConst 2).comp hp).unaryAdd hi).unaryMod (hn.comp hp)
  have hwireCode : ComputableInLogSpace (fun p : ℕ × ℕ => (([],
      (List.range 2).map (fun k => (2 * (p.2 / 2) + k) % p.1)) : CodeLogspace.RawCode))
      enc encCode :=
    ((ComputableInLogSpace.const (encMid := encList encGate) []).pair
      (CodeLogspace.map_range (ComputableInLogSpace.const 2) hwire.unaryToBinary)).congr_fun
      (fun _ => by simp [Nat.mul_comm])
  have hbound (p : ℕ × ℕ) : CodeLogspace.BoundedReferences
      ((([], (List.range 2).map (fun k => (2 * (p.2 / 2) + k) % p.1)) :
        CodeLogspace.RawCode).2.length + (termGate (p.2 % 2 = 1)).code.1.length)
      (termGate (p.2 % 2 = 1)).code := by
    simp only [List.length_map, List.length_range]
    rw [Circuit.length_code_fst]
    exact CodeLogspace.circuit_boundedReferences _
  have hterm' : ComputableInLogSpace (fun p : ℕ × ℕ => (termGate (p.2 % 2 = 1)).code)
      enc encCode := hterm.congr_fun (fun p => by
    simp only [decide_eq_true_eq]
    split <;> simp_all)
  have hcomp := CodeLogspace.compCode_logspace hn hterm' hwireCode hbound
  have hpos := (ComputableInLogSpace.const 0).unaryLt hn
  exact (hpos.ite hcomp (Code.constant hn false)).congr_fun fun p => by
    simp only [termEntry, decide_eq_true_eq]
    split_ifs with h
    · rw [← compCode_code, Circuit.code_wiring_eq_map]
      intro i
      rfl
    · rfl

private theorem termBank_logspace :
    ComputableInLogSpace (fun n => (termBank n).code) encUnary encCode := by
  have hm : ComputableInLogSpace (fun n => 2 * n) encUnary encUnary :=
    (ComputableInLogSpace.id.unaryMulConst 2).congr_fun (fun n => Nat.mul_comm _ _)
  exact Code.bank ComputableInLogSpace.id hm termEntry_logspace

private theorem orBank_logspace :
    ComputableInLogSpace (fun n => (orBank n).code) encUnary encCode := by
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have hn := ComputableInLogSpace.fst encUnary encUnary
  have ht := hi.unaryMulConst 2
  have ht1 := ht.unaryAdd (ComputableInLogSpace.const 1)
  have hg : ComputableInLogSpace (fun p : ℕ × ℕ => orGateCode p.2)
      (encPair encUnary encUnary) encGate :=
    (ComputableInLogSpace.const (encMid := encOp) Op.or).pair
      ((ht.unaryToBinary.listCons (ComputableInLogSpace.listSingleton.comp
        ht1.unaryToBinary)).congr_fun (fun _ => by simp [Nat.mul_comm]))
  have hout := CodeLogspace.map_range ComputableInLogSpace.id
    (((hn.unaryMulConst 2).unaryAdd hi).unaryToBinary)
  exact ((CodeLogspace.map_range ComputableInLogSpace.id hg).pair hout).congr_fun
    (fun n => by simpa [Nat.mul_comm] using orBank_code n)

private theorem layer_logspace :
    ComputableInLogSpace (fun n => (layer n).code) encUnary encCode :=
  CodeLogspace.circuit_comp_logspace ComputableInLogSpace.id termBank_logspace orBank_logspace

private theorem stages_succ_code (n d : ℕ) :
    (stages n (d + 1)).code =
      UniformComposition.sequentialCodes n (layer n).code (List.replicate d (layer n).code) := by
  induction d with
  | zero =>
    rw [stages, stages, ← compCode_code, Circuit.code_wiring_id]
    have h i : compCodeWire n ([], List.range n) i = i := by
      by_cases hi : i < n <;> simp [compCodeWire, List.getD_eq_getElem?_getD, hi]
      omega
    have hfun : compCodeWire n ([], List.range n) = id := funext h
    simp [compCode, hfun, UniformComposition.sequentialCodes]
  | succ d ih =>
    rw [stages, ← compCode_code, ih, List.replicate_succ', UniformComposition.sequentialCodes_snoc]

private theorem stages_logspace {α : Type} {enc : α ↪ List Bool} {n d : α → ℕ}
    (hn : ComputableInLogSpace n enc encUnary) (hd : ComputableInLogSpace d enc encUnary) :
    ComputableInLogSpace (fun a => (stages (n a) (d a)).code) enc encCode := by
  have hlocal := layer_logspace.comp hn
  have hcount := hd.unarySub (ComputableInLogSpace.const 1)
  have hsteps : ComputableInLogSpace (fun a => List.replicate (d a - 1) (layer (n a)).code)
      enc (encList encCode) := by
    refine (CodeLogspace.map_range hcount
      (hlocal.comp (ComputableInLogSpace.fst enc encUnary))).congr_fun ?_
    intro a
    simp [List.map_const']
  have hchain := UniformComposition.sequentialCodes_logspace hn hn hlocal hsteps
    (fun a => layer_consecutive (n a))
    (fun a c hc => by
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hc
      exact layer_consecutive (n a))
    (fun a c hc => by
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hc
      rw [Circuit.length_code_fst]
      exact CodeLogspace.circuit_boundedReferences _)
  have hzero := hd.unaryEq (ComputableInLogSpace.const 0)
  exact (hzero.ite (UniformComposition.identityCode_logspace hn) hchain).congr_fun fun a => by
    cases d a with
    | zero => simp [stages, Circuit.code_wiring_id]
    | succ e => simp [stages_succ_code]

/-- A uniform parity network on a complete binary tree, with other input
sizes still assigned a total circuit. -/
def reduce (n d : ℕ) : Gates n 1 :=
  if hn : 0 < n then (wireBit ⟨0, hn⟩).comp (stages n d) else constBit n false

theorem reduce_depth (n d : ℕ) (hn : 0 < n) : (reduce n d).depth ≤ 3 * d := by
  rw [reduce, dite_eq_left hn]
  exact (Circuit.depth_comp_le _ _).trans (by simpa using stages_depth n d)

theorem reduce_size (n d : ℕ) (hn : 0 < n) : (reduce n d).size = 5 * n * d := by
  simp [reduce, hn, stages_size]

theorem reduce_eval {n d : ℕ} (h : n = 2 ^ d) (x : Bits n) :
    bit ((reduce n d).eval interpretation x 0) = ∑ j, bit (x j) := by
  subst n
  have hp := Nat.two_pow_pos d
  rw [reduce, dite_eq_left hp, Circuit.eval_comp, wireBit_eval, stages_eval _ d ⟨0, hp⟩ (by simp)]
  simp only [blockSum, Nat.mul_zero, Nat.zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun j _ => dite_eq_left j.isLt)

theorem reduce_code_logspace {α : Type} {enc : α ↪ List Bool} {n d : α → ℕ}
    (hn : ComputableInLogSpace n enc encUnary) (hd : ComputableInLogSpace d enc encUnary) :
    ComputableInLogSpace (fun a => (reduce (n a) (d a)).code) enc encCode := by
  have hs := stages_logspace hn hd
  have hc : ComputableInLogSpace (fun _ : α => (([], [0]) : CodeLogspace.RawCode))
      enc encCode := ComputableInLogSpace.const _
  have hcomp := CodeLogspace.compCode_logspace hn hc hs (fun a => by
    simp [CodeLogspace.BoundedReferences])
  have hpos := (ComputableInLogSpace.const 0).unaryLt hn
  exact (hpos.ite hcomp (Code.constant hn false)).congr_fun fun a => by
    simp only [reduce, decide_eq_true_eq]
    split_ifs
    · rw [← compCode_code, wireBit, Circuit.code_wiring]
      rfl
    · rfl

end PredictionDepth.FrozenPascal.UniformXor
