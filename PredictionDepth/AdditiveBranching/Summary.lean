import PredictionDepth.AdditiveBranching
import PredictionDepth.Complexity.BlockSummary
import PredictionDepth.FrozenPascal.UniformGuards
import PredictionDepth.FrozenPascal.CoefficientUniform

/-! A three-bit ordered summary for additive controls with unconditional hops. -/

namespace PredictionDepth.AdditiveBranching

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open FrozenPascal (Gates bit bit_and bit_xor bit_injective bit_ofBoolRing)
open Linear (F₂)
open scoped BigOperators

/-- The empty block has zero data and parity and satisfies the zero-control test. -/
def emptySummary : Bits 3 := ![true, false, false]

/-- A site contributes its zero-control flag, data bit, and masked control bit. -/
def leafSummary (mask : Bool) (site : Bits 2) : Bits 3 :=
  ![!site 0, site 1, mask && site 0]

/-- Concatenation keeps data from the left block only when all right controls are zero. -/
def mergeSummary (left right : Bits 3) : Bits 3 :=
  ![left 0 && right 0, (left 1 && right 0) ^^ right 1, left 2 ^^ right 2]

/-- The terminal data wire bypasses the summary. -/
def readSummary (s : Bits 3) (terminal : Bool) : Bool := terminal ^^ (s 2 && s 1)

private def xorOf (a b : Gates n 1) : Gates n 1 := FrozenPascal.xorGate.comp (a.append b)

@[simp] private theorem xorOf_eval (a b : Gates n 1) (x : Bits n) :
    (xorOf a b).eval interpretation x 0 =
      (a.eval interpretation x 0 ^^ b.eval interpretation x 0) := by
  rw [xorOf, Circuit.eval_comp, Circuit.eval_append, FrozenPascal.xorGate_eval]
  rfl

/-- All dynamic data in a leaf are two input wires. The generator chooses its Lucas mask. -/
def leafGate (mask : Bool) : Gates 2 3 :=
  Circuit.pi ![Circuit.oneGate (σ := signature) .not (fun _ => 0),
    FrozenPascal.wireBit 1,
    if mask then FrozenPascal.wireBit 0 else FrozenPascal.constBit 2 false]

/-- Constant identity for an empty prefix or padding. -/
def emptyGate : Gates 0 3 := Circuit.pi fun i => FrozenPascal.constBit 0 (emptySummary i)

/-- Input wires are the left summary followed by the right summary. -/
def mergeGate : Gates 6 3 :=
  Circuit.pi ![FrozenPascal.conjoin (FrozenPascal.wireBit 0) (FrozenPascal.wireBit 3),
    xorOf (FrozenPascal.conjoin (FrozenPascal.wireBit 1) (FrozenPascal.wireBit 3))
      (FrozenPascal.wireBit 4),
    xorOf (FrozenPascal.wireBit 2) (FrozenPascal.wireBit 5)]

/-- Read out the summary and the bypassed terminal data bit. -/
def readGate : Gates 4 1 :=
  xorOf (FrozenPascal.wireBit 3)
    (FrozenPascal.conjoin (FrozenPascal.wireBit 2) (FrozenPascal.wireBit 1))

theorem leafGate_eval (mask : Bool) (site : Bits 2) :
    (leafGate mask).eval interpretation site = leafSummary mask site := by
  rw [leafGate, Circuit.eval_pi]
  funext i
  fin_cases i <;> cases mask <;> rfl

theorem emptyGate_eval (x : Bits 0) : emptyGate.eval interpretation x = emptySummary := by
  simp [emptyGate]

theorem mergeGate_eval (left right : Bits 3) :
    mergeGate.eval interpretation (Fin.append left right) = mergeSummary left right := by
  rw [mergeGate, Circuit.eval_pi]
  funext i
  fin_cases i <;> simp [mergeSummary] <;> rfl

theorem readGate_eval (s : Bits 3) (terminal : Bits 1) :
    readGate.eval interpretation (Fin.append s terminal) 0 = readSummary s (terminal 0) := by
  simp only [readGate, xorOf_eval, FrozenPascal.wireBit_eval, FrozenPascal.conjoin_eval]
  rfl

theorem leafGate_depth (mask : Bool) : (leafGate mask).depth ≤ 1 := by
  cases mask <;> decide +kernel

theorem leafGate_size (mask : Bool) : (leafGate mask).size ≤ 2 := by
  cases mask <;> decide +kernel

theorem emptyGate_depth : emptyGate.depth ≤ 1 := by decide +kernel

theorem emptyGate_size : emptyGate.size ≤ 3 := by decide +kernel

theorem mergeGate_depth : mergeGate.depth ≤ 4 := by decide +kernel

theorem mergeGate_size : mergeGate.size ≤ 12 := by decide +kernel

theorem readGate_depth : readGate.depth ≤ 4 := by decide +kernel

theorem readGate_size : readGate.size ≤ 6 := by decide +kernel

@[simp] private theorem bit_not (b : Bool) : bit (!b) = 1 + bit b := by cases b <;> rfl

theorem mergeSummary_assoc (l m r : Bits 3) :
    mergeSummary (mergeSummary l m) r = mergeSummary l (mergeSummary m r) := by
  funext i
  apply bit_injective
  fin_cases i <;> simp [mergeSummary] <;> ring

theorem mergeSummary_leftId (r : Bits 3) : mergeSummary emptySummary r = r := by
  funext i
  fin_cases i <;> simp [mergeSummary, emptySummary]

theorem mergeSummary_rightId (l : Bits 3) : mergeSummary l emptySummary = l := by
  funext i
  fin_cases i <;> simp [mergeSummary, emptySummary]


/-- Each site strictly before time `t` supplies a control/data pair.
The final site supplies only its data wire, which bypasses the summary. -/
abbrev InputWidth (t : ℕ) : ℕ := 2 * t + 1

def siteWire (j : Fin t) (b : Fin 2) : Fin (InputWidth t) :=
  ⟨2 * j.val + b.val, by have := j.isLt; have := b.isLt; unfold InputWidth; omega⟩

def terminalWire (t : ℕ) : Fin (InputWidth t) := Fin.last (2 * t)

/-- Sample the explicit interleaved window at the origin. -/
def sample (t : ℕ) (x : FrozenPascal.Config F₂) : Bits (InputWidth t) := fun i =>
  if i.val = 2 * t then ofBoolRing (x.2 t)
  else if i.val % 2 = 0 then ofBoolRing (x.1 (i.val / 2 : ℕ))
  else ofBoolRing (x.2 (i.val / 2 : ℕ))

@[simp] theorem sample_site (t : ℕ) (x : FrozenPascal.Config F₂) (j : Fin t) (b : Fin 2) :
    sample t x (siteWire j b) = ![ofBoolRing (x.1 j.val), ofBoolRing (x.2 j.val)] b := by
  have hj := j.isLt
  have hb := b.isLt
  have hterminal : 2 * j.val + b.val ≠ 2 * t := by omega
  have hdiv : (2 * j.val + b.val) / 2 = j.val := by omega
  have hmod : (2 * j.val + b.val) % 2 = b.val := by omega
  simp only [sample, siteWire, hterminal, hdiv, hmod, ↓reduceIte]
  fin_cases b <;> rfl

@[simp] theorem sample_terminal (t : ℕ) (x : FrozenPascal.Config F₂) :
    sample t x (terminalWire t) = ofBoolRing (x.2 t) := by simp [sample, terminalWire]

/-- Extend a sampled window by zero to an infinite initial configuration. -/
def decode (t : ℕ) (u : Bits (InputWidth t)) : FrozenPascal.Config F₂ :=
  (fun i => bit (FrozenPascal.extendTrack (fun j : Fin t => u (siteWire j 0)) i),
    fun i => bit (FrozenPascal.extendTrack
      (Fin.lastCases (u (terminalWire t)) (fun j : Fin t => u (siteWire j 1))) i))

theorem sample_decode (t : ℕ) (u : Bits (InputWidth t)) : sample t (decode t u) = u := by
  have hb (v : Bool) : ofBoolRing (bit v) = v := bit_injective (by simp)
  funext i
  by_cases h : i.val = 2 * t
  · have hi : i = terminalWire t := Fin.ext h
    subst i
    rw [sample_terminal]
    change ofBoolRing (bit (FrozenPascal.extendTrack _ ((Fin.last t).val : ℤ))) = _
    rw [FrozenPascal.extendTrack_fin, Fin.lastCases_last, hb]
  · have hi := i.isLt
    let j : Fin t := ⟨i.val / 2, by unfold InputWidth at hi; omega⟩
    let b : Fin 2 := ⟨i.val % 2, by omega⟩
    have he : i = siteWire j b := Fin.ext (by change i.val = 2 * (i.val / 2) + i.val % 2; omega)
    rw [he, sample_site]
    rcases Fin.eq_zero_or_eq_succ b with h₀ | ⟨b', h₁⟩
    · rw [h₀]
      change ofBoolRing (bit (FrozenPascal.extendTrack _ (j.val : ℤ))) = _
      rw [FrozenPascal.extendTrack_fin, hb]
    · have h' : b = 1 := h₁.trans (congrArg Fin.succ (Subsingleton.elim b' 0))
      rw [h']
      change ofBoolRing (bit (FrozenPascal.extendTrack _ (j.castSucc.val : ℤ))) = _
      rw [FrozenPascal.extendTrack_fin, Fin.lastCases_castSucc, hb]

/-- The site circuit on the complete window, with identity in padded slots. -/
def block (t j : ℕ) : Gates (InputWidth t) 3 :=
  if h : j < t then
    (leafGate (FrozenPascal.chooseParity t j)).comp (Circuit.wiring signature (siteWire ⟨j,h⟩))
  else emptyGate.comp (Circuit.wiring signature Fin.elim0)

theorem block_eval (t j : ℕ) (x : Bits (InputWidth t)) :
    (block t j).eval interpretation x =
      if h : j < t then leafSummary (FrozenPascal.chooseParity t j) (x ∘ siteWire ⟨j,h⟩)
      else emptySummary := by
  unfold block
  split <;> simp [Circuit.eval_comp, leafGate_eval, emptyGate_eval]

theorem block_depth (t j : ℕ) : (block t j).depth ≤ 1 := by
  unfold block
  split
  · exact (Circuit.depth_comp_le _ _).trans (by simpa using leafGate_depth (FrozenPascal.chooseParity t j))
  · exact (Circuit.depth_comp_le _ _).trans (by simpa using emptyGate_depth)

theorem block_size (t j : ℕ) : (block t j).size ≤ 3 := by
  unfold block
  split
  · exact (Circuit.size_comp _ _).le.trans (by simpa using
      (leafGate_size (FrozenPascal.chooseParity t j)).trans (by decide : 2 ≤ 3))
  · exact (Circuit.size_comp _ _).le.trans (by simpa using emptyGate_size)

/-- The only context wire is the terminal datum. -/
def contextGate (t : ℕ) : Gates (InputWidth t) 1 := FrozenPascal.wireBit (terminalWire t)

open StandardComplexity Turing.MultiTapeTM

theorem inputWidth_logspace : ComputableInLogSpace InputWidth encUnary encUnary :=
  (ComputableInLogSpace.const 2).unaryMul ComputableInLogSpace.id
    |>.unaryAdd (ComputableInLogSpace.const 1)

/-- A block writer scans two unary indices and prints the fixed leaf template,
the appropriate relocated wires, or the constant identity when padded. -/
theorem block_code_logspace : ComputableInLogSpace
    (fun p : ℕ × ℕ => (block p.1 p.2).code) (encPair encUnary encUnary) encCode := by
  let enc := encPair encUnary encUnary
  have ht := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  have hw := inputWidth_logspace.comp ht
  have hmask := FrozenPascal.chooseParity_logspace ht hj
  have hleaf : ComputableInLogSpace
      (fun p : ℕ × ℕ => (leafGate (FrozenPascal.chooseParity p.1 p.2)).code) enc encCode := by
    refine (hmask.ite (ComputableInLogSpace.const (leafGate true).code)
      (ComputableInLogSpace.const (leafGate false).code)).congr_fun ?_
    intro p
    cases FrozenPascal.chooseParity p.1 p.2 <;> rfl
  have hc := (ComputableInLogSpace.const 2).unaryMul hj
  have hx := hc.unaryAdd (ComputableInLogSpace.const 1)
  have houtputs : ComputableInLogSpace (fun p : ℕ × ℕ => [2 * p.2, 2 * p.2 + 1])
      enc (encList encNat) :=
    hc.unaryToBinary.listCons (ComputableInLogSpace.listSingleton.comp hx.unaryToBinary)
  have hwire := (ComputableInLogSpace.const (encMid := encList encGate) []).pair houtputs
  have hblock := CodeLogspace.compCode_logspace hw hleaf hwire (fun p => by
    rw [Circuit.length_code_fst]
    exact CodeLogspace.circuit_boundedReferences (leafGate (FrozenPascal.chooseParity p.1 p.2)))
  have hpad : ComputableInLogSpace _ enc encCode :=
    CodeLogspace.compCode_logspace hw (ComputableInLogSpace.const emptyGate.code)
      (ComputableInLogSpace.const ([], [])) (fun _ => by
        rw [Circuit.length_code_fst]
        exact CodeLogspace.circuit_boundedReferences emptyGate)
  refine ((hj.unaryLt ht).ite hblock hpad).congr_fun ?_
  intro p
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [block, dite_eq_left h, ← compCode_code, Circuit.code_wiring]
    rfl
  · rw [block, dite_eq_right h, ← compCode_code, Circuit.code_wiring, List.ofFn_zero]
    rfl

theorem contextGate_code_logspace :
    ComputableInLogSpace (fun t => (contextGate t).code) encUnary encCode := by
  have href : ComputableInLogSpace (fun t : ℕ => 2 * t) encUnary encNat :=
    ((ComputableInLogSpace.const 2).unaryMul ComputableInLogSpace.id).unaryToBinary
  exact ((ComputableInLogSpace.const (encMid := encList encGate) []).pair
    (ComputableInLogSpace.listSingleton.comp href)).congr_fun (fun _ => rfl)


theorem summaryLaws : BlockSummary.Laws mergeSummary emptySummary :=
  ⟨mergeSummary_assoc, mergeSummary_leftId, mergeSummary_rightId⟩

private def prefixSummary (n : ℕ) (control data mask : ℕ → Bool) : Bits 3 :=
  BlockSummary.summarize mergeSummary emptySummary (List.ofFn fun j : Fin n =>
    leafSummary (mask j.val) ![control j.val, data j.val])

/-- Sum of data from sites followed only by zero controls in the prefix. -/
private def suffixValue (a b : ℕ → F₂) (n : ℕ) : F₂ :=
  ∑ k ∈ Finset.range n, (∏ j ∈ Finset.Ioo k n, (1 + a j)) * b k

private theorem suffixValue_succ (a b : ℕ → F₂) (n : ℕ) :
    suffixValue a b (n + 1) = suffixValue a b n * (1 + a n) + b n := by
  unfold suffixValue
  rw [Finset.sum_range_succ, Finset.sum_mul]
  have hlast : Finset.Ioo n (n + 1) = ∅ := by ext j; simp
  simp only [hlast, Finset.prod_empty, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  have hs : Finset.Ioo k (n + 1) = insert n (Finset.Ioo k n) := by
    ext j
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  have hn : n ∉ Finset.Ioo k n := by simp
  rw [hs, Finset.prod_insert hn]
  ring

private theorem prefixSummary_values (n : ℕ) (c x mask : ℕ → Bool) :
    bit (prefixSummary n c x mask 0) = ∏ j ∈ Finset.range n, (1 + bit (c j)) ∧
    bit (prefixSummary n c x mask 1) =
      suffixValue (bit ∘ c) (bit ∘ x) n ∧
    bit (prefixSummary n c x mask 2) =
      ∑ j ∈ Finset.range n, bit (mask j) * bit (c j) := by
  induction n with
  | zero => simp [prefixSummary, BlockSummary.summarize, emptySummary, suffixValue]
  | succ n ih =>
    have h : prefixSummary (n + 1) c x mask =
        mergeSummary (prefixSummary n c x mask) (leafSummary (mask n) ![c n, x n]) := by
      rw [prefixSummary, List.ofFn_succ_last, BlockSummary.summarize_append summaryLaws]
      simp [prefixSummary, BlockSummary.summarize, mergeSummary_rightId]
    rw [h, suffixValue_succ, Finset.sum_range_succ, Finset.prod_range_succ]
    simp [mergeSummary, leafSummary, ih.1, ih.2.1, ih.2.2]

private theorem prefixSummary_correct (t : ℕ) (x : FrozenPascal.Config F₂) :
    readSummary
      (prefixSummary t (fun j => ofBoolRing (x.1 j)) (fun j => ofBoolRing (x.2 j))
        (FrozenPascal.chooseParity t))
      (ofBoolRing (x.2 t)) = ofBoolRing ((step^[t] x).2 0) := by
  let s := prefixSummary t (fun j => ofBoolRing (x.1 j)) (fun j => ofBoolRing (x.2 j))
    (FrozenPascal.chooseParity t)
  change readSummary s _ = _
  have hs := prefixSummary_values t (fun j => ofBoolRing (x.1 j))
    (fun j => ofBoolRing (x.2 j)) (FrozenPascal.chooseParity t)
  have hQ : bit (s 2) = trimmedParity x.1 0 t := by
    rw [hs.2.2, trimmedParity_eq_sum]
    simp only [bit_ofBoolRing, zero_add]
    simp only [FrozenPascal.chooseParity_correct]
  have hV : bit (s 1) = ∑ k ∈ Finset.range t, zeroSuffix x.1 0 t k * x.2 k := by
    rw [hs.2.1]
    simp [suffixValue, zeroSuffix]
  apply bit_injective
  rw [readSummary, bit_xor, bit_and, bit_ofBoolRing, hQ, hV,
    iterate_data, bit_ofBoolRing, Finset.sum_range_succ, coefficient_diag, one_mul, zero_add]
  rw [Finset.mul_sum, add_comm (x.2 _)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkt := Finset.mem_range.mp hk
  rw [coefficient, ite_eq_left hkt, zero_add, ← mul_assoc, mul_comm (trimmedParity _ _ _)]

private theorem summarize_padded_blocks (t m : ℕ) (htm : t ≤ m) (x : FrozenPascal.Config F₂) :
    BlockSummary.summarize mergeSummary emptySummary (List.ofFn fun j : Fin m =>
      (block t j.val).eval interpretation (sample t x)) =
      prefixSummary t (fun j => ofBoolRing (x.1 j)) (fun j => ofBoolRing (x.2 j))
        (FrozenPascal.chooseParity t) := by
  simp only [block_eval]
  have h : ∀ j : Fin t, (sample t x ∘ siteWire j) =
      ![ofBoolRing (x.1 j.val), ofBoolRing (x.2 j.val)] := fun j =>
    funext (sample_site t x j)
  simpa only [h, prefixSummary] using BlockSummary.summarize_pad_le summaryLaws
    (fun j : Fin t => leafSummary (FrozenPascal.chooseParity t j.val)
      ![ofBoolRing (x.1 j.val), ofBoolRing (x.2 j.val)]) htm

private theorem combine_mergeGate : BlockSummary.combine mergeGate = mergeSummary := by
  funext a b
  exact mergeGate_eval a b

/-- Pad the time prefix to a power of two using the identity circuit. -/
def initialGate (t : ℕ) : Gates (InputWidth t) (2 ^ BlockSummary.paddingDepth t * 3) :=
  BlockSummary.bank (fun j : Fin (BlockSummary.paddedCount t) => block t j.val)

theorem initialGate_code_logspace :
    ComputableInLogSpace (fun t => (initialGate t).code) encUnary encCode := by
  apply BlockSummary.bank_code_logspace
    (cs := fun t (j : Fin (BlockSummary.paddedCount t)) => block t j.val)
    inputWidth_logspace BlockSummary.paddedCount_logspace
  have ht := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  refine ((hj.unaryLt (BlockSummary.paddedCount_logspace.comp ht)).ite block_code_logspace
    (ComputableInLogSpace.const ([], []))).congr_fun ?_
  intro p
  simp only [decide_eq_true_eq, Function.comp_apply]
  split_ifs <;> rfl

/-- The additive predictor is an instance of the generic ordered-summary compiler. -/
def prediction (t : ℕ) : Gates (InputWidth t) 1 :=
  BlockSummary.compile mergeGate (BlockSummary.paddingDepth t) (initialGate t) (contextGate t) readGate

theorem prediction_correct (t : ℕ) (x : FrozenPascal.Config F₂) :
    (prediction t).eval interpretation (sample t x) 0 = ofBoolRing ((step^[t] x).2 0) := by
  have laws : BlockSummary.Laws (BlockSummary.combine mergeGate) emptySummary := by
    rw [combine_mergeGate]
    exact summaryLaws
  unfold prediction
  rw [congrFun (BlockSummary.compile_eval mergeGate laws _ (initialGate t)
    (contextGate t) readGate (sample t x)) 0, combine_mergeGate, readGate_eval]
  have hbank := funext (BlockSummary.bank_eval
    (fun j : Fin (BlockSummary.paddedCount t) => block t j.val) (sample t x))
  change readSummary (BlockSummary.summarize mergeSummary emptySummary (List.ofFn
    (BlockSummary.unpack ((BlockSummary.bank (fun j : Fin (BlockSummary.paddedCount t) =>
      block t j.val)).eval interpretation (sample t x))))) (sample t x (terminalWire t)) = _
  rw [hbank, sample_terminal,
    summarize_padded_blocks t (BlockSummary.paddedCount t) (BlockSummary.le_paddedCount t)]
  exact prefixSummary_correct t x

/-- Includes the compiler's initial and per-round copy layers. -/
theorem prediction_depth (t : ℕ) : (prediction t).depth ≤ 6 + 5 * Nat.clog 2 t := by
  have h := BlockSummary.compile_depth mergeGate (BlockSummary.paddingDepth t)
    (initialGate t) (contextGate t) readGate
  have hi : (initialGate t).depth ≤ 1 := BlockSummary.bank_depth _ (fun j => block_depth t j.val)
  have hm := Nat.mul_le_mul_left (BlockSummary.paddingDepth t) (Nat.add_le_add_right mergeGate_depth 1)
  change (prediction t).depth ≤ _ at h
  simp only [contextGate, FrozenPascal.wireBit_depth, max_eq_left (Nat.zero_le _),
    BlockSummary.paddingDepth_eq_clog] at h
  rw [BlockSummary.paddingDepth_eq_clog] at hm
  have hr := readGate_depth
  omega

/-- The halving schedule uses linearly many gates, including copies. -/
theorem prediction_size (t : ℕ) : (prediction t).size ≤ 108 * (t + 1) := by
  have h := BlockSummary.compile_size mergeGate (BlockSummary.paddingDepth t)
    (initialGate t) (contextGate t) readGate
  have hi : (initialGate t).size ≤ BlockSummary.paddedCount t * 3 * 3 :=
    BlockSummary.bank_size _ (fun j => block_size t j.val)
  have hm := Nat.mul_le_mul_left (BlockSummary.paddedCount t - 1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 mergeGate_size) 3)
  have hr := readGate_size
  have hp := BlockSummary.paddedCount_le t
  change (prediction t).size ≤ (initialGate t).size + BlockSummary.paddedCount t * 3 +
    (BlockSummary.paddedCount t - 1) * (3 * mergeGate.size + 3) + (contextGate t).size +
    readGate.size at h
  simp only [contextGate, FrozenPascal.wireBit_size, add_zero] at h
  omega

theorem prediction_code_logspace :
    ComputableInLogSpace (fun t => (prediction t).code) encUnary encCode := by
  unfold prediction
  exact BlockSummary.compile_code_logspace (enc := encUnary) (w := 3) (k := 1)
    (n := InputWidth) (d := BlockSummary.paddingDepth) mergeGate readGate (initial := initialGate)
    (context := contextGate) inputWidth_logspace BlockSummary.paddingDepth_logspace
    BlockSummary.paddedCount_logspace initialGate_code_logspace contextGate_code_logspace

private theorem inputWidth_of_odd (n : ℕ) (h : n % 2 = 1) : InputWidth (n / 2) = n := by
  unfold InputWidth
  omega

/-- The explicit window has odd length, and every even length is rejected. -/
def predictionFamily : BooleanCircuitFamily := fun n =>
  if h : n % 2 = 1 then FrozenPascal.UniformGuards.castInputs (inputWidth_of_odd n h) (prediction (n / 2))
  else FrozenPascal.constBit n false

theorem predictionFamily_at_time (t : ℕ) : predictionFamily (InputWidth t) = prediction t := by
  have ho : InputWidth t % 2 = 1 := by unfold InputWidth; omega
  have ht : InputWidth t / 2 = t := by unfold InputWidth; omega
  apply Circuit.code_injective
  simp only [predictionFamily, dite_eq_left ho, FrozenPascal.UniformGuards.castInputs_code]
  exact congrArg (fun u : ℕ => (prediction u).code) ht

theorem predictionFamily_code_logspace :
    ComputableInLogSpace (fun n => (predictionFamily n).code) encUnary encCode := by
  have hn : ComputableInLogSpace (fun n : ℕ => n) encUnary encUnary := ComputableInLogSpace.id
  have ht := hn.unaryDiv (ComputableInLogSpace.const 2)
  have ho := (hn.unaryMod (ComputableInLogSpace.const 2)).unaryEq (ComputableInLogSpace.const 1)
  exact (ho.ite (prediction_code_logspace.comp ht) (FrozenPascal.Code.constant hn false)).congr_fun (fun n => by
    simp only [predictionFamily, decide_eq_true_eq, Function.comp_apply]
    split_ifs
    · exact FrozenPascal.UniformGuards.castInputs_code _ _
    · rfl)

theorem predictionFamily_uniform : LogspaceUniform predictionFamily :=
  (ComputableInLogSpace.id.pair predictionFamily_code_logspace).congr (fun _ => rfl)

/-- Semantic prediction on every legal finite input, evaluated on its zero extension. -/
def predictionLanguage : Set (List Bool) :=
  {word | ∃ t, word.length = InputWidth t ∧
    ofBoolRing ((step^[t] (decode t (BitString.ofList (InputWidth t) word))).2 0) = true}

theorem predictionFamily_decides : FamilyDecides predictionFamily predictionLanguage := by
  intro word
  have he (t : ℕ) (hlen : word.length = InputWidth t) :
      evaluateFamily predictionFamily word =
        ofBoolRing ((step^[t] (decode t (BitString.ofList (InputWidth t) word))).2 0) := by
    rw [evaluateFamily, hlen, predictionFamily_at_time]
    simpa only [sample_decode] using prediction_correct t (decode t (BitString.ofList (InputWidth t) word))
  constructor
  · rintro ⟨t, ht, heval⟩
    exact (he t ht).trans heval
  · intro h
    by_cases ho : word.length % 2 = 1
    · exact ⟨word.length / 2, (inputWidth_of_odd word.length ho).symm,
        (he _ (inputWidth_of_odd word.length ho).symm).symm.trans h⟩
    · simp [evaluateFamily, predictionFamily, ho] at h

theorem predictionFamily_depth (n : ℕ) :
    (predictionFamily n).depth ≤ 11 * (Nat.log 2 n + 1) := by
  unfold predictionFamily
  split
  · rw [FrozenPascal.UniformGuards.castInputs_depth]
    have h := prediction_depth (n / 2)
    have ht : n / 2 ≤ n + 1 := by omega
    have hlog := (Nat.clog_mono_right 2 ht).trans (clog_succ_le_log_add_one n)
    omega
  · simp only [FrozenPascal.constBit_depth]
    omega

theorem predictionFamily_size (n : ℕ) :
    (predictionFamily n).size ≤ 108 * (n + 1) := by
  have castSize {m n k : ℕ} (h : m = n) (c : Gates m k) :
      (FrozenPascal.UniformGuards.castInputs h c).size = c.size := by
    subst n
    rfl
  unfold predictionFamily
  split
  · rw [castSize]
    exact (prediction_size (n / 2)).trans
      (Nat.mul_le_mul_left 108 (Nat.add_le_add_right (Nat.div_le_self n 2) 1))
  · simp only [FrozenPascal.constBit_size]
    omega

theorem predictionLanguage_mem_uniformNC_one : predictionLanguage ∈ UniformNCLevel 1 :=
  mem_uniformNCLevel_of_uniform predictionFamily_uniform predictionFamily_decides
    (fun n => by simpa only [pow_one] using predictionFamily_depth n)

/-- The frozen endpoint's stay count and enabled-hop flag, for endpoint one. -/
def frozenEndpointSummary (c : Bits 2) : ℕ × Bool :=
  ((c 0).toNat + (c 1).toNat, true)

/-- Time-two observation at the origin with two controls and three data bits. -/
def endpointObservation (c : Bits 2) (x : Bits 3) : Bool :=
  ofBoolRing ((step^[2]
    (fun i => bit (FrozenPascal.extendTrack c i),
      fun i => bit (FrozenPascal.extendTrack x i))).2 0)

/-- The generic search finds the same-context collision in this finite test domain. -/
theorem frozenEndpoint_search :
    BlockSummary.findCollision? frozenEndpointSummary endpointObservation
      [![true, false], ![false, true]] [![false, true, false]] =
      some (![true, false], ![false, true], ![false, true, false]) := by
  decide +kernel

/-- Swapping the two controls preserves the frozen endpoint summary.
The same data context distinguishes the actual evolving predictions. -/
theorem frozenEndpointCollision :
    BlockSummary.Collision frozenEndpointSummary endpointObservation
      ![true, false] ![false, true] ![false, true, false] :=
  BlockSummary.findCollision?_sound frozenEndpoint_search

theorem frozenEndpoint_noReadout :
    ¬ ∃ read : (ℕ × Bool) → Bits 3 → Bool, ∀ c x,
      read (frozenEndpointSummary c) x = endpointObservation c x :=
  frozenEndpointCollision.noReadout

end PredictionDepth.AdditiveBranching
