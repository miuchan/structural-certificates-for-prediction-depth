import PredictionDepth.BlockSummary
import PredictionDepth.Complexity.VariableChain
import PredictionDepth.Complexity.UniformComposition
import PredictionDepth.FrozenPascal.UniformWeightWidths
import PredictionDepth.FrozenPascal.UniformWeightPrimitives

/-! Compile ordered, fixed-width summaries by halving the bank of active blocks. -/

namespace PredictionDepth.BlockSummary

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition StandardComplexity Turing.MultiTapeTM
open CodeLogspace CodeLogspaceFamilies OutputNormalization

local notation "Gates" => Circuit signature

def paddingDepth (m : ℕ) : ℕ := (m - 1).size

def paddedCount (m : ℕ) : ℕ := 2 ^ paddingDepth m

theorem paddingDepth_eq_clog (m : ℕ) : paddingDepth m = Nat.clog 2 m := by
  cases m with
  | zero => rfl
  | succ m => simp [paddingDepth, RegularReduction.size_eq_clog_succ]

theorem le_paddedCount (m : ℕ) : m ≤ paddedCount m := by
  rw [paddedCount, paddingDepth_eq_clog]
  exact Nat.le_pow_clog (by decide) m

theorem paddedCount_le (m : ℕ) : paddedCount m ≤ 2 * (m + 1) := by
  rw [paddedCount, paddingDepth, ← FrozenPascal.UniformWeight.wordWidth_eq_size]
  exact (FrozenPascal.UniformWeight.paddedCount_le (m - 1)).trans (by omega)

theorem paddingDepth_logspace : ComputableInLogSpace paddingDepth encUnary encUnary :=
  (FrozenPascal.UniformWeight.wordWidth_logspace.comp
    (ComputableInLogSpace.id.unarySub (ComputableInLogSpace.const 1))).congr_fun
    (fun m => (FrozenPascal.UniformWeight.wordWidth_eq_size (m - 1)).symm)

theorem paddedCount_logspace : ComputableInLogSpace paddedCount encUnary encUnary :=
  (FrozenPascal.UniformWeight.paddedCount_logspace.comp
    (ComputableInLogSpace.id.unarySub (ComputableInLogSpace.const 1))).congr_fun
    (fun m => by simp [paddedCount, paddingDepth, FrozenPascal.UniformWeight.paddedCount,
      FrozenPascal.UniformWeight.wordWidth_eq_size])

def unpack (x : Bits (m * w)) (j : Fin m) : Bits w :=
  fun i => x (finProdFinEquiv (j, i))

private def selectOutput (c : Gates n w) (i : Fin w) : Gates n 1 :=
  (Circuit.wiring signature (fun _ : Fin 1 => i)).comp c

/-- Assemble ordered multi-output blocks on the same input. The existing
one-output bank compiler copies each template at most once per output lane. -/
def bank (cs : Fin m → Gates n w) : Gates n (m * w) :=
  Circuit.pi fun q => selectOutput (cs (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2

@[simp] theorem bank_eval (cs : Fin m → Gates n w) (x : Bits n) (j : Fin m) :
    unpack ((bank cs).eval interpretation x) j = (cs j).eval interpretation x := by
  funext i
  simp only [unpack, bank, Circuit.eval_pi, Equiv.symm_apply_apply, selectOutput,
    Circuit.eval_comp, Circuit.eval_wiring, Function.comp_apply]

theorem bank_depth (cs : Fin m → Gates n w) (h : ∀ j, (cs j).depth ≤ d) :
    (bank cs).depth ≤ d := by
  apply Circuit.depth_pi_le
  intro q
  exact (Circuit.depth_comp_le _ _).trans (by simpa [selectOutput] using h (finProdFinEquiv.symm q).1)

theorem bank_size (cs : Fin m → Gates n w) (h : ∀ j, (cs j).size ≤ s) :
    (bank cs).size ≤ m * w * s := by
  rw [bank, Circuit.size_pi]
  calc
    _ ≤ ∑ _ : Fin (m * w), s := Finset.sum_le_sum fun q _ => by
      simpa [selectOutput] using h (finProdFinEquiv.symm q).1
    _ = _ := by simp

section BankGenerator
variable {α : Type} {enc : α ↪ List Bool} {n m : α → ℕ} {w : ℕ}

theorem bank_code_logspace {cs : ∀ a, Fin (m a) → Gates (n a) w}
    (hn : ComputableInLogSpace n enc encUnary) (hm : ComputableInLogSpace m enc encUnary)
    (hc : ComputableInLogSpace (fun p : α × ℕ =>
      if h : p.2 < m p.1 then (cs p.1 ⟨p.2, h⟩).code else ([], []))
      (encPair enc encUnary) encCode) :
    ComputableInLogSpace (fun a => (bank (cs a)).code) enc encCode := by
  let raw (p : α × ℕ) : RawCode :=
    if h : p.2 / w < m p.1 then (cs p.1 ⟨p.2 / w, h⟩).code else ([], [])
  have hp := ComputableInLogSpace.fst enc encUnary
  have hq := ComputableInLogSpace.snd enc encUnary
  have hr : ComputableInLogSpace raw (encPair enc encUnary) encCode :=
    hc.comp (hp.pair (hq.unaryDiv (ComputableInLogSpace.const w)))
  have hw := ComputableInLogSpace.listLength.comp hr.snd'
  have hi := (hq.unaryMod (ComputableInLogSpace.const w)).unaryMin hw
  have hout : ComputableInLogSpace (fun p : α × ℕ => (([], [min (p.2 % w) (raw p).2.length]) :
      RawCode)) (encPair enc encUnary) encCode :=
    (ComputableInLogSpace.const []).pair (ComputableInLogSpace.listSingleton.comp hi.unaryToBinary)
  have hs := compCode_logspace (hn.comp hp) hout hr (fun p => by
    simp [BoundedReferences])
  have hW := hm.unaryMulConst w
  apply circuit_pi_of_indexed_logspace hn hW
  refine ((hq.unaryLt (hW.comp hp)).ite hs (ComputableInLogSpace.const ([], []))).congr_fun ?_
  intro p
  simp only [decide_eq_true_eq, Function.comp_apply]
  split_ifs with hqW
  · let q : Fin (m p.1 * w) := ⟨p.2, hqW⟩
    let r := (finProdFinEquiv.symm q).1
    let i := (finProdFinEquiv.symm q).2
    have hrval : r.val = p.2 / w := rfl
    have hival : i.val = p.2 % w := rfl
    have hrlt : p.2 / w < m p.1 := hrval ▸ r.isLt
    have hilt : p.2 % w < w := hival ▸ i.isLt
    have houtlen : (cs p.1 r).code.2.length = w := by simp [Circuit.code]
    change (selectOutput (cs p.1 r) i).code =
      compCode (n p.1) ([], [min (p.2 % w) (raw p).2.length]) (raw p)
    have he : raw p = (cs p.1 r).code := by
      change (if h : p.2 / w < m p.1 then (cs p.1 ⟨p.2 / w, h⟩).code else ([], [])) = _
      rw [dite_eq_left hrlt]
      rfl
    rw [he, houtlen, Nat.min_eq_left hilt.le, selectOutput, ← compCode_code,
      Circuit.code_wiring, ← hival]
    rfl
  · rfl

end BankGenerator

def combine (merge : Gates (2 * w) w) (a b : Bits w) : Bits w :=
  merge.eval interpretation (Fin.append a b ∘ Fin.cast (Nat.two_mul w))

private def pairWires (j : Fin m) (i : Fin (2 * w)) : Fin ((m * 2) * w) :=
  ⟨i.val + (2 * w) * j.val, by
    have h := Nat.mul_le_mul_left (2 * w) (Nat.succ_le_of_lt j.isLt)
    rw [Nat.mul_succ] at h
    have hi := i.isLt
    calc
      i.val + (2 * w) * j.val < (2 * w) * m := by omega
      _ = (m * 2) * w := by ring⟩

private def layer (merge : Gates (2 * w) w) (m : ℕ) : Gates ((m * 2) * w) (m * w) :=
  bank fun j => merge.comp (Circuit.wiring signature (pairWires j))

private theorem layer_eval (merge : Gates (2 * w) w) (v : Bits ((m * 2) * w)) (j : Fin m) :
    unpack ((layer merge m).eval interpretation v) j =
      combine merge (unpack v ⟨2 * j.val, by omega⟩)
        (unpack v ⟨2 * j.val + 1, by omega⟩) := by
  rw [layer, bank_eval, Circuit.eval_comp, Circuit.eval_wiring, combine]
  congr 1
  funext i
  change v (pairWires j i) = _
  let k := Fin.cast (Nat.two_mul w) i
  change v (pairWires j i) = Fin.append _ _ k
  have hk : (Fin.cast (Nat.two_mul w).symm k).val = i.val := rfl
  generalize hk' : k = l at hk ⊢
  induction l using Fin.addCases with
  | left l =>
    simp only [Fin.append_left, unpack]
    congr 1
    apply Fin.ext
    change i.val + 2 * w * j.val = l.val + w * (2 * j.val)
    change l.val = i.val at hk
    rw [← hk]
    ring
  | right l =>
    simp only [Fin.append_right, unpack]
    congr 1
    apply Fin.ext
    change i.val + 2 * w * j.val = l.val + w * (2 * j.val + 1)
    change w + l.val = i.val at hk
    rw [← hk]
    ring

private theorem layer_depth (merge : Gates (2 * w) w) (m : ℕ) :
    (layer merge m).depth ≤ merge.depth :=
  bank_depth _ (fun _ => (Circuit.depth_comp_le _ _).trans (by simp))

private theorem layer_size (merge : Gates (2 * w) w) (m : ℕ) :
    (layer merge m).size ≤ m * w * merge.size :=
  bank_size _ (fun _ => by simp)

private theorem layer_code_logspace (merge : Gates (2 * w) w) :
    ComputableInLogSpace (fun m => (layer merge m).code) encUnary encCode := by
  have hn : ComputableInLogSpace (fun m : ℕ => (m * 2) * w) encUnary encUnary :=
    (ComputableInLogSpace.id.unaryMulConst 2).unaryMulConst w
  have hp := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  -- Generate the same wiring as a total raw template, then mask invalid queries.
  let wire (j : ℕ) : RawCode := ([], (List.range (2 * w)).map (fun i => i + 2 * w * j))
  have hg := (ComputableInLogSpace.snd (encPair encUnary encUnary) encUnary).unaryAdd
    ((hj.unaryMulConst (2 * w)).comp (ComputableInLogSpace.fst (encPair encUnary encUnary) encUnary))
  have hwire : ComputableInLogSpace (fun p : ℕ × ℕ => wire p.2)
      (encPair encUnary encUnary) encCode := by
    refine ((ComputableInLogSpace.const []).pair
      (map_range (ComputableInLogSpace.const (2 * w)) hg.unaryToBinary)).congr_fun ?_
    intro p
    simp [wire, Nat.mul_comm]
  have hc := compCode_logspace (hn.comp hp) (ComputableInLogSpace.const merge.code) hwire
    (fun p => by
      have h := circuit_boundedReferences merge
      simpa only [wire, List.length_map, List.length_range, Circuit.length_code_fst] using
        (show BoundedReferences (2 * w + merge.code.1.length) merge.code by
          rw [Circuit.length_code_fst]; exact h))
  apply bank_code_logspace hn ComputableInLogSpace.id
  refine ((hj.unaryLt hp).ite hc (ComputableInLogSpace.const ([], []))).congr_fun ?_
  intro p
  simp only [decide_eq_true_eq, Function.comp_apply]
  split_ifs
  · rw [← compCode_code, Circuit.code_wiring_eq_map]
    intro i
    rfl
  · rfl

private def castOutput {m p : ℕ} (h : m = p) (c : Gates n m) : Gates n p :=
  h ▸ c

@[simp] private theorem castOutput_code (h : m = p) (c : Gates n m) :
    (castOutput h c).code = c.code := by subst p; rfl

@[simp] private theorem castOutput_depth (h : m = p) (c : Gates n m) :
    (castOutput h c).depth = c.depth := by subst p; rfl

@[simp] private theorem castOutput_size (h : m = p) (c : Gates n m) :
    (castOutput h c).size = c.size := by subst p; rfl

private theorem castOutput_eval (h : m = p) (c : Gates n m) (x : Bits n) (i : Fin p) :
    (castOutput h c).eval interpretation x i = c.eval interpretation x (Fin.cast h.symm i) := by
  subst p
  rfl

private def reduce (merge : Gates (2 * w) w) :
    (d : ℕ) → Gates n (2 ^ d * w) → Gates n w
  | 0, c => castOutput (Nat.one_mul w) c
  | d+1, c => reduce merge d ((normalizeOutputs (layer merge (2 ^ d))).comp c)

/-- The context is computed in parallel on the original input and is available
to the readout. The initial bank can already include charged preprocessing. -/
def compile (merge : Gates (2 * w) w) (d : ℕ) (initial : Gates n (2 ^ d * w))
    (context : Gates n k) (read : Gates (w + k) 1) : Gates n 1 :=
  read.comp ((reduce merge d (normalizeOutputs initial)).append context)

private theorem reduce_depth (merge : Gates (2 * w) w) (d : ℕ) (c : Gates n (2 ^ d * w)) :
    (reduce merge d c).depth ≤ c.depth + d * (merge.depth + 1) := by
  induction d with
  | zero => simp [reduce]
  | succ d ih =>
    change Gates n ((2 ^ d * 2) * w) at c
    apply (ih _).trans
    have hm := (normalizeOutputs_depth_le (layer merge (2 ^ d))).trans
      (Nat.add_le_add_right (layer_depth merge _) 1)
    have hc := (Circuit.depth_comp_le (normalizeOutputs (layer merge (2 ^ d))) c).trans
      (Nat.add_le_add_right hm c.depth)
    change _ ≤ c.depth + (d + 1) * (merge.depth + 1)
    exact (Nat.add_le_add_right hc _).trans (by
      simp only [Nat.add_mul, Nat.one_mul]
      omega)

theorem compile_depth (merge : Gates (2 * w) w) (d : ℕ) (initial : Gates n (2 ^ d * w))
    (context : Gates n k) (read : Gates (w + k) 1) :
    (compile merge d initial context read).depth ≤
      max (initial.depth + 1 + d * (merge.depth + 1)) context.depth + read.depth := by
  have h := (reduce_depth merge d (normalizeOutputs initial)).trans
    (Nat.add_le_add_right (normalizeOutputs_depth_le initial) _)
  have hmid := (Circuit.depth_append_le _ context).trans (max_le_max_right _ h)
  exact (Circuit.depth_comp_le read _).trans (by
    simpa only [Nat.add_comm read.depth] using Nat.add_le_add_left hmid read.depth)

private theorem reduce_size (merge : Gates (2 * w) w) (d : ℕ) (c : Gates n (2 ^ d * w)) :
    (reduce merge d c).size ≤ c.size + (2 ^ d - 1) * (w * merge.size + w) := by
  induction d with
  | zero => simp [reduce]
  | succ d ih =>
    change Gates n ((2 ^ d * 2) * w) at c
    apply (ih _).trans
    have h := layer_size merge (2 ^ d)
    rw [Circuit.size_comp, normalizeOutputs_size]
    have hpow : 0 < 2 ^ d := Nat.two_pow_pos _
    have he : 2 ^ (d + 1) - 1 = 2 ^ d + (2 ^ d - 1) := by rw [pow_succ]; omega
    have hstep : (layer merge (2 ^ d)).size + 2 ^ d * w ≤ 2 ^ d * (w * merge.size + w) := by
      rw [Nat.mul_add, ← Nat.mul_assoc]
      omega
    rw [he, Nat.add_mul]
    omega

theorem compile_size (merge : Gates (2 * w) w) (d : ℕ) (initial : Gates n (2 ^ d * w))
    (context : Gates n k) (read : Gates (w + k) 1) :
    (compile merge d initial context read).size ≤
      initial.size + 2 ^ d * w + (2 ^ d - 1) * (w * merge.size + w) +
        context.size + read.size := by
  have h := reduce_size merge d (normalizeOutputs initial)
  simp only [normalizeOutputs_size] at h
  simp only [compile, Circuit.size_comp, Circuit.size_append]
  omega

private theorem reduce_eval (merge : Gates (2 * w) w) {empty : Bits w}
    (laws : Laws (combine merge) empty) (d : ℕ) (initial : Gates n (2 ^ d * w)) (x : Bits n) :
    (reduce merge d initial).eval interpretation x =
      summarize (combine merge) empty (List.ofFn (unpack (initial.eval interpretation x))) := by
  induction d with
  | zero =>
    rw [reduce, List.ofFn_succ, List.ofFn_zero]
    change (castOutput _ initial).eval interpretation x = combine merge _ empty
    rw [laws.rightId]
    funext i
    rw [castOutput_eval]
    congr 1
  | succ d ih =>
    change Gates n ((2 ^ d * 2) * w) at initial
    change (reduce merge d ((normalizeOutputs (layer merge (2 ^ d))).comp initial)).eval
      interpretation x = _
    rw [ih, Circuit.eval_comp, normalizeOutputs_eval]
    let v := initial.eval interpretation x
    change summarize (combine merge) empty (List.ofFn (unpack ((layer merge (2 ^ d)).eval
      interpretation v))) = summarize (combine merge) empty (List.ofFn (unpack (m := 2 ^ d * 2) v))
    exact (congrArg (fun f => summarize (combine merge) empty (List.ofFn f))
      (funext (layer_eval merge v))).trans (summarize_pair_bank laws (unpack v))

theorem compile_eval (merge : Gates (2 * w) w) {empty : Bits w}
    (laws : Laws (combine merge) empty) (d : ℕ) (initial : Gates n (2 ^ d * w))
    (context : Gates n k) (read : Gates (w + k) 1) (x : Bits n) :
    (compile merge d initial context read).eval interpretation x =
      read.eval interpretation (Fin.append
        (summarize (combine merge) empty (List.ofFn (unpack (initial.eval interpretation x))))
        (context.eval interpretation x)) := by
  rw [compile, Circuit.eval_comp, Circuit.eval_append, reduce_eval merge laws, normalizeOutputs_eval]

private def stages (merge : Gates (2 * w) w) : ℕ → List RawCode
  | 0 => []
  | d + 1 => (normalizeOutputs (layer merge (2 ^ d))).code :: stages merge d

private theorem reduce_code (merge : Gates (2 * w) w) (d : ℕ) (initial : Gates n (2 ^ d * w)) :
    (reduce merge d initial).code =
      UniformComposition.sequentialCodes n initial.code (stages merge d) := by
  induction d with
  | zero => simp [reduce, stages, UniformComposition.sequentialCodes]
  | succ d ih =>
    change Gates n ((2 ^ d * 2) * w) at initial
    change (reduce merge d ((normalizeOutputs (layer merge (2 ^ d))).comp initial)).code = _
    rw [ih, ← compCode_code]
    rfl

private theorem stages_compatible (merge : Gates (2 * w) w) (d : ℕ) :
    VariableChain.Compatible (2 ^ d * w) (stages merge d) := by
  induction d with
  | zero => trivial
  | succ d ih =>
    let c := normalizeOutputs (layer merge (2 ^ d))
    have hw : c.code.2.length = 2 ^ d * w := by simp [Circuit.code]
    change VariableChain.Compatible (2 ^ d * 2 * w) (c.code :: stages merge d)
    refine ⟨?_, ?_, ?_⟩
    · rw [hw]
      exact normalizeOutputs_consecutive _
    · rw [Circuit.length_code_fst]
      exact circuit_boundedReferences c
    · rw [hw]
      exact ih

private theorem stages_indexed (merge : Gates (2 * w) w) (d : ℕ) :
    stages merge d = (List.range d).map (fun j =>
      (normalizeOutputs (layer merge (2 ^ (d - 1 - j)))).code) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [stages, ih, List.range_succ_eq_map, List.map_cons]
    simp only [Nat.sub_zero, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro j _
    rw [show d + 1 - 1 - j.succ = d - 1 - j by omega]

section Generator
variable {α : Type} {enc : α ↪ List Bool} {n d : α → ℕ}

private theorem stages_code_logspace (merge : Gates (2 * w) w)
    (hd : ComputableInLogSpace d enc encUnary)
    (hP : ComputableInLogSpace (fun a => 2 ^ d a) enc encUnary) :
    ComputableInLogSpace (fun a => stages merge (d a)) enc (encList encCode) := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  have he := ((hd.comp hp).unarySub (ComputableInLogSpace.const 1)).unarySub hj
  have hzero := (ComputableInLogSpace.bitsMap (fun _ => false)).comp
    (he.congr (encOut := encBits) (fun _ => rfl))
  have hbits := hzero.bitsAppend (ComputableInLogSpace.const [true])
  have hb : ComputableInLogSpace (fun p : α × ℕ => 2 ^ (d p.1 - 1 - p.2))
      (encPair enc encUnary) encNat := hbits.congr (fun p => by
        change encNat (2 ^ (d p.1 - 1 - p.2)) =
          encBits (List.map (fun _ : Bool => false) (List.replicate (d p.1 - 1 - p.2) true) ++ [true])
        simp only [encNat_two_pow, encBits_apply, List.map_replicate])
  have hm := boundedBinaryToUnary hb (hP.comp hp) (fun p =>
    Nat.pow_le_pow_right (by decide) ((Nat.sub_le _ _).trans (Nat.sub_le _ _)))
  have hn := (hm.unaryMulConst 2).unaryMulConst w
  have hstage := normalizeOutputs_logspace hn (hm.unaryMulConst w)
    ((layer_code_logspace merge).comp hm)
  exact (map_range hd hstage).congr_fun (fun a => stages_indexed merge (d a))

/-- Logspace for the complete circuit code follows from the local banks and
the widths. The merge and read circuits are fixed, with no generator premise
on the composed network. -/
theorem compile_code_logspace (merge : Gates (2 * w) w) (read : Gates (w + k) 1)
    {initial : ∀ a, Gates (n a) (2 ^ d a * w)} {context : ∀ a, Gates (n a) k}
    (hn : ComputableInLogSpace n enc encUnary)
    (hd : ComputableInLogSpace d enc encUnary)
    (hP : ComputableInLogSpace (fun a => 2 ^ d a) enc encUnary)
    (hi : ComputableInLogSpace (fun a => (initial a).code) enc encCode)
    (hc : ComputableInLogSpace (fun a => (context a).code) enc encCode) :
    ComputableInLogSpace (fun a => (compile merge (d a) (initial a) (context a) read).code)
      enc encCode := by
  have hninit := normalizeOutputs_logspace hn (hP.unaryMulConst w) hi
  have hlen (a : α) : (normalizeOutputs (initial a)).code.2.length = 2 ^ d a * w := by
    simp [Circuit.code]
  have hs := VariableChain.sequentialCodes_logspace hn hninit (stages_code_logspace merge hd hP)
    (fun a => by simpa only [hlen a, UniformComposition.Consecutive] using normalizeOutputs_consecutive (initial a))
    (fun a => by simpa only [hlen a] using stages_compatible merge (d a))
  have hr := hs.congr_fun fun a => reduce_code merge (d a) (normalizeOutputs (initial a))
  exact circuit_comp_logspace hn (circuit_append_logspace hn hr hc)
    (ComputableInLogSpace.const read.code)

end Generator
end PredictionDepth.BlockSummary
