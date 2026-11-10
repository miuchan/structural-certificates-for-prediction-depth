import PredictionDepth.Complexity.UniformComposition.Chain

/-! Logspace streaming for a chain whose normalized stage widths may vary. -/

namespace PredictionDepth.StandardComplexity.VariableChain

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM CodeLogspace CodeLogspaceFamilies UniformComposition RegularCompositionCode

/-- Each template consumes the previous output width and ends in its own
consecutive output bank. -/
def Compatible : ℕ → List RawCode → Prop
  | _, [] => True
  | n, c :: cs =>
    Consecutive n c.2.length c ∧ BoundedReferences (n + c.1.length) c ∧ Compatible c.2.length cs

private def priorWidth (initial : RawCode) (codes : List RawCode) (j : ℕ) : ℕ :=
  ((initial :: codes).getD j ([], [])).2.length

private theorem priorWidth_append (initial : RawCode) (codes more : List RawCode)
    (j : ℕ) (hj : j ≤ codes.length) :
    priorWidth initial (codes ++ more) j = priorWidth initial codes j := by
  have h : j < (initial :: codes).length := by simpa using Nat.lt_succ_iff.mpr hj
  unfold priorWidth
  change (((initial :: codes) ++ more).getD j ([], [])).2.length = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, h, ite_true]

private theorem priorWidth_snoc_last (initial : RawCode) (codes : List RawCode) (c : RawCode) :
    priorWidth initial (codes ++ [c]) (codes ++ [c]).length = c.2.length := by
  unfold priorWidth
  change (((initial :: codes) ++ [c]).getD _ ([], [])).2.length = _
  simp [List.getD_eq_getElem?_getD]

private theorem compatible_snoc (initial c : RawCode) (codes : List RawCode) :
    Compatible initial.2.length (codes ++ [c]) ↔ Compatible initial.2.length codes ∧
      Consecutive (priorWidth initial codes codes.length) c.2.length c ∧
      BoundedReferences (priorWidth initial codes codes.length + c.1.length) c := by
  induction codes generalizing initial with
  | nil => simp [Compatible, priorWidth]
  | cons b codes ih =>
    simp only [List.cons_append, List.length_cons, priorWidth, List.getD_cons_succ, Compatible]
    rw [ih b]
    simp only [priorWidth, and_assoc]

private theorem compatible_reference (initial : RawCode) (codes : List RawCode) (j : ℕ)
    (h : Compatible initial.2.length codes) :
    BoundedReferences (priorWidth initial codes j + ((codes.getD j ([], [])).1).length)
      (codes.getD j ([], [])) := by
  induction codes generalizing initial j with
  | nil => simp [BoundedReferences]
  | cons c codes ih =>
    cases j with
    | zero => exact h.2.1
    | succ j => exact ih c j h.2.2

private theorem consecutive_comp {n W V : ℕ} {prior later : RawCode}
    (hp : Consecutive n W prior) (hl : Consecutive W V later) :
    Consecutive n V (compCode n later prior) := by
  rw [compCode_consecutive n W prior later hp]
  constructor
  · simpa only [List.length_append, List.length_map] using hl.1.trans (Nat.le_add_left _ _)
  · simp only [hl.2, List.map_map, Function.comp_def, List.length_append, List.length_map]
    apply List.map_congr_left
    intro j _
    have := hp.1
    have := hl.1
    omega

private theorem sequential_consecutive (n : ℕ) (initial : RawCode) (codes : List RawCode)
    (hi : Consecutive n initial.2.length initial) (hc : Compatible initial.2.length codes) :
    Consecutive n (priorWidth initial codes codes.length) (sequentialCodes n initial codes) := by
  induction codes using List.reverseRecOn with
  | nil => exact hi
  | append_singleton codes c ih =>
    rw [sequentialCodes_snoc, priorWidth_snoc_last]
    obtain ⟨hprefix, hlast, _⟩ := (compatible_snoc initial c codes).mp hc
    exact consecutive_comp (ih hprefix) hlast

private def directCodes (n : ℕ) (initial : RawCode) (codes : List RawCode) : RawCode :=
  (initial.1 ++ (List.range codes.length).flatMap (fun j =>
      (codes.getD j ([], [])).1.map
        (shiftGate (prefixBase n (priorWidth initial codes j) initial codes j))),
    (List.range (priorWidth initial codes codes.length)).map (fun j =>
      prefixBase n (priorWidth initial codes codes.length) initial codes codes.length + j))

private theorem directCodes_gates_snoc (n : ℕ) (initial : RawCode)
    (codes : List RawCode) (c : RawCode) :
    (directCodes n initial (codes ++ [c])).1 = (directCodes n initial codes).1 ++
      c.1.map (shiftGate (prefixBase n (priorWidth initial codes codes.length)
        initial codes codes.length)) := by
  have hget (j : ℕ) (hj : j < codes.length) :
      (codes ++ [c]).getD j ([], []) = codes.getD j ([], []) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hj]
  have hlast : (codes ++ [c]).getD codes.length ([], []) = c := by
    simp [List.getD_eq_getElem?_getD]
  simp only [directCodes, List.length_append, List.length_singleton, List.range_succ,
    List.flatMap_append, List.flatMap_singleton, hlast, prefixBase, List.take_left,
    List.take_length, priorWidth_append initial codes [c] codes.length le_rfl, List.append_assoc]
  congr 1
  congr 1
  apply List.flatMap_congr
  intro j hj
  have h := List.mem_range.mp hj
  rw [hget j h, List.take_append_of_le_length h.le, priorWidth_append initial codes [c] j h.le]

private theorem directCodes_eq (n : ℕ) (initial : RawCode) (codes : List RawCode)
    (hi : Consecutive n initial.2.length initial) (hc : Compatible initial.2.length codes) :
    directCodes n initial codes = sequentialCodes n initial codes := by
  induction codes using List.reverseRecOn with
  | nil =>
    apply Prod.ext
    · simp [directCodes, sequentialCodes]
    · simpa [directCodes, sequentialCodes, prefixBase, priorWidth] using hi.2.symm
  | append_singleton codes c ih =>
    obtain ⟨hprefix, hlast, _⟩ := (compatible_snoc initial c codes).mp hc
    have hprev := sequential_consecutive n initial codes hi hprefix
    have hind := ih hprefix
    rw [sequentialCodes_snoc, compCode_consecutive n _ _ c hprev]
    apply Prod.ext
    · rw [directCodes_gates_snoc, hind, sequentialCodes_length]
      simp only [prefixBase, List.take_length, Nat.add_assoc]
    · simp only [directCodes, prefixBase, sequentialCodes_length]
      rw [priorWidth_snoc_last, List.take_length]
      conv_rhs => rw [hlast.2]
      simp only [List.flatMap_append, List.flatMap_singleton, List.length_append,
        List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro j _
      have := hprev.1
      rw [sequentialCodes_length] at this
      have := hlast.1
      omega

/-- The generator streams a variable-width normalized chain by recomputing
the earlier gate count and reading the preceding template's output width. -/
theorem sequentialCodes_logspace {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {initial : α → RawCode} {codes : α → List RawCode}
    (hn : ComputableInLogSpace n enc encUnary)
    (hi : ComputableInLogSpace initial enc encCode)
    (hc : ComputableInLogSpace codes enc (encList encCode))
    (hinit : ∀ a, Consecutive (n a) (initial a).2.length (initial a))
    (hsteps : ∀ a, Compatible (initial a).2.length (codes a)) :
    ComputableInLogSpace (fun a => sequentialCodes (n a) (initial a) (codes a))
      enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  have hblock := getD ([], []) (hc.comp hp) hj
  have hcodes := hi.listCons hc
  have hprior : ComputableInLogSpace
      (fun p : α × ℕ => priorWidth (initial p.1) (codes p.1) p.2)
      (encPair enc encUnary) encUnary :=
    ComputableInLogSpace.listLength.comp (getD ([], []) (hcodes.comp hp) hj).snd'
  have hpre := CodeLogspaceFamilies.take ([], []) (hc.comp hp) hj
  have hpreGates := flatMapWithInput ([], []) hpre
    (ComputableInLogSpace.snd (encPair enc encUnary) encCode).fst'
  have hpreLen := ComputableInLogSpace.listLength.comp hpreGates
  have hinitLen := ComputableInLogSpace.listLength.comp hi.fst'
  have hbase := (((hn.unaryAdd hinitLen).comp hp).unaryAdd hpreLen).unarySub hprior
  have hB := hprior.unaryAdd (ComputableInLogSpace.listLength.comp hblock.fst')
  have hb (p : α × ℕ) := compatible_reference (initial p.1) (codes p.1) p.2 (hsteps p.1)
  have hpar := ComputableInLogSpace.fst (encPair enc encUnary) encUnary
  have hix := ComputableInLogSpace.snd (encPair enc encUnary) encUnary
  have hw := ((hbase.comp hpar).unaryAdd hix).unaryToBinary
  have hshift := mapCode_logspace hblock hB hb hw
  have hcount := ComputableInLogSpace.listLength.comp hc
  have hgates := flatMap_range_list hcount hshift.fst'
  have hid : ComputableInLogSpace (id : α → α) enc enc := ComputableInLogSpace.id
  have hlast := hid.pair hcount
  have hlastWidth := hprior.comp hlast
  have hlastBase := hbase.comp hlast
  have houts := map_range hlastWidth (((hlastBase.comp hp).unaryAdd hj).unaryToBinary)
  exact ((hi.fst'.listAppend hgates).pair houts).congr_fun fun a =>
    (directCodes_eq (n a) (initial a) (codes a) (hinit a) (hsteps a)).symm

end PredictionDepth.StandardComplexity.VariableChain
