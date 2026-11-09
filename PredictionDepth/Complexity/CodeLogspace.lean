import PredictionDepth.Complexity.LogspaceBatch
import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
import CslibFrontier.Computability.Circuit.Boolean.CodeSubstitution
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Equality
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words

/-!
# Logspace transformations of circuit descriptions

The transformations stream lists by the verified polynomial-batch compiler.
Intermediate circuits are queried by recomputation, rather than copied onto
work tapes. Binary wire references of valid circuits are bounded by their
unary input count and gate count; bounded binary-to-unary conversion permits
the existing finite-machine counter arithmetic to perform relocation.
-/

namespace PredictionDepth.StandardComplexity.CodeLogspace
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}

/-- Stream a polynomially bounded number of computed, framed elements. -/
theorem map_range {r : α → ℕ} {f : α × ℕ → β}
    (hr : ComputableInLogSpace r enc encUnary)
    (hf : ComputableInLogSpace f (encPair enc encUnary) encB) :
    ComputableInLogSpace (fun a => (List.range (r a)).map (fun j => f (a, j)))
      enc (encList encB) := by
  have hword : ComputableInLogSpace (fun p => frame (encB (f p)))
      (encPair enc encUnary) encBits :=
    (ComputableInLogSpace.listSingleton.comp hf).congr (fun _ => by simp)
  have h := LogspaceBatch.flatMap_range hr hword
  exact h.congr fun a => by
    change ((List.range (r a)).map (fun j => f (a, j))).flatMap (frame ∘ encB) = _
    rw [List.flatMap_map]
    rfl

/-- Indexed lookup with a default, at a computed unary index. -/
theorem getD (fallback : β) {l : α → List β} {j : α → ℕ}
    (hl : ComputableInLogSpace l enc (encList encB))
    (hj : ComputableInLogSpace j enc encUnary) :
    ComputableInLogSpace (fun a => (l a).getD (j a) fallback) enc encB := by
  have h := (ComputableInLogSpace.optionGetD fallback).comp (hl.getElem?' hj)
  exact h.congr_fun fun a => List.getD_eq_getElem?_getD

private theorem range_pick_word (word : ℕ → List Bool) {bound value : ℕ} (h : value ≤ bound) :
    (List.range (bound + 1)).flatMap (fun j => if j = value then word j else []) = word value := by
  induction bound with
  | zero =>
    have : value = 0 := by omega
    subst value
    simp
  | succ bound ih =>
    by_cases hle : value ≤ bound
    · rw [List.range_succ, List.flatMap_append, ih hle]
      simp [show bound + 1 ≠ value by omega]
    · have heq : value = bound + 1 := by omega
      subst value
      rw [List.range_succ, List.flatMap_append]
      have hz : (List.range (bound + 1)).flatMap
          (fun j => if j = bound + 1 then word j else []) = [] := by
        calc
          _ = (List.range (bound + 1)).flatMap (fun _ => []) :=
            List.flatMap_congr (fun j hj => by
              simp [show j ≠ bound + 1 by have := List.mem_range.mp hj; omega])
          _ = [] := by simp
      simp [hz]

/-- A binary number bounded by a logspace unary clock can be emitted in unary.
Only the loop index is stored; equality compares the two encoded values. -/
theorem boundedBinaryToUnary {v B : α → ℕ}
    (hv : ComputableInLogSpace v enc encNat)
    (hB : ComputableInLogSpace B enc encUnary) (hbound : ∀ a, v a ≤ B a) :
    ComputableInLogSpace v enc encUnary := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  have he := hj.unaryToBinary.equal (hv.comp hp)
  have hjword : ComputableInLogSpace (fun p : α × ℕ => List.replicate p.2 true)
      (encPair enc encUnary) encBits := hj.congr fun _ => rfl
  have hworker := he.ite hjword (ComputableInLogSpace.const ([] : List Bool))
  have h := LogspaceBatch.flatMap_range (hB.unaryAdd (ComputableInLogSpace.const 1)) hworker
  exact h.congr fun a => by
    change List.replicate (v a) true = _
    simpa only [decide_eq_true_eq, Function.comp_apply, encBits_apply] using
      (range_pick_word (fun j => List.replicate j true) (hbound a)).symm

/-- Word length in unary, by a finite-state transducer. -/
theorem bitsLength : ComputableInLogSpace (List.length : List Bool → ℕ) encBits encUnary :=
  (ComputableInLogSpace.bitsMap (fun _ => true)).congr fun w => by
    simp [encUnary_apply]

theorem getD_nat_le {l : List ℕ} {B : ℕ} (h : ∀ i ∈ l, i ≤ B) (j : ℕ) : l.getD j 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  cases he : l[j]? with
  | none => simp
  | some v => exact h v (List.mem_of_getElem? he)

theorem getD_property {δ : Type} {l : List δ} {d : δ} {P : δ → Prop}
    (hl : ∀ v ∈ l, P v) (hd : P d) (j : ℕ) : P (l.getD j d) := by
  rw [List.getD_eq_getElem?_getD]
  cases he : l[j]? with
  | none => exact hd
  | some v => exact hl v (List.mem_of_getElem? he)

theorem range_map_getD {δ ε : Type} (l : List δ) (fallback : δ) (f : δ → ε) :
    (List.range l.length).map (fun j => f (l.getD j fallback)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < l.length := by simpa using hi
    simp [hi']

/-- Map a unary-indexed worker over binary naturals known to fit a logspace
unary bound. The complete source list is queried rather than stored. -/
theorem map_boundedNatList {l : α → List ℕ} {B : α → ℕ} {f : α × ℕ → β}
    (hl : ComputableInLogSpace l enc (encList encNat))
    (hB : ComputableInLogSpace B enc encUnary)
    (hbound : ∀ a v, v ∈ l a → v ≤ B a)
    (hf : ComputableInLogSpace f (encPair enc encUnary) encB) :
    ComputableInLogSpace (fun a => (l a).map (fun v => f (a, v))) enc (encList encB) := by
  have hfirst := ComputableInLogSpace.fst enc encUnary
  have hindex := ComputableInLogSpace.snd enc encUnary
  have hval := getD 0 (hl.comp hfirst) hindex
  have hvalUnary := boundedBinaryToUnary hval (hB.comp hfirst)
    (fun p => getD_nat_le (hbound p.1) p.2)
  have hworker := hf.comp (hfirst.pair hvalUnary)
  have h := map_range (ComputableInLogSpace.listLength.comp hl) hworker
  exact h.congr_fun fun a => (range_map_getD (l a) 0 (fun v => f (a, v))).symm

abbrev RawCode := List (Op × List ℕ) × List ℕ

/-- A global reference bound, weaker than topological well-formedness. Codes
of typed circuits satisfy it with their input count plus gate count. -/
def BoundedReferences (bound : ℕ) (c : RawCode) : Prop :=
  (∀ g ∈ c.1, ∀ i ∈ g.2, i ≤ bound) ∧ (∀ i ∈ c.2, i ≤ bound)

def mapCode (f : ℕ → ℕ) (c : RawCode) : RawCode :=
  (c.1.map (fun g => (g.1, g.2.map f)), c.2.map f)

theorem mapCode_logspace {c : α → RawCode} {B : α → ℕ} {f : α × ℕ → ℕ}
    (hc : ComputableInLogSpace c enc encCode)
    (hB : ComputableInLogSpace B enc encUnary)
    (hbound : ∀ a, BoundedReferences (B a) (c a))
    (hf : ComputableInLogSpace f (encPair enc encUnary) encNat) :
    ComputableInLogSpace (fun a => mapCode (fun i => f (a, i)) (c a)) enc encCode := by
  have hfirst := ComputableInLogSpace.fst enc encUnary
  have hindex := ComputableInLogSpace.snd enc encUnary
  have hg := getD (Op.const false, []) (hc.fst'.comp hfirst) hindex
  have hgateBound (p : α × ℕ) :
      ∀ i ∈ ((c p.1).1.getD p.2 (Op.const false, [])).2, i ≤ B p.1 :=
    getD_property (fun g hg => (hbound p.1).1 g hg) (by simp) p.2
  have houter := ComputableInLogSpace.fst (encPair enc encUnary) encUnary
  have hinner := ComputableInLogSpace.snd (encPair enc encUnary) encUnary
  have hargs := map_boundedNatList hg.snd' (hB.comp hfirst) hgateBound
    (hf.comp (houter.fst'.pair hinner))
  have hgates := map_range (ComputableInLogSpace.listLength.comp hc.fst')
    (hg.fst'.pair hargs)
  have hgates' : ComputableInLogSpace
      (fun a => (c a).1.map (fun g => (g.1, g.2.map (fun i => f (a, i)))))
      enc (encList encGate) := hgates.congr_fun fun a =>
    (range_map_getD (c a).1 (Op.const false, [])
      (fun g => (g.1, g.2.map (fun i => f (a, i))))).symm
  exact hgates'.pair (map_boundedNatList hc.snd' hB (fun a => (hbound a).2) hf)

/-- Actual logspace rewiring of one later-circuit reference. Its unary index
is supplied by bounded-reference enumeration. -/
theorem compCodeWire_logspace {n : α → ℕ} {c : α → RawCode} {i : α → ℕ}
    (hn : ComputableInLogSpace n enc encUnary)
    (hc : ComputableInLogSpace c enc encCode)
    (hi : ComputableInLogSpace i enc encUnary) :
    ComputableInLogSpace (fun a => compCodeWire (n a) (c a) (i a)) enc encNat := by
  have hout := ComputableInLogSpace.listLength.comp hc.snd'
  have hgate := ComputableInLogSpace.listLength.comp hc.fst'
  have hlookup := getD 0 hc.snd' hi
  have hshift := ((hn.unaryAdd hgate).unaryAdd (hi.unarySub hout)).unaryToBinary
  exact ((hi.unaryLt hout).ite hlookup hshift).congr_fun fun a => by
    simp only [compCodeWire, decide_eq_true_eq, Function.comp_apply]

/-- Sequential code composition in real logarithmic workspace. Only the later
code's numerical references need the explicit bound; the earlier code can be
streamed with any number of output wires. -/
theorem compCode_logspace {n : α → ℕ} {d c : α → RawCode}
    (hn : ComputableInLogSpace n enc encUnary)
    (hd : ComputableInLogSpace d enc encCode)
    (hc : ComputableInLogSpace c enc encCode)
    (hbound : ∀ a, BoundedReferences ((c a).2.length + (d a).1.length) (d a)) :
    ComputableInLogSpace (fun a => compCode (n a) (d a) (c a)) enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hwire := compCodeWire_logspace (hn.comp hp) (hc.comp hp) hi
  have hB := (ComputableInLogSpace.listLength.comp hc.snd').unaryAdd
    (ComputableInLogSpace.listLength.comp hd.fst')
  have hmap := mapCode_logspace hd hB hbound hwire
  exact (hc.fst'.listAppend hmap.fst').pair hmap.snd'

theorem shiftCodeWire_logspace {n offset i : α → ℕ}
    (hn : ComputableInLogSpace n enc encUnary)
    (hoffset : ComputableInLogSpace offset enc encUnary)
    (hi : ComputableInLogSpace i enc encUnary) :
    ComputableInLogSpace (fun a => shiftCodeWire (n a) (offset a) (i a)) enc encNat :=
  ((hi.unaryLt hn).ite hi.unaryToBinary (hi.unaryAdd hoffset).unaryToBinary).congr_fun
    (fun a => by simp only [shiftCodeWire, decide_eq_true_eq])

theorem appendCode_logspace {n : α → ℕ} {c d : α → RawCode}
    (hn : ComputableInLogSpace n enc encUnary)
    (hc : ComputableInLogSpace c enc encCode)
    (hd : ComputableInLogSpace d enc encCode)
    (hbound : ∀ a, BoundedReferences (n a + (d a).1.length) (d a)) :
    ComputableInLogSpace (fun a => appendCode (n a) (c a) (d a)) enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hsize := ComputableInLogSpace.listLength.comp hc.fst'
  have hwire := shiftCodeWire_logspace (hn.comp hp) (hsize.comp hp) hi
  have hB := hn.unaryAdd (ComputableInLogSpace.listLength.comp hd.fst')
  have hmap := mapCode_logspace hd hB hbound hwire
  exact (hc.fst'.listAppend hmap.fst').pair (hc.snd'.listAppend hmap.snd')

theorem prefixWire_logspace {r : α → List Bool} {n i : α → ℕ}
    (hr : ComputableInLogSpace r enc encBits)
    (hn : ComputableInLogSpace n enc encUnary)
    (hi : ComputableInLogSpace i enc encUnary) :
    ComputableInLogSpace (fun a => prefixWire (r a) (n a) (i a)) enc encNat := by
  have hlen := bitsLength.comp hr
  have hbit := (ComputableInLogSpace.bitsHeadD false).comp (hr.bitsDrop' hi)
  have hbit' : ComputableInLogSpace (fun a => (r a).getD (i a) false) enc encBool :=
    hbit.congr_fun fun a => by simp [List.getD_eq_getElem?_getD]
  have hconst := hn.unaryAdd
    (hbit'.ite (ComputableInLogSpace.const 1) (ComputableInLogSpace.const 0))
  have hlive := hi.unarySub hlen
  have htotal := hlen.unaryAdd hn
  have hgate := (hn.unaryAdd (ComputableInLogSpace.const 2)).unaryAdd (hi.unarySub htotal)
  exact ((hi.unaryLt hlen).ite hconst.unaryToBinary
    ((hi.unaryLt htotal).ite hlive.unaryToBinary hgate.unaryToBinary)).congr_fun fun a => by
      simp only [prefixWire, decide_eq_true_eq, Function.comp_apply]

theorem prefixCode_logspace {r : α → List Bool} {n : α → ℕ} {c : α → RawCode}
    (hr : ComputableInLogSpace r enc encBits)
    (hn : ComputableInLogSpace n enc encUnary)
    (hc : ComputableInLogSpace c enc encCode)
    (hbound : ∀ a, BoundedReferences ((r a).length + n a + (c a).1.length) (c a)) :
    ComputableInLogSpace (fun a => prefixCode (r a) (n a) (c a)) enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hwire := prefixWire_logspace (hr.comp hp) (hn.comp hp) hi
  have hB := ((bitsLength.comp hr).unaryAdd hn).unaryAdd
    (ComputableInLogSpace.listLength.comp hc.fst')
  have hmap := mapCode_logspace hc hB hbound hwire
  exact ((ComputableInLogSpace.const [(Op.const false, []), (Op.const true, [])]).listAppend
    hmap.fst').pair hmap.snd'

/-- Every typed circuit automatically discharges the bounded-reference premise.
This theorem has no complexity assumption. -/
theorem circuit_boundedReferences {n m : ℕ} (c : Circuit signature n m) :
    BoundedReferences (n + c.size) c.code := by
  have hvalid := (Circuit.isSome_ofCode_iff (n := n) (m := m) (code := c.code)).mp
    (by rw [Circuit.ofCode_code]; rfl)
  constructor
  · intro g hg i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have h := (hvalid.1.getElem j hj).2 i hi
    have hj' : j < c.size := hj.trans_le (Circuit.length_code_fst c).le
    omega
  · intro i hi
    have h := hvalid.2.2 i hi
    rw [Circuit.length_code_fst] at h
    omega

/-- Sequential composition for families of typed circuits, without reference
bound obligations beyond their native well-formed types. -/
theorem circuit_comp_logspace {n m p : α → ℕ}
    {c : ∀ a, Circuit signature (n a) (m a)}
    {d : ∀ a, Circuit signature (m a) (p a)}
    (hn : ComputableInLogSpace n enc encUnary)
    (hc : ComputableInLogSpace (fun a => (c a).code) enc encCode)
    (hd : ComputableInLogSpace (fun a => (d a).code) enc encCode) :
    ComputableInLogSpace (fun a => ((d a).comp (c a)).code) enc encCode := by
  have h := compCode_logspace hn hd hc (fun a => by
    rw [Circuit.length_code_fst (d a)]
    have hout : (c a).code.2.length = m a := by simp [Circuit.code]
    rw [hout]
    exact circuit_boundedReferences (d a))
  exact h.congr_fun fun a => (compCode_code (d a) (c a)).symm

theorem circuit_append_logspace {n m p : α → ℕ}
    {c : ∀ a, Circuit signature (n a) (m a)}
    {d : ∀ a, Circuit signature (n a) (p a)}
    (hn : ComputableInLogSpace n enc encUnary)
    (hc : ComputableInLogSpace (fun a => (c a).code) enc encCode)
    (hd : ComputableInLogSpace (fun a => (d a).code) enc encCode) :
    ComputableInLogSpace (fun a => ((c a).append (d a)).code) enc encCode := by
  have h := appendCode_logspace hn hc hd (fun a => by
    rw [Circuit.length_code_fst (d a)]
    exact circuit_boundedReferences (d a))
  exact h.congr_fun fun a => (appendCode_code (c a) (d a)).symm

theorem circuit_prefix_logspace {n m : α → ℕ} {r : α → List Bool}
    {c : ∀ a, Circuit signature ((r a).length + n a) (m a)}
    (hr : ComputableInLogSpace r enc encBits)
    (hn : ComputableInLogSpace n enc encUnary)
    (hc : ComputableInLogSpace (fun a => (c a).code) enc encCode) :
    ComputableInLogSpace (fun a => (prefixCircuit (r a) (c a)).code) enc encCode := by
  have h := prefixCode_logspace hr hn hc (fun a => by
    rw [Circuit.length_code_fst (c a)]
    exact circuit_boundedReferences (c a))
  exact h.congr_fun fun a => code_prefixCircuit (r a) (c a)

end PredictionDepth.StandardComplexity.CodeLogspace
