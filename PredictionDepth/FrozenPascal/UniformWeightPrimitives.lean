import PredictionDepth.Complexity.CodeLogspaceFamilies
import PredictionDepth.Complexity.UniformComposition.TypedChain
import PredictionDepth.Complexity.UniformComposition.Generator
import CslibFrontier.Computability.Circuit.Boolean.CarrySave
import Mathlib.Tactic.FinCases

/-! Actual logspace constructors for the carry-save arithmetic primitives. -/

namespace PredictionDepth.FrozenPascal.UniformWeight
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM
open StandardComplexity CodeLogspace CodeLogspaceFamilies

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}

/-- A fixed-size tuple of independently computed values can be printed in order. -/
theorem ofFn_logspace {k : ℕ} {f : α → Fin k → β}
    (hf : ∀ i, ComputableInLogSpace (fun a => f a i) enc encB) :
    ComputableInLogSpace (fun a => List.ofFn (f a)) enc (encList encB) := by
  induction k with
  | zero => exact (ComputableInLogSpace.const []).congr_fun (fun _ => by simp)
  | succ k ih =>
      have hp := ih (f := fun a i => f a i.castSucc) (fun i => hf i.castSucc)
      have ht := ComputableInLogSpace.listSingleton.comp (hf (Fin.last k))
      exact (hp.listAppend ht).congr_fun fun a => List.ofFn_succ_last

/-- Print a free wiring from unary output count and pointwise binary references. -/
theorem wiring_logspace {n m : α → ℕ} {f : ∀ a, Fin (m a) → Fin (n a)}
    {g : α × ℕ → ℕ} (hm : ComputableInLogSpace m enc encUnary)
    (hg : ComputableInLogSpace g (encPair enc encUnary) encNat)
    (hfg : ∀ a i, (f a i).val = g (a, i.val)) :
    ComputableInLogSpace (fun a => (Circuit.wiring signature (f a)).code) enc encCode := by
  have ho := CodeLogspace.map_range hm hg
  have h := (ComputableInLogSpace.const (encMid := encList encGate)
    ([] : List (Op × List ℕ))).pair ho
  exact h.congr_fun fun a => Circuit.code_wiring_eq_map (hfg a)

/-- A fixed formula template can be renamed onto actual computed input wires
in logarithmic space. The reference validity is carried by the finite types. -/
theorem renamedFormula_logspace {k : ℕ} (F : Formula signature k)
    {n : α → ℕ} {wires : ∀ a, Fin k → Fin (n a)}
    (hn : ComputableInLogSpace n enc encUnary)
    (hw : ∀ i, ComputableInLogSpace (fun a => (wires a i).val) enc encNat) :
    ComputableInLogSpace (fun a => (F.rename (wires a)).toCircuit.code) enc encCode := by
  induction F with
  | input i =>
      exact ((ComputableInLogSpace.const (encMid := encList encGate) []).pair
        (ComputableInLogSpace.listSingleton.comp (hw i))).congr_fun fun _ => rfl
  | gate op args ih =>
      have hargs := circuit_pi_logspace hn (ofFn_logspace ih)
      exact CodeLogspace.circuit_comp_logspace hn hargs
        (ComputableInLogSpace.const (Circuit.oneGate (σ := signature) op id).code)

theorem constant_logspace {n : α → ℕ} (hn : ComputableInLogSpace n enc encUnary) (b : Bool) :
    ComputableInLogSpace
      (fun a => (Circuit.oneGate (σ := signature) (n := n a) (.const b) Fin.elim0).code)
      enc encCode :=
  ((ComputableInLogSpace.const ([(Op.const b, [])] : List (Op × List ℕ))).pair
    (ComputableInLogSpace.listSingleton.comp hn.unaryToBinary)).congr_fun (fun _ => rfl)

def sumTemplate : Formula signature 3 :=
  ((Formula.input 0).xor (.input 1)).xor (.input 2)

def tripleWires (w : ℕ) (i : Fin w) : Fin 3 → Fin (w + (w + w)) :=
  ![Fin.castAdd (w + w) i, Fin.natAdd w (Fin.castAdd w i), Fin.natAdd w (Fin.natAdd w i)]

theorem sumTemplate_rename (w : ℕ) (i : Fin w) :
    sumTemplate.rename (tripleWires w i) = csaSumFormula w i := by
  simp [sumTemplate, csaSumFormula, tripleWires, Formula.rename, Formula.xor,
    Formula.and, Formula.or, Formula.not, funext_iff, Fin.forall_fin_succ]

theorem majTemplate_rename (w : ℕ) (i : Fin w) :
    (maj3Formula (0 : Fin 3) 1 2).rename (tripleWires w i) =
      maj3Formula (Fin.castAdd (w + w) i) (Fin.natAdd w (Fin.castAdd w i))
        (Fin.natAdd w (Fin.natAdd w i)) := by
  simp [maj3Formula, tripleWires, Formula.rename, Formula.and, Formula.or,
    funext_iff, Fin.forall_fin_succ]

section Selected
variable {w i : α → ℕ} (hi : ∀ a, i a < w a)

theorem sumFormula_logspace (hw : ComputableInLogSpace w enc encUnary)
    (hindex : ComputableInLogSpace i enc encUnary) :
    ComputableInLogSpace (fun a => (csaSumFormula (w a) ⟨i a, hi a⟩).toCircuit.code)
      enc encCode := by
  have hn : ComputableInLogSpace (fun a => w a + (w a + w a)) enc encUnary :=
    hw.unaryAdd (hw.unaryAdd hw)
  have hr : ∀ j : Fin 3, ComputableInLogSpace
      (fun a => (tripleWires (w a) ⟨i a, hi a⟩ j).val) enc encNat := by
    intro j
    fin_cases j
    · exact hindex.unaryToBinary
    · simpa [tripleWires, Nat.add_comm] using (hw.unaryAdd hindex).unaryToBinary
    · simpa [tripleWires, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (hw.unaryAdd (hw.unaryAdd hindex)).unaryToBinary
  exact (renamedFormula_logspace sumTemplate hn hr).congr_fun fun a => by
    rw [sumTemplate_rename]

theorem majorityFormula_logspace (hw : ComputableInLogSpace w enc encUnary)
    (hindex : ComputableInLogSpace i enc encUnary) :
    ComputableInLogSpace (fun a =>
      ((maj3Formula (0 : Fin 3) 1 2).rename (tripleWires (w a) ⟨i a, hi a⟩)).toCircuit.code)
      enc encCode := by
  have hn : ComputableInLogSpace (fun a => w a + (w a + w a)) enc encUnary :=
    hw.unaryAdd (hw.unaryAdd hw)
  apply renamedFormula_logspace _ hn
  intro j
  fin_cases j
  · exact hindex.unaryToBinary
  · simpa [tripleWires, Nat.add_comm] using (hw.unaryAdd hindex).unaryToBinary
  · simpa [tripleWires, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (hw.unaryAdd (hw.unaryAdd hindex)).unaryToBinary

theorem carryFormula_logspace (hw : ComputableInLogSpace w enc encUnary)
    (hindex : ComputableInLogSpace i enc encUnary) :
    ComputableInLogSpace (fun a => (csaCarryFormula (w a) ⟨i a, hi a⟩).toCircuit.code)
      enc encCode := by
  let f (a : α) := (csaCarryFormula (w a) ⟨i a, hi a⟩).toCircuit.code
  let test (a : α) := decide (0 < i a)
  have ht : ComputableInLogSpace test enc encBool :=
    (ComputableInLogSpace.const 0).unaryLt hindex
  have htrue : ComputableInLogSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype (test · = true)).trans enc) encCode := by
    have hpred : ∀ p : {a : α // test a = true}, i p.val - 1 < w p.val := by
      intro p
      have := hi p.val
      omega
    have h := majorityFormula_logspace hpred (hw.restrict _)
      ((hindex.unarySub (ComputableInLogSpace.const 1)).restrict _)
    exact h.congr_fun fun p => by
      have hp : 0 < i p.val := of_decide_eq_true p.property
      dsimp only [f, Function.comp_apply]
      rw [csaCarryFormula, dite_eq_left hp, majTemplate_rename]
  have hfalse : ComputableInLogSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype (test · = false)).trans enc) encCode := by
    have hn := hw.unaryAdd (hw.unaryAdd hw)
    have h := (constant_logspace hn false).restrict (test · = false)
    exact h.congr_fun fun p => by
      have hp : ¬ 0 < i p.val := of_decide_eq_false p.property
      dsimp only [f, Function.comp_apply]
      rw [csaCarryFormula, dite_eq_right hp]
      rfl
  exact (ht.ite_subtype htrue hfalse).congr_fun (fun _ => by simp [f])

end Selected

/-- Safe total code queries, whose out-of-range results are never emitted by
the circuit bank. This keeps zero width in the same native generator. -/
def sumCodeAt (p : ℕ × ℕ) : RawCode :=
  if h : p.2 < p.1 then (csaSumFormula p.1 ⟨p.2, h⟩).toCircuit.code else ([], [])

theorem sumCodeAt_logspace :
    ComputableInLogSpace sumCodeAt (encPair encUnary encUnary) encCode := by
  let test (p : ℕ × ℕ) := decide (p.2 < p.1)
  have hw := ComputableInLogSpace.fst encUnary encUnary
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have ht : ComputableInLogSpace test (encPair encUnary encUnary) encBool := hi.unaryLt hw
  have htrue : ComputableInLogSpace (sumCodeAt ∘ Subtype.val)
      ((Function.Embedding.subtype (test · = true)).trans (encPair encUnary encUnary)) encCode := by
    have hr := sumFormula_logspace
      (fun p : {p : ℕ × ℕ // test p = true} => of_decide_eq_true p.property)
      (hw.restrict _) (hi.restrict _)
    exact hr.congr_fun fun p => by simp only [Function.comp_apply, sumCodeAt,
      dite_eq_left (of_decide_eq_true p.property)]
  have hfalse : ComputableInLogSpace ((fun _ : ℕ × ℕ => (([], []) : RawCode)) ∘ Subtype.val)
      ((Function.Embedding.subtype (test · = false)).trans (encPair encUnary encUnary)) encCode :=
    ComputableInLogSpace.const ([], [])
  exact (ht.ite_subtype htrue hfalse).congr_fun fun p => by
    by_cases h : p.2 < p.1 <;> simp [test, sumCodeAt, h]

def carryCodeAt (p : ℕ × ℕ) : RawCode :=
  if h : p.2 < p.1 then (csaCarryFormula p.1 ⟨p.2, h⟩).toCircuit.code else ([], [])

theorem carryCodeAt_logspace :
    ComputableInLogSpace carryCodeAt (encPair encUnary encUnary) encCode := by
  let test (p : ℕ × ℕ) := decide (p.2 < p.1)
  have hw := ComputableInLogSpace.fst encUnary encUnary
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have ht : ComputableInLogSpace test (encPair encUnary encUnary) encBool := hi.unaryLt hw
  have htrue : ComputableInLogSpace (carryCodeAt ∘ Subtype.val)
      ((Function.Embedding.subtype (test · = true)).trans (encPair encUnary encUnary)) encCode := by
    have hr := carryFormula_logspace
      (fun p : {p : ℕ × ℕ // test p = true} => of_decide_eq_true p.property)
      (hw.restrict _) (hi.restrict _)
    exact hr.congr_fun fun p => by simp only [Function.comp_apply, carryCodeAt,
      dite_eq_left (of_decide_eq_true p.property)]
  have hfalse : ComputableInLogSpace ((fun _ : ℕ × ℕ => (([], []) : RawCode)) ∘ Subtype.val)
      ((Function.Embedding.subtype (test · = false)).trans (encPair encUnary encUnary)) encCode :=
    ComputableInLogSpace.const ([], [])
  exact (ht.ite_subtype htrue hfalse).congr_fun fun p => by
    by_cases h : p.2 < p.1 <;> simp [test, carryCodeAt, h]

theorem csa3to2_logspace :
    ComputableInLogSpace (fun w => (csa3to2 w).code) encUnary encCode := by
  have hw : ComputableInLogSpace (fun w : ℕ => w) encUnary encUnary := ComputableInLogSpace.id
  have hn := hw.unaryAdd (hw.unaryAdd hw)
  have hs := circuit_pi_of_indexed_logspace (cs := fun w i => (csaSumFormula w i).toCircuit)
    hn hw sumCodeAt_logspace
  have hc := circuit_pi_of_indexed_logspace (cs := fun w i => (csaCarryFormula w i).toCircuit)
    hn hw carryCodeAt_logspace
  exact CodeLogspace.circuit_append_logspace hn hs hc

theorem csa4to2FirstIn_val (w : ℕ) (i : Fin (w + (w + w))) :
    (csa4to2FirstIn w i).val = i.val := by
  induction i using Fin.addCases with
  | left i => simp [csa4to2FirstIn]
  | right i =>
    induction i using Fin.addCases with
    | left i => simp [csa4to2FirstIn, Nat.add_comm]
    | right i => simp [csa4to2FirstIn, -Fin.natAdd_eq_addNat, Nat.add_assoc]

theorem csa4to2_logspace :
    ComputableInLogSpace (fun w => (csa4to2 w).code) encUnary encCode := by
  have hw : ComputableInLogSpace (fun w : ℕ => w) encUnary encUnary := ComputableInLogSpace.id
  have h3 := hw.unaryAdd (hw.unaryAdd hw)
  have h4 := (hw.unaryAdd hw).unaryAdd (hw.unaryAdd hw)
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have hp := ComputableInLogSpace.fst encUnary encUnary
  have hfirst := wiring_logspace (f := fun w => csa4to2FirstIn w) h3 hi.unaryToBinary
    (fun w i => csa4to2FirstIn_val w i)
  have hlast := wiring_logspace
    (f := fun w => (Fin.natAdd (w + w) ∘ Fin.natAdd w : Fin w → Fin ((w + w) + (w + w))))
    hw (((hp.unaryAdd hp).unaryAdd (hp.unaryAdd hi)).unaryToBinary)
    (fun w i => by simp [Nat.add_comm])
  exact CodeLogspace.circuit_comp_logspace h4
    (CodeLogspace.circuit_append_logspace h4 hlast
      (CodeLogspace.circuit_comp_logspace h4 hfirst csa3to2_logspace)) csa3to2_logspace

theorem finishStepIn_val (w : ℕ) (i : Fin (w + (w + w))) :
    (finishStepIn w i).val = if i.val < w + w then i.val else w + w := by
  induction i using Fin.addCases with
  | left i =>
    have hi : i.val < w + w := by have := i.isLt; omega
    simp [finishStepIn, hi]
  | right i =>
    induction i using Fin.addCases with
    | left i =>
      have hi : w + i.val < w + w := by have := i.isLt; omega
      simp [finishStepIn, hi, Nat.add_comm]
    | right i =>
      have hi : ¬w + (w + i.val) < w + w := by omega
      simp [finishStepIn, -Fin.natAdd_eq_addNat, hi]

theorem finishStep_logspace :
    ComputableInLogSpace (fun w => (finishStep w).code) encUnary encCode := by
  have hw : ComputableInLogSpace (fun w : ℕ => w) encUnary encUnary := ComputableInLogSpace.id
  have h2 := hw.unaryAdd hw
  have h3 := hw.unaryAdd (hw.unaryAdd hw)
  have hp := ComputableInLogSpace.fst encUnary encUnary
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have hbase := hp.unaryAdd hp
  have href := ((hi.unaryLt hbase).ite hi hbase).unaryToBinary
  have hwire := wiring_logspace (f := finishStepIn) h3 href
    (fun w i => by simpa only [decide_eq_true_eq] using finishStepIn_val w i)
  have hinput := CodeLogspace.circuit_append_logspace h2
    (StandardComplexity.UniformComposition.identityCode_logspace h2)
    (constant_logspace h2 false)
  exact CodeLogspace.circuit_comp_logspace h2
    (CodeLogspace.circuit_comp_logspace h2 hinput hwire) csa3to2_logspace

section Leaves
variable {n w : α → ℕ}

theorem zeroPair_logspace (hn : ComputableInLogSpace n enc encUnary)
    (hw : ComputableInLogSpace w enc encUnary) :
    ComputableInLogSpace (fun a => (zeroPairCircuit (n a) (w a)).code) enc encCode := by
  have hwire := wiring_logspace
    (f := fun a => (fun _ : Fin (w a + w a) => (0 : Fin 1))) (hw.unaryAdd hw)
    (ComputableInLogSpace.const (encMid := encNat) 0) (fun _ _ => rfl)
  exact CodeLogspace.circuit_comp_logspace hn (constant_logspace hn false) hwire

def bitPairWires (n w : ℕ) (j : Fin n) : Fin (w + w) → Fin (n + 1) :=
  Fin.addCases (fun i : Fin w => if i.val = 0 then Fin.castAdd 1 j else Fin.natAdd n 0)
    (fun _ : Fin w => Fin.natAdd n 0)

theorem bitPairWires_val (n w : ℕ) (j : Fin n) (i : Fin (w + w)) :
    (bitPairWires n w j i).val = if i.val = 0 then j.val else n := by
  induction i using Fin.addCases with
  | left i => simp [bitPairWires]; split <;> rfl
  | right i =>
    have hw : w ≠ 0 := by have := i.isLt; omega
    simp [bitPairWires, -Fin.natAdd_eq_addNat, hw]

theorem bitPair_logspace {j : ∀ a, Fin (n a)}
    (hn : ComputableInLogSpace n enc encUnary)
    (hw : ComputableInLogSpace w enc encUnary)
    (hj : ComputableInLogSpace (fun a => (j a).val) enc encUnary) :
    ComputableInLogSpace (fun a => (bitPairCircuit (n a) (w a) (j a)).code) enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hraw := ((hi.unaryEq (ComputableInLogSpace.const 0)).ite (hj.comp hp) (hn.comp hp)).unaryToBinary
  have hwire := wiring_logspace (f := fun a => bitPairWires (n a) (w a) (j a))
    (hw.unaryAdd hw) hraw
    (fun a i => by simpa only [decide_eq_true_eq, Function.comp_apply] using
      bitPairWires_val (n a) (w a) (j a) i)
  have hinput := CodeLogspace.circuit_append_logspace hn
    (StandardComplexity.UniformComposition.identityCode_logspace hn)
    (constant_logspace hn false)
  exact CodeLogspace.circuit_comp_logspace hn hinput hwire

end Leaves

end PredictionDepth.FrozenPascal.UniformWeight
