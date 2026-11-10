import PredictionDepth.SparseCorrections.RepairCircuit

/-!
# Logspace generation of chronological repair

The prefix circuit, local checks, and each repair stage are serialized before
the normalized-chain generator streams the indexed sequence of rounds.
-/

namespace PredictionDepth.SparseCorrections.RepairCircuit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FrozenPascal (andGate notGate constBit wireBit negateBank)
open StandardComplexity UniformComposition Turing.MultiTapeTM CodeLogspace CodeLogspaceFamilies

section Families
variable {α : Type} {enc : α ↪ List Bool}

private theorem templateBank_logspace {n m : α → ℕ} {q : ℕ}
    (template : Gates q 1) {wire : ∀ a, Fin (m a) → Fin q → Fin (n a)}
    {ref : Fin q → α × ℕ → ℕ}
    (hn : ComputableInLogSpace n enc encUnary) (hm : ComputableInLogSpace m enc encUnary)
    (href : ∀ i, ComputableInLogSpace (ref i) (encPair enc encUnary) encUnary)
    (he : ∀ a j i, (wire a j i).val = ref i (a, j.val)) :
    ComputableInLogSpace
      (fun a => (Circuit.pi fun j => template.comp (Circuit.wiring signature (wire a j))).code)
      enc encCode := by
  let wiringCode (p : α × ℕ) : RawCode := ([], List.ofFn (fun i => ref i p))
  have hw : ComputableInLogSpace wiringCode (encPair enc encUnary) encCode :=
    (ComputableInLogSpace.const []).pair
      (FrozenPascal.UniformWeight.ofFn_logspace (fun i => (href i).unaryToBinary))
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  have ht := compCode_logspace (hn.comp hp) (ComputableInLogSpace.const template.code) hw
    (fun p => by
      change BoundedReferences ((wiringCode p).2.length + template.code.1.length) template.code
      rw [Circuit.length_code_fst]
      simpa [wiringCode] using circuit_boundedReferences template)
  apply circuit_pi_of_indexed_logspace hn hm
  refine ((hj.unaryLt (hm.comp hp)).ite ht (ComputableInLogSpace.const ([], []))).congr_fun ?_
  intro p
  simp only [Function.comp_apply, decide_eq_true_eq]
  split_ifs with hjm
  · have hw' : (Circuit.wiring signature (wire p.1 ⟨p.2, hjm⟩)).code = wiringCode p := by
      rw [Circuit.code_wiring]
      exact congrArg (fun g : Fin q → ℕ => ([], List.ofFn g)) (funext fun i => he p.1 ⟨p.2, hjm⟩ i)
    rw [← compCode_code, hw']
  · rfl

private theorem patch_code_logspace {n M B : α → ℕ}
    {block : ∀ a, Fin (M a) → Fin (B a)} {blockAt : α × ℕ → ℕ}
    (hn : ComputableInLogSpace n enc encUnary) (hM : ComputableInLogSpace M enc encUnary)
    (hB : ComputableInLogSpace B enc encUnary)
    (hblock : ComputableInLogSpace blockAt (encPair enc encUnary) encUnary)
    (hblock_eq : ∀ a j, (block a j).val = blockAt (a, j.val)) :
    ComputableInLogSpace (fun a => (patch (n a) (block a)).code) enc encCode := by
  have hW := hM.unaryAdd hn
  have hinput := hW.unaryAdd (hM.unaryAdd hB)
  have ha := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  let ref (i : Fin 3) (p : α × ℕ) :=
    ![p.2, (M p.1 + n p.1) + p.2, (M p.1 + n p.1) + (M p.1 + blockAt p)] i
  have href (i : Fin 3) : ComputableInLogSpace (ref i) (encPair enc encUnary) encUnary := by
    fin_cases i
    · exact hj
    · exact (hW.comp ha).unaryAdd hj
    · exact (hW.comp ha).unaryAdd ((hM.comp ha).unaryAdd hblock)
  have hpatch := templateBank_logspace updateTemplate
    (wire := fun a => patchWires (n a) (block a)) hinput hM href (fun a j i => by
      fin_cases i
      · rfl
      · rfl
      · exact congrArg (fun x => (M a + n a) + (M a + x)) (hblock_eq a j))
  have hpass : ComputableInLogSpace
      (fun a => (Circuit.wiring signature
        (fun i : Fin (n a) => (Fin.natAdd (M a) i).castAdd (M a + B a))).code) enc encCode :=
    FrozenPascal.Code.wiring hn (((hM.comp ha).unaryAdd hj).unaryToBinary) (fun _ _ => rfl)
  exact circuit_append_logspace hinput hpatch hpass

private theorem seed_code_logspace {n M : α → ℕ}
    (hn : ComputableInLogSpace n enc encUnary) (hM : ComputableInLogSpace M enc encUnary) :
    ComputableInLogSpace (fun a => (seed (M a) (n a)).code) enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  have hz : ComputableInLogSpace
      (fun p : α × ℕ => if p.2 < M p.1 then (constBit (n p.1) false).code else ([], []))
      (encPair enc encUnary) encCode :=
    ((hj.unaryLt (hM.comp hp)).ite ((FrozenPascal.Code.constant hn false).comp hp)
      (ComputableInLogSpace.const ([], []))).congr_fun (fun p => by
        simp only [Function.comp_apply, decide_eq_true_eq])
  exact circuit_append_logspace hn (circuit_pi_of_indexed_logspace hn hM
    (hz.congr_fun fun p => by split_ifs <;> rfl)) (identityCode_logspace hn)

end Families

theorem negateBank_code_logspace :
    ComputableInLogSpace (fun m => (negateBank m).code) encUnary encCode := by
  exact templateBank_logspace notGate (wire := fun _ j _ => j)
    ComputableInLogSpace.id ComputableInLogSpace.id
    (fun _ => ComputableInLogSpace.snd encUnary encUnary) (fun _ _ _ => rfl)

private theorem select_code_logspace :
    ComputableInLogSpace (fun B => (select B).code) encUnary encCode := by
  have hB : ComputableInLogSpace (fun B : ℕ => B) encUnary encUnary :=
    ComputableInLogSpace.id
  have hp := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  let ref (i : Fin 2) (p : ℕ × ℕ) := ![p.2, p.1 + p.2] i
  have href (i : Fin 2) : ComputableInLogSpace (ref i) (encPair encUnary encUnary) encUnary := by
    fin_cases i
    · exact hj
    · exact hp.unaryAdd hj
  exact templateBank_logspace selectTemplate (wire := fun _ => selectWires)
    (hB.unaryAdd hB) hB href (fun _ _ i => by fin_cases i <;> rfl)

private theorem firstFailed_code_logspace :
    ComputableInLogSpace (fun B => (firstFailed B).code) encUnary encCode := by
  have hB : ComputableInLogSpace (fun B : ℕ => B) encUnary encUnary :=
    ComputableInLogSpace.id
  exact circuit_comp_logspace hB
    (circuit_append_logspace hB Prefix.scan_code_logspace (identityCode_logspace hB))
    select_code_logspace

set_option maxHeartbeats 1200000 in
/-- Generate the complete gate list and output addresses of the typed repair
predictor for a logspace-indexed round budget and local components. -/
theorem compile_code_logspace {α : Type} {enc : α ↪ List Bool} {n M V B k : α → ℕ}
    {response : ∀ a, Gates (M a + n a) (V a)}
    {check : ∀ a, Fin (M a) → Gates (V a) 1}
    {bad : ∀ a, Gates (M a) (B a)}
    {block : ∀ a, Fin (M a) → Fin (B a)}
    {obs : ∀ a, Fin (V a)}
    {blockAt : α × ℕ → ℕ}
    (hn : ComputableInLogSpace n enc encUnary) (hM : ComputableInLogSpace M enc encUnary)
    (hV : ComputableInLogSpace V enc encUnary) (hB : ComputableInLogSpace B enc encUnary)
    (hk : ComputableInLogSpace k enc encUnary)
    (hresponse : ComputableInLogSpace (fun a => (response a).code) enc encCode)
    (hcheck : ComputableInLogSpace
      (fun p : α × ℕ => if h : p.2 < M p.1 then (check p.1 ⟨p.2, h⟩).code else ([], []))
      (encPair enc encUnary) encCode)
    (hbad : ComputableInLogSpace (fun a => (bad a).code) enc encCode)
    (hblock : ComputableInLogSpace blockAt (encPair enc encUnary) encUnary)
    (hblock_eq : ∀ a j, (block a j).val = blockAt (a, j.val))
    (hobs : ComputableInLogSpace (fun a => (obs a).val) enc encUnary) :
    ComputableInLogSpace
      (fun a => (compile (response a) (check a) (bad a) (block a) (obs a) (k a)).code) enc encCode := by
  have hW := hM.unaryAdd hn
  have hchecks := circuit_pi_of_indexed_logspace hV hM hcheck
  have hfirst := circuit_comp_logspace hM hbad (firstFailed_code_logspace.comp hB)
  have hev : ComputableInLogSpace (fun a => (evidence (check a) (bad a)).code) enc encCode :=
    circuit_comp_logspace hV hchecks
      (circuit_append_logspace hM (identityCode_logspace hM) hfirst)
  have hstage : ComputableInLogSpace
      (fun a => (stage (response a) (check a) (bad a) (block a)).code) enc encCode :=
    circuit_comp_logspace hW
      (circuit_append_logspace hW (identityCode_logspace hW)
        (circuit_comp_logspace hW hresponse hev))
      (patch_code_logspace hn hM hB hblock hblock_eq)
  have hrounds : ComputableInLogSpace
      (fun a => (List.replicate (k a) (stage (response a) (check a) (bad a) (block a))).map Circuit.code)
      enc (encList encCode) :=
    (map_range hk (hstage.comp (ComputableInLogSpace.fst enc encUnary))).congr_fun
      (fun a => by simp [List.map_const'])
  have hchain := normalizedChain_logspace hn hW (seed_code_logspace hn hM) hrounds
  have hver : ComputableInLogSpace (fun a => (verify (check a)).code) enc encCode :=
    circuit_comp_logspace hV hchecks ((BooleanReduction.reduce_code_logspace andGate true).comp hM)
  have hwire : ComputableInLogSpace (fun a => (wireBit (obs a)).code) enc encCode :=
    FrozenPascal.Code.wire hobs.unaryToBinary (fun _ => rfl)
  have htag := circuit_comp_logspace hV (circuit_append_logspace hV hver hwire)
    (ComputableInLogSpace.const tag.code)
  exact circuit_comp_logspace hn hchain (circuit_comp_logspace hW hresponse htag)

end PredictionDepth.SparseCorrections.RepairCircuit
