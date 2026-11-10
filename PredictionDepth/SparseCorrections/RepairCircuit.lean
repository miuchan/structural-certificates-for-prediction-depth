import PredictionDepth.SparseCorrections.Compiler
import PredictionDepth.SparseCorrections.Prefix
import PredictionDepth.SparseCorrections.LayerRepair
import PredictionDepth.Complexity.UniformComposition.TypedChain

/-!
# Compiling chronological repair

A round reconstructs a trajectory, checks all its updates, selects the
first failed block, and toggles just its failing coordinates. For bit
repair every coordinate forms its own block. Initial bits are passed
through as wires during all rounds.
-/

namespace PredictionDepth.SparseCorrections.RepairCircuit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FrozenPascal (andGate notGate constBit wireBit xorGate negateBank)
open BooleanReduction
open StandardComplexity UniformComposition Turing.MultiTapeTM CodeLogspace CodeLogspaceFamilies

def selectTemplate : Gates 2 1 :=
  andGate.comp ((notGate.comp (wireBit 0)).append (wireBit 1))

def selectWires (j : Fin B) : Fin 2 → Fin (B + B) :=
  ![j.castAdd B, Fin.natAdd B j]

def select (B : ℕ) : Gates (B + B) B :=
  Circuit.pi fun j => selectTemplate.comp (Circuit.wiring signature (selectWires j))

private theorem select_eval (p b : Fin B → Bool) (j : Fin B) :
    (select B).eval interpretation (Fin.append p b) j = (!p j && b j) := by
  rw [select, Circuit.eval_pi]
  change (!Fin.append p b (j.castAdd B) && Fin.append p b (Fin.natAdd B j)) = _
  rw [Fin.append_left, Fin.append_right]

private theorem select_depth (B : ℕ) : (select B).depth ≤ 2 := by
  have ht : selectTemplate.depth = 2 := by decide +kernel
  apply Circuit.depth_pi_le
  intro j
  exact (Circuit.depth_comp_le _ _).trans (by simp [ht])

private theorem select_size (B : ℕ) : (select B).size = B * 2 := by
  have ht : selectTemplate.size = 2 := by decide +kernel
  simp [select, Circuit.size_pi, ht]

def firstFailed (B : ℕ) : Gates B B :=
  (select B).comp ((Prefix.scan B).append (Circuit.id signature B))

theorem firstFailed_true_iff (b : Fin B → Bool) (j : Fin B) :
    (firstFailed B).eval interpretation b j = true ↔
      b j = true ∧ ∀ i, i < j → b i = false := by
  rw [firstFailed, Circuit.eval_comp, Circuit.eval_append, Circuit.id, Circuit.eval_wiring, Function.comp_id, select_eval,
    Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
  have he : (Prefix.scan B).eval interpretation b j ≠ true ↔ ∀ i, i < j → b i = false := by
    rw [ne_eq, Prefix.scan_true_iff]
    simp only [not_exists, not_and]
    exact forall_congr' fun i => imp_congr_right fun _ => Bool.eq_false_iff.symm
  rw [he, and_comm]

private theorem firstFailed_depth (B : ℕ) : (firstFailed B).depth ≤ 2 * Nat.clog 2 B + 4 := by
  have ha := (Circuit.depth_append_le (Prefix.scan B) (Circuit.id signature B)).trans
    (max_le (Prefix.scan_depth B) (by simp [Circuit.id]))
  exact (Circuit.depth_comp_le _ _).trans (by have := select_depth B; omega)

private theorem firstFailed_size (B : ℕ) : (firstFailed B).size ≤ 10 * (B + 1) := by
  simp only [firstFailed, Circuit.size_comp, Circuit.size_append, Circuit.id, Circuit.size_wiring,
    Nat.add_zero, select_size]
  have := Prefix.scan_size B
  omega

def updateTemplate : Gates 3 1 :=
  let old := wireBit (0 : Fin 3)
  let passing := wireBit (1 : Fin 3)
  let active := wireBit (2 : Fin 3)
  xorGate.comp (old.append (andGate.comp ((notGate.comp passing).append active)))

private theorem updateTemplate_eval (x : Fin 3 → Bool) :
    updateTemplate.eval interpretation x 0 = (x 0 ^^ (!x 1 && x 2)) := by
  simp [updateTemplate, Circuit.eval_append, notGate, interpretation]

private theorem updateTemplate_depth : updateTemplate.depth = 5 := by decide +kernel
private theorem updateTemplate_size : updateTemplate.size = 7 := by decide +kernel

def patchWires (n : ℕ) (block : Fin M → Fin B) (j : Fin M) :
    Fin 3 → Fin ((M + n) + (M + B)) :=
  ![(j.castAdd n).castAdd (M + B), Fin.natAdd (M + n) (j.castAdd B),
    Fin.natAdd (M + n) (Fin.natAdd M (block j))]

def patch (n : ℕ) (block : Fin M → Fin B) : Gates ((M + n) + (M + B)) (M + n) :=
  (Circuit.pi fun j => updateTemplate.comp (Circuit.wiring signature (patchWires n block j))).append
    (Circuit.wiring signature (fun i : Fin n => (Fin.natAdd M i).castAdd (M + B)))

private theorem patch_eval (block : Fin M → Fin B) (e : Fin M → Bool) (u : Fin n → Bool)
    (p : Fin M → Bool) (b : Fin B → Bool) :
    (patch n block).eval interpretation (Fin.append (Fin.append e u) (Fin.append p b)) =
      Fin.append (fun j => e j ^^ (!p j && b (block j))) u := by
  simp [patch, patchWires, Circuit.eval_append, updateTemplate_eval, Function.comp_def]

private theorem patch_depth (n : ℕ) (block : Fin M → Fin B) : (patch n block).depth ≤ 5 := by
  apply (Circuit.depth_append_le _ _).trans
  apply max_le
  · apply Circuit.depth_pi_le
    intro j
    exact (Circuit.depth_comp_le _ _).trans (by simp [updateTemplate_depth])
  · simp

private theorem patch_size (n : ℕ) (block : Fin M → Fin B) : (patch n block).size = M * 7 := by
  simp [patch, Circuit.size_pi, updateTemplate_size]

def evidence (check : Fin M → Gates V 1) (bad : Gates M B) : Gates V (M + B) :=
  ((Circuit.id signature M).append ((firstFailed B).comp bad)).comp (Circuit.pi check)

def stage (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (bad : Gates M B) (block : Fin M → Fin B) : Gates (M + n) (M + n) :=
  (patch n block).comp ((Circuit.id signature (M + n)).append ((evidence check bad).comp response))

theorem stage_eval (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (bad : Gates M B) (block : Fin M → Fin B) (e : Fin M → Bool) (u : Fin n → Bool) :
    let y := response.eval interpretation (Fin.append e u)
    let p : Fin M → Bool := fun j => (check j).eval interpretation y 0
    let b := (firstFailed B).eval interpretation (bad.eval interpretation p)
    (stage response check bad block).eval interpretation (Fin.append e u) =
      Fin.append (fun j => e j ^^ (!p j && b (block j))) u := by
  simp only [stage, evidence, Circuit.eval_comp, Circuit.eval_append, Circuit.id, Circuit.eval_wiring, Function.comp_id,
    Circuit.eval_pi, patch_eval]

theorem stage_depth (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (bad : Gates M B) (block : Fin M → Fin B) (hcheck : ∀ j, (check j).depth ≤ d) :
    (stage response check bad block).depth ≤ response.depth + d + bad.depth + 2 * Nat.clog 2 B + 9 := by
  have hselect := (Circuit.depth_comp_le (firstFailed B) bad).trans
    (Nat.add_le_add_right (firstFailed_depth B) bad.depth)
  have hpass := Circuit.depth_pi_le check hcheck
  have hbank := (Circuit.depth_append_le (Circuit.id signature M) ((firstFailed B).comp bad)).trans
    (max_le (by simp [Circuit.id]) hselect)
  have hev : (evidence check bad).depth ≤ (2 * Nat.clog 2 B + 4 + bad.depth) + d :=
    (Circuit.depth_comp_le _ _).trans (Nat.add_le_add hbank hpass)
  have hp := (Circuit.depth_comp_le (evidence check bad) response).trans
    (Nat.add_le_add_right hev response.depth)
  have ha := (Circuit.depth_append_le (Circuit.id signature (M + n))
    ((evidence check bad).comp response)).trans (max_le (by simp [Circuit.id]) hp)
  exact (Circuit.depth_comp_le _ _).trans (by have := patch_depth n block; omega)

theorem stage_size (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (bad : Gates M B) (block : Fin M → Fin B) (hcheck : ∀ j, (check j).size ≤ s) :
    (stage response check bad block).size ≤ response.size + M * (s + 7) + bad.size + 10 * (B + 1) := by
  have hpass : (Circuit.pi check).size ≤ M * s := by
    rw [Circuit.size_pi]
    calc
      _ ≤ ∑ _ : Fin M, s := Finset.sum_le_sum fun j _ => hcheck j
      _ = _ := by simp
  simp only [stage, evidence, Circuit.size_comp, Circuit.size_append, Circuit.id,
    Circuit.size_wiring, patch_size, Nat.mul_add]
  have := firstFailed_size B
  omega

def seed (M n : ℕ) : Gates n (M + n) :=
  (Circuit.pi fun _ : Fin M => constBit n false).append (Circuit.id signature n)

private theorem seed_depth (M n : ℕ) : (seed M n).depth ≤ 1 :=
  (Circuit.depth_append_le _ _).trans
    (max_le (Circuit.depth_pi_le _ fun _ => by simp) (by simp [Circuit.id]))

def finish (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) : Gates (M + n) 2 :=
  (tag.comp ((verify check).append (wireBit obs))).comp response

private theorem finish_eval (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (x : Fin (M + n) → Bool) :
    let y := response.eval interpretation x
    (finish response check obs).eval interpretation x 0 = (verify check).eval interpretation y 0 ∧
      (finish response check obs).eval interpretation x 1 =
        ((verify check).eval interpretation y 0 && y obs) := by
  constructor <;> simp [finish, tag, Circuit.eval_append]

private theorem finish_depth (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (hcheck : ∀ j, (check j).depth ≤ d) :
    (finish response check obs).depth ≤ response.depth + d + 2 * Nat.clog 2 M + 3 := by
  have hred : (andReduce M).depth ≤ 2 + 2 * Nat.clog 2 M := by
    simpa [andReduce, Nat.mul_comm] using reduce_depth andGate true M
  have hv := (Circuit.depth_comp_le (andReduce M) (Circuit.pi check)).trans
    (Nat.add_le_add hred (Circuit.depth_pi_le check hcheck))
  have ha := (Circuit.depth_append_le (verify check) (wireBit obs)).trans
    (max_le (show (verify check).depth ≤ _ from hv) (by simp))
  have ht : tag.depth ≤ 1 := (Circuit.depth_append_le _ _).trans (by simp)
  have hc := (Circuit.depth_comp_le tag ((verify check).append (wireBit obs))).trans
    (Nat.add_le_add ht ha)
  exact (Circuit.depth_comp_le _ _).trans (by omega)

private theorem finish_size (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (hcheck : ∀ j, (check j).size ≤ s) :
    (finish response check obs).size ≤ response.size + M * s + 8 * (M + 1) + 1 := by
  have hred : (andReduce M).size ≤ 8 * (M + 1) := by
    have h := reduce_size andGate true M
    simp only [FrozenPascal.andGate_size] at h
    change (reduce andGate true M).size ≤ _
    omega
  have hpass : (Circuit.pi check).size ≤ M * s := by
    rw [Circuit.size_pi]
    calc
      _ ≤ ∑ _ : Fin M, s := Finset.sum_le_sum fun j _ => hcheck j
      _ = _ := by simp
  simp only [finish, tag, verify, Circuit.size_comp, Circuit.size_append, FrozenPascal.wireBit_size,
    FrozenPascal.andGate_size, Nat.zero_add, Nat.add_zero]
  omega

def compile (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (bad : Gates M B) (block : Fin M → Fin B) (obs : Fin V) (k : ℕ) : Gates n 2 :=
  (finish response check obs).comp (normalizedChain (seed M n)
    (List.replicate k (stage response check bad block)))

private theorem fold_rounds (eval : S → X → X) (s : S) (x : X) (k : ℕ) :
    (List.replicate k s).foldl (fun a g => eval g a) x = (eval s)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]

theorem compile_depth (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (bad : Gates M B) (block : Fin M → Fin B) (obs : Fin V) (k : ℕ)
    (hcheck : ∀ j, (check j).depth ≤ d) :
    (compile response check bad block obs k).depth ≤
      k * (response.depth + d + bad.depth + 2 * Nat.clog 2 B + 10) +
        (response.depth + d + 2 * Nat.clog 2 M + 5) := by
  have hc : (normalizedChain (seed M n) (List.replicate k (stage response check bad block))).depth ≤
      (seed M n).depth + 1 + k * ((stage response check bad block).depth + 1) := by
    simpa only [List.map_replicate, List.sum_replicate, Nat.nsmul_eq_mul] using
      normalizedChain_depth (seed M n) (List.replicate k (stage response check bad block))
  have hi : k * ((stage response check bad block).depth + 1) ≤
      k * (response.depth + d + bad.depth + 2 * Nat.clog 2 B + 10) :=
    Nat.mul_le_mul_left k (by have := stage_depth response check bad block hcheck; omega)
  have hf := finish_depth response check obs hcheck
  exact (Circuit.depth_comp_le _ _).trans (by have := seed_depth M n; omega)

theorem compile_size (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (bad : Gates M B) (block : Fin M → Fin B) (obs : Fin V) (k : ℕ)
    (hcheck : ∀ j, (check j).size ≤ s) :
    (compile response check bad block obs k).size ≤
      k * (response.size + M * (s + 7) + bad.size + 10 * (B + 1) + (M + n)) +
        (response.size + M * s + 8 * (M + 1) + 1) + M + (M + n) := by
  have hi := Nat.mul_le_mul_left k
    (Nat.add_le_add_right (stage_size response check bad block hcheck) (M + n))
  have hf := finish_size response check obs hcheck
  simp [compile, normalizedChain_size, seed, Circuit.id, Circuit.size_pi]
  omega

section Semantics

variable {w : ℕ → ℕ} {T : ℕ}
variable (F L : Transition w) (event : Fin M ≃ Event w T) (state : Fin V ≃ StateBit w T)
variable (response : Gates (M + w 0) V) (check : Fin M → Gates V 1)
variable (bad : Gates M B) (rank : Event w T → Fin B)

private theorem trigger_iff (p : Fin M → Bool)
    (hb : ∀ b, (bad.eval interpretation p b = true) ↔
      ∃ j, rank (event j) = b ∧ p j = false) (i : Fin M) :
    (!p i && (firstFailed B).eval interpretation (bad.eval interpretation p) (rank (event i))) =
      true ↔ p i = false ∧ ∀ j, rank (event j) < rank (event i) → p j = true := by
  rw [Bool.and_eq_true, Bool.not_eq_true', firstFailed_true_iff]
  constructor
  · rintro ⟨hi, _, hp⟩
    refine ⟨hi, fun j hj => ?_⟩
    cases h : p j with
    | true => rfl
    | false =>
      have hb' := (hb (rank (event j))).mpr ⟨j, rfl, h⟩
      rw [hp _ hj] at hb'
      contradiction
  · rintro ⟨hi, hp⟩
    refine ⟨hi, (hb _).mpr ⟨i, rfl, hi⟩, fun b hb' => Bool.eq_false_iff.mpr ?_⟩
    intro ht
    obtain ⟨j, h, hfalse⟩ := (hb b).mp ht
    have htrue := hp j (h ▸ hb')
    rw [hfalse] at htrue
    contradiction

variable
  (hresponse : ∀ u e, decodeTrajectory state (response.eval interpretation (Fin.append e u)) =
    forcedTrajectory L u (e ∘ event.symm))
  (hcheck : ∀ y i, (check i).eval interpretation y 0 = true ↔
    let v := event i
    let z := decodeTrajectory state y
    z v.1.succ v.2 = F v.1 (z v.1.castSucc) v.2)
  (hbad : ∀ p b, (bad.eval interpretation p b = true) ↔
    ∃ j, rank (event j) = b ∧ p j = false)

include hresponse hcheck hbad in
private theorem stage_simulates
    (u : Layer w 0) (step : Residual w T → Residual w T)
    (hstep : ∀ e v, step e v =
      if ¬ Passes F L u e v ∧ (∀ z, rank z < rank v → Passes F L u e z) then !e v else e v)
    (e : Residual w T) :
    (stage response check bad (rank ∘ event)).eval interpretation (Fin.append (e ∘ event) u) =
      Fin.append (step e ∘ event) u := by
  rw [stage_eval]
  let y := response.eval interpretation (Fin.append (e ∘ event) u)
  let p : Fin M → Bool := fun j => (check j).eval interpretation y 0
  have he : (e ∘ event) ∘ event.symm = e := by funext v; simp
  have hy : decodeTrajectory state y = forcedTrajectory L u e := by
    rw [show decodeTrajectory state y = forcedTrajectory L u ((e ∘ event) ∘ event.symm)
      from hresponse _ _, he]
  have hp (j : Fin M) : p j = true ↔ Passes F L u e (event j) := by
    rw [show p j = true ↔ _ from hcheck y j]
    simp only [hy, Passes]
  have hpf (j : Fin M) : p j = false ↔ ¬ Passes F L u e (event j) :=
    Bool.eq_false_iff.trans (not_congr (hp j))
  apply congrArg (fun r : Fin M → Bool => Fin.append r u)
  funext j
  let mask := !p j && (firstFailed B).eval interpretation (bad.eval interpretation p) (rank (event j))
  have hm : mask = true ↔ ¬ Passes F L u e (event j) ∧
      ∀ v, rank v < rank (event j) → Passes F L u e v := by
    refine (trigger_iff event bad rank p (hbad p) j).trans (and_congr (hpf j) ?_)
    rw [← event.forall_congr_right (q := fun v => rank v < rank (event j) → Passes F L u e v)]
    exact forall_congr' fun i => imp_congr_right (fun _ => hp i)
  change (e (event j) ^^ mask) = step e (event j)
  rw [hstep]
  by_cases h : mask = true
  · rw [h, ite_eq_left (hm.mp h)]
    cases e (event j) <;> rfl
  · rw [Bool.eq_false_iff.mpr h, ite_eq_right (fun h' => h (hm.mpr h'))]
    exact Bool.xor_false _

include hresponse hcheck hbad in
/-- A ranked block transition compiles to a bounded sequence of rounds
followed by complete verification and gated readout. -/
theorem compile_semantics
    (obs : Fin V) (u : Layer w 0) (k : ℕ) (step : Residual w T → Residual w T)
    (hstep : ∀ e v, step e v =
      if ¬ Passes F L u e v ∧ (∀ z, rank z < rank v → Passes F L u e z) then !e v else e v) :
    let out := (compile response check bad (rank ∘ event) obs k).eval interpretation u
    let final := forcedTrajectory L u (step^[k] (fun _ => false))
    (out 0 = true ↔ Valid F final) ∧
      out 1 = (out 0 && actualTrajectory F u (state obs).1 (state obs).2) := by
  let s := stage response check bad (rank ∘ event)
  have hs (k : ℕ) : (s.eval interpretation)^[k] ((seed M (w 0)).eval interpretation u) =
      Fin.append ((step^[k] (fun _ => false)) ∘ event) u := by
    induction k with
    | zero =>
      simp [seed, Circuit.id, Circuit.eval_append, Function.comp_def]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact stage_simulates F L event state response check bad rank hresponse hcheck hbad u step hstep _
  let e := step^[k] (fun _ => false)
  let y := response.eval interpretation (Fin.append (e ∘ event) u)
  have hy : decodeTrajectory state y = forcedTrajectory L u e := by
    have he : (e ∘ event) ∘ event.symm = e := by funext v; simp
    exact (hresponse u (e ∘ event)).trans (congrArg (forcedTrajectory L u) he)
  let out := (compile response check bad (rank ∘ event) obs k).eval interpretation u
  have hout : out = (finish response check obs).eval interpretation (Fin.append (e ∘ event) u) := by
    simp only [out, compile, Circuit.eval_comp]
    rw [normalizedChain_eval, circuitChain_eval]
    have h := fold_rounds (fun c : Gates (M + w 0) (M + w 0) => c.eval interpretation)
      s ((seed M (w 0)).eval interpretation u) k
    exact congrArg ((finish response check obs).eval interpretation) (h.trans (hs k))
  obtain ⟨h₀, h₁⟩ := finish_eval response check obs (Fin.append (e ∘ event) u)
  change (out 0 = true ↔ Valid F (forcedTrajectory L u e)) ∧
    out 1 = (out 0 && actualTrajectory F u (state obs).1 (state obs).2)
  have hacc : out 0 = (verify check).eval interpretation y 0 :=
    (congrFun hout 0).trans h₀
  have hvalue : out 1 = (out 0 && y obs) := by
    exact (congrFun hout 1).trans (h₁.trans (congrArg (fun b => b && y obs) hacc.symm))
  have ha : out 0 = true ↔ Valid F (forcedTrajectory L u e) := by
    rw [hacc, verify_true_iff, valid_iff_pointwise, ← event.forall_congr_right]
    refine forall_congr' fun j => (hcheck y j).trans ?_
    dsimp only
    rw [hy]
  refine ⟨ha, ?_⟩
  rw [hvalue]
  cases h : out 0 with
  | false => rfl
  | true =>
    have hv := eq_actualTrajectory_of_valid (forcedTrajectory_zero L u e) (ha.mp h)
    have ho := congrArg (fun z : Trajectory w T => z (state obs).1 (state obs).2) (hy.trans hv)
    have hread : decodeTrajectory state y (state obs).1 (state obs).2 = y obs := by
      unfold decodeTrajectory
      exact congrArg y (by rw [Sigma.eta, Equiv.symm_apply_apply])
    rw [hread] at ho
    exact congrArg (fun b => true && b) ho

def compileBits (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (k : ℕ) : Gates n 2 :=
  compile response check (negateBank M) id obs k

def indexedOrder (event : Fin M ≃ Event w T)
    (hchron : ∀ v z : Event w T, v.1.val < z.1.val → event.symm v < event.symm z) :
    EventOrder w T where
  rank v := (event.symm v).val
  injective := fun _ _ h => event.symm.injective (Fin.ext h)
  chronological := hchron

include hresponse hcheck in
theorem compileBits_correct
    (hchron : ∀ v z : Event w T, v.1.val < z.1.val → event.symm v < event.symm z)
    (obs : Fin V) (u : Layer w 0) (k : ℕ) :
    let out := (compileBits response check obs k).eval interpretation u
    (out 0 = true ↔ Sparse (actualResidual F L u : Residual w T) k) ∧
      out 1 = (out 0 && actualTrajectory F u (state obs).1 (state obs).2) := by
  have hb (p : Fin M → Bool) (b : Fin M) :
      (negateBank M).eval interpretation p b = true ↔
        ∃ j, event.symm (event j) = b ∧ p j = false := by
    simp [negateBank, notGate, interpretation]
  have h := compile_semantics F L event state response check (negateBank M) event.symm
    hresponse hcheck hb obs u k (repair (indexedOrder event hchron) F L u) (by
      intro e v
      rfl)
  dsimp only at h ⊢
  rw [repair_accept_iff] at h
  have hi : (event.symm ∘ event : Fin M → Fin M) = id := by funext j; simp
  rw [hi] at h
  exact h

include hresponse hcheck in
theorem compileLayers_correct (bad : Gates M T)
    (hb : ∀ p b, bad.eval interpretation p b = true ↔ ∃ j, (event j).1 = b ∧ p j = false)
    (obs : Fin V) (u : Layer w 0) (k : ℕ) :
    let out := (compile response check bad (fun j => (event j).1) obs k).eval interpretation u
    (out 0 = true ↔ (layerSupport (actualResidual F L u : Residual w T)).card ≤ k) ∧
      out 1 = (out 0 && actualTrajectory F u (state obs).1 (state obs).2) := by
  have h := compile_semantics F L event state response check bad (fun v => v.1)
    hresponse hcheck hb obs u k (repairLayer F L u) (by intro e v; rfl)
  dsimp only at h ⊢
  rw [repairLayer_accept_iff] at h
  exact h

end Semantics

end PredictionDepth.SparseCorrections.RepairCircuit
