import PredictionDepth.SparseCorrections.Semantics
import PredictionDepth.SparseCorrections.Candidates
import PredictionDepth.SparseCorrections.Reduction
import PredictionDepth.SparseCorrections.Length

/-!
# Circuit compiler for finite correction families

Each candidate gets a copy of the full forced response, one equality check
for every event, and a pair of outputs. The final OR reductions separately
report applicability and the gated value.
-/

namespace PredictionDepth.SparseCorrections

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity CodeLogspace CodeLogspaceFamilies Turing.MultiTapeTM
open FastComposition (Bits)
open FrozenPascal (wireBit andGate xorGate)
open FrozenPascal.UniformGuards (castInputs castInputs_code castInputs_depth)
open BooleanReduction

@[simp] private theorem append_zero (x y : Bits 1) : Fin.append x y 0 = x 0 :=
  Fin.append_left x y 0
@[simp] private theorem append_one (x y : Bits 1) : Fin.append x y 1 = y 0 :=
  Fin.append_right x y 0

private def equality : Gates 2 1 :=
  (Circuit.oneGate (σ := signature) .not id).comp xorGate

@[simp] private theorem equality_eval (x : Bits 2) :
    equality.eval interpretation x 0 = decide (x 0 = x 1) := by
  simp only [equality, Circuit.eval_comp, Circuit.eval_oneGate, interpretation, id_eq,
    FrozenPascal.xorGate_eval]
  cases x 0 <;> cases x 1 <;> rfl

/-- Evaluate a fixed rule template on its predecessor wires and compare it to
the proposed output bit. -/
def equalCheck (f : Gates a 1) (inputs : Fin a → Fin V) (out : Fin V) : Gates V 1 :=
  equality.comp ((f.comp (Circuit.wiring signature inputs)).append (wireBit out))

theorem equalCheck_true_iff (f : Gates a 1) (inputs : Fin a → Fin V) (out : Fin V)
    (x : Bits V) :
    (equalCheck f inputs out).eval interpretation x 0 = true ↔
      x out = f.eval interpretation (x ∘ inputs) 0 := by
  simp [equalCheck, Circuit.eval_comp, Circuit.eval_append, eq_comm]

theorem equalCheck_size (f : Gates a 1) (inputs : Fin a → Fin V) (out : Fin V) :
    (equalCheck f inputs out).size = f.size + 6 := by
  simp [equalCheck, equality]

theorem equalCheck_depth (f : Gates a 1) (inputs : Fin a → Fin V) (out : Fin V) :
    (equalCheck f inputs out).depth ≤ f.depth + 4 := by
  have he : equality.depth ≤ 4 :=
    (Circuit.depth_comp_le _ _).trans (by simp)
  have hw := Circuit.depth_comp_le f (Circuit.wiring signature inputs)
  have ha := Circuit.depth_append_le (f.comp (Circuit.wiring signature inputs)) (wireBit out)
  simp only [Circuit.depth_wiring, Nat.add_zero] at hw
  simp only [FrozenPascal.wireBit_depth, Nat.max_eq_left (Nat.zero_le _)] at ha
  exact (Circuit.depth_comp_le _ _).trans (by omega)

def verify (check : Fin M → Gates V 1) : Gates V 1 :=
  (andReduce M).comp (Circuit.pi check)

theorem verify_true_iff (check : Fin M → Gates V 1) (y : Bits V) :
    (verify check).eval interpretation y 0 = true ↔
      ∀ j, (check j).eval interpretation y 0 = true := by
  rw [verify, Circuit.eval_comp, andReduce_true_iff, Circuit.eval_pi]

def tag : Gates 2 2 := (wireBit 0).append andGate

private def branch (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (e : Bits M) : Gates n 2 :=
  (tag.comp ((verify check).append (wireBit obs))).comp
    (prefixCircuit (List.ofFn e) (castInputs (by simp) response))

private theorem branch_eval (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (e : Bits M) (u : Bits n) :
    let y := response.eval interpretation (Fin.append e u)
    (branch response check obs e).eval interpretation u =
      Fin.append ((verify check).eval interpretation y)
        (fun _ : Fin 1 => ((verify check).eval interpretation y 0 && y obs)) := by
  unfold branch
  simp only [Circuit.eval_comp, eval_prefixCircuit]
  have hcast {b c d : ℕ} (h : b = c) (g : Gates b d) (x : Bits c) :
      (castInputs h g).eval interpretation x = g.eval interpretation (x ∘ Fin.cast h) := by
    subst c
    rfl
  rw [hcast]
  have he : (Fin.append (fun i => (List.ofFn e)[i.val]) u ∘ Fin.cast (by simp)) =
      Fin.append e u := by
    funext i
    refine Fin.addCases (motive := fun i => _ = Fin.append e u i) ?_ ?_ i
    · intro j
      simp [Function.comp_apply, show Fin.cast (by simp : M + n = (List.ofFn e).length + n)
        (j.castAdd n) = (Fin.cast (show (List.ofFn e).length = M by simp).symm j).castAdd n from rfl]
    · intro j
      simp [Function.comp_apply, show Fin.cast (by simp : M + n = (List.ofFn e).length + n)
        (Fin.natAdd M j) = Fin.natAdd (List.ofFn e).length j from
        Fin.ext (by simp)]
  rw [he]
  funext i
  fin_cases i <;> simp [tag, Circuit.eval_append]

private def laneWiring (N : ℕ) (lane : Fin 2) : Gates (N * 2) N :=
  Circuit.wiring signature (fun j => finProdFinEquiv (j, lane))

private def collect (N : ℕ) : Gates (N * 2) 2 :=
  ((orReduce N).comp (laneWiring N 0)).append ((orReduce N).comp (laneWiring N 1))

def compile (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (candidates : Fin N → Bits M) : Gates n 2 :=
  (collect N).comp (BlockSummary.bank fun j => branch response check obs (candidates j))

theorem compile_accept_iff (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (candidates : Fin N → Bits M) (u : Bits n) :
    (compile response check obs candidates).eval interpretation u 0 = true ↔
      ∃ j, ∀ i, (check i).eval interpretation
        (response.eval interpretation (Fin.append (candidates j) u)) 0 = true := by
  simp only [compile, Circuit.eval_comp, collect, Circuit.eval_append]
  change ((orReduce N).eval interpretation ((laneWiring N 0).eval interpretation _) 0 = true) ↔ _
  rw [orReduce_true_iff]
  apply exists_congr
  intro j
  change BlockSummary.unpack ((BlockSummary.bank _).eval interpretation u) j 0 = true ↔ _
  rw [BlockSummary.bank_eval, branch_eval]
  exact verify_true_iff _ _

theorem compile_value_true_iff (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (candidates : Fin N → Bits M) (u : Bits n) :
    (compile response check obs candidates).eval interpretation u 1 = true ↔
      ∃ j, (∀ i, (check i).eval interpretation
        (response.eval interpretation (Fin.append (candidates j) u)) 0 = true) ∧
        response.eval interpretation (Fin.append (candidates j) u) obs = true := by
  simp only [compile, Circuit.eval_comp, collect, Circuit.eval_append]
  change ((orReduce N).eval interpretation ((laneWiring N 1).eval interpretation _) 0 = true) ↔ _
  rw [orReduce_true_iff]
  apply exists_congr
  intro j
  change BlockSummary.unpack ((BlockSummary.bank _).eval interpretation u) j 1 = true ↔ _
  rw [BlockSummary.bank_eval, branch_eval]
  exact Bool.and_eq_true_iff.trans (and_congr_left' (verify_true_iff _ _))

theorem compile_depth (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (candidates : Fin N → Bits M)
    (hcheck : ∀ j, (check j).depth ≤ d) :
    (compile response check obs candidates).depth ≤
      response.depth + d + 2 * Nat.clog 2 M + 2 * Nat.clog 2 N + 6 := by
  have hr (m : ℕ) : (andReduce m).depth ≤ 2 + 2 * Nat.clog 2 m := by
    simpa [andReduce, Nat.mul_comm] using reduce_depth andGate true m
  have ho (m : ℕ) : (orReduce m).depth ≤ 2 + 2 * Nat.clog 2 m := by
    simpa [orReduce, Nat.mul_comm] using reduce_depth orGate false m
  have hv : (verify check).depth ≤ d + (2 + 2 * Nat.clog 2 M) :=
    (Circuit.depth_comp_le _ _).trans (by have := Circuit.depth_pi_le check hcheck; have := hr M; omega)
  have ht : tag.depth ≤ 1 := (Circuit.depth_append_le _ _).trans (by simp)
  have hb (e : Bits M) : (branch response check obs e).depth ≤
      response.depth + d + 2 * Nat.clog 2 M + 4 := by
    have hf := Circuit.depth_comp_le (castInputs (by simp) response)
      (substituteCircuit (prefixInputs (List.ofFn e) n))
    have hsub := depth_substituteCircuit_le (prefixInputs (List.ofFn e) n)
    simp only [castInputs_depth] at hf
    have hw := Circuit.depth_append_le (verify check) (wireBit obs)
    simp only [FrozenPascal.wireBit_depth, Nat.max_eq_left (Nat.zero_le _)] at hw
    have htag := Circuit.depth_comp_le tag ((verify check).append (wireBit obs))
    exact (Circuit.depth_comp_le _ _).trans (by
      change _ + (prefixCircuit _ _).depth ≤ _
      unfold prefixCircuit
      omega)
  have hs (i : Fin 2) : ((orReduce N).comp (laneWiring N i)).depth ≤ 2 + 2 * Nat.clog 2 N :=
    (Circuit.depth_comp_le _ _).trans (by simpa [laneWiring] using ho N)
  have hc : (collect N).depth ≤ 2 + 2 * Nat.clog 2 N :=
    (Circuit.depth_append_le _ _).trans (max_le (hs 0) (hs 1))
  have hbank := BlockSummary.bank_depth (fun j : Fin N => branch response check obs (candidates j))
    (fun _ => hb _)
  exact (Circuit.depth_comp_le _ _).trans (by omega)

theorem compile_size (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (candidates : Fin N → Bits M) (hcheck : ∀ j, (check j).size ≤ s) :
    (compile response check obs candidates).size ≤
      N * 2 * (response.size + M * s + 8 * (M + 1) + 3) + 16 * (N + 1) := by
  have hr (m : ℕ) : (andReduce m).size ≤ 8 * (m + 1) := by
    exact (reduce_size andGate true m).trans (by simp; omega)
  have ho (m : ℕ) : (orReduce m).size ≤ 8 * (m + 1) := by
    exact (reduce_size orGate false m).trans (by simp; omega)
  have hv : (verify check).size ≤ M * s + 8 * (M + 1) := by
    have hs : (Circuit.pi check).size ≤ M * s := by
      rw [Circuit.size_pi]
      calc
        _ ≤ ∑ _ : Fin M, s := Finset.sum_le_sum fun j _ => hcheck j
        _ = _ := by simp
    simp only [verify, Circuit.size_comp]
    have := hr M
    omega
  have hb (e : Bits M) : (branch response check obs e).size ≤
      response.size + M * s + 8 * (M + 1) + 3 := by
    have hc {b c d : ℕ} (h : b = c) (g : Gates b d) :
        (castInputs h g).size = g.size := by subst c; rfl
    simp only [branch, Circuit.size_comp, Circuit.size_append, FrozenPascal.wireBit_size,
      tag, FrozenPascal.andGate_size, Nat.zero_add, Nat.add_zero, size_prefixCircuit, hc]
    omega
  have hbank := BlockSummary.bank_size (fun j : Fin N => branch response check obs (candidates j))
    (fun _ => hb _)
  have hc : (collect N).size ≤ 16 * (N + 1) := by
    simp only [collect, laneWiring, Circuit.size_append, Circuit.size_comp,
      Circuit.size_wiring, Nat.zero_add]
    have := ho N
    omega
  simp only [compile, Circuit.size_comp]
  exact Nat.add_le_add hbank hc

section Generator

variable {α : Type} {enc : α ↪ List Bool}

private theorem wireBit_code_logspace {n : α → ℕ} {obs : ∀ a, Fin (n a)}
    (ho : ComputableInLogSpace (fun a => (obs a).val) enc encUnary) :
    ComputableInLogSpace (fun a => (wireBit (obs a)).code) enc encCode :=
  ((ComputableInLogSpace.const []).pair
    (ComputableInLogSpace.listSingleton.comp ho.unaryToBinary)).congr_fun (fun _ => rfl)

theorem equalCheck_code_logspace {V : α → ℕ} (f : Gates a 1)
    {inputs : ∀ p, Fin a → Fin (V p)} {out : ∀ p, Fin (V p)}
    (hV : ComputableInLogSpace V enc encUnary)
    (hi : ∀ i, ComputableInLogSpace (fun p => (inputs p i).val) enc encNat)
    (ho : ComputableInLogSpace (fun p => (out p).val) enc encUnary) :
    ComputableInLogSpace (fun p => (equalCheck f (inputs p) (out p)).code) enc encCode := by
  have hw : ComputableInLogSpace
      (fun p => (Circuit.wiring signature (inputs p)).code) enc encCode :=
    ((ComputableInLogSpace.const []).pair
      (FrozenPascal.UniformWeight.ofFn_logspace hi)).congr_fun (fun _ => rfl)
  have hf := circuit_comp_logspace hV hw (ComputableInLogSpace.const f.code)
  exact circuit_comp_logspace hV (circuit_append_logspace hV hf (wireBit_code_logspace ho))
    (ComputableInLogSpace.const equality.code)

private theorem collect_code_logspace :
    ComputableInLogSpace (fun N => (collect N).code) encUnary encCode := by
  have hn : ComputableInLogSpace (fun N : ℕ => N) encUnary encUnary := ComputableInLogSpace.id
  have hw (i : Fin 2) : ComputableInLogSpace (fun N => (laneWiring N i).code) encUnary encCode := by
    apply FrozenPascal.UniformWeight.wiring_logspace hn
      (((ComputableInLogSpace.snd encUnary encUnary).unaryMulConst 2).unaryAdd
        (ComputableInLogSpace.const i.val)).unaryToBinary
    intro N j
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  have hor := reduce_code_logspace orGate false
  exact circuit_append_logspace (hn.unaryMulConst 2)
    (circuit_comp_logspace (hn.unaryMulConst 2) (hw 0) hor)
    (circuit_comp_logspace (hn.unaryMulConst 2) (hw 1) hor)

set_option maxHeartbeats 1200000 in
/-- The serializer uses the actual typed circuit constructors. Generators for
the candidate bank, local templates, and reference are independent inputs. -/
theorem compile_code_logspace {n M V N : α → ℕ}
    {response : ∀ a, Gates (M a + n a) (V a)}
    {check : ∀ a, Fin (M a) → Gates (V a) 1}
    {obs : ∀ a, Fin (V a)} {candidates : ∀ a, Fin (N a) → Bits (M a)}
    (hn : ComputableInLogSpace n enc encUnary) (hM : ComputableInLogSpace M enc encUnary)
    (hV : ComputableInLogSpace V enc encUnary) (hN : ComputableInLogSpace N enc encUnary)
    (hr : ComputableInLogSpace (fun a => (response a).code) enc encCode)
    (hc : ComputableInLogSpace
      (fun p : α × ℕ => if h : p.2 < M p.1 then (check p.1 ⟨p.2, h⟩).code else ([], []))
      (encPair enc encUnary) encCode)
    (ho : ComputableInLogSpace (fun a => (obs a).val) enc encUnary)
    (he : ComputableInLogSpace
      (fun p : α × ℕ => List.ofFn
        (if h : p.2 < N p.1 then candidates p.1 ⟨p.2, h⟩ else fun _ => false))
      (encPair enc encUnary) encBits) :
    ComputableInLogSpace (fun a => (compile (response a) (check a) (obs a) (candidates a)).code)
      enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  have hv : ComputableInLogSpace (fun a => (verify (check a)).code) enc encCode :=
    circuit_comp_logspace (c := fun a => Circuit.pi (check a)) (d := fun a => andReduce (M a))
      hV (circuit_pi_of_indexed_logspace hV hM hc) ((reduce_code_logspace andGate true).comp hM)
  have ht : ComputableInLogSpace
      (fun a => (tag.comp ((verify (check a)).append (wireBit (obs a)))).code) enc encCode :=
    circuit_comp_logspace hV (circuit_append_logspace hV hv (wireBit_code_logspace ho))
      (ComputableInLogSpace.const tag.code)
  let e (p : α × ℕ) : Bits (M p.1) :=
    if h : p.2 < N p.1 then candidates p.1 ⟨p.2, h⟩ else fun _ => false
  have hr' : ComputableInLogSpace
      (fun p => (castInputs (by simp : M p.1 + n p.1 = (List.ofFn (e p)).length + n p.1)
        (response p.1)).code) (encPair enc encUnary) encCode :=
    (hr.comp hp).congr_fun (fun _ => castInputs_code _ _)
  have hforced : ComputableInLogSpace
      (fun p => (prefixCircuit (n := n p.1) (List.ofFn (e p))
        (castInputs (by simp) (response p.1))).code)
      (encPair enc encUnary) encCode := circuit_prefix_logspace he (hn.comp hp) hr'
  have hb : ComputableInLogSpace (fun p => (branch (response p.1) (check p.1) (obs p.1) (e p)).code)
      (encPair enc encUnary) encCode := circuit_comp_logspace (hn.comp hp) hforced (ht.comp hp)
  have hbank : ComputableInLogSpace
      (fun a => (BlockSummary.bank fun j => branch (response a) (check a) (obs a)
        (candidates a j)).code) enc encCode := by
    apply BlockSummary.bank_code_logspace hn hN
    refine ((hj.unaryLt (hN.comp hp)).ite hb (ComputableInLogSpace.const ([], []))).congr_fun ?_
    intro p
    simp only [e, decide_eq_true_eq, Function.comp_apply]
    split_ifs <;> rfl
  exact circuit_comp_logspace hn hbank (collect_code_logspace.comp hN)

end Generator

section Semantics

variable {w : ℕ → ℕ} {T : ℕ}

abbrev StateBit (w : ℕ → ℕ) (T : ℕ) := (t : Fin (T + 1)) × Fin (w t.val)

def decodeTrajectory (state : Fin V ≃ StateBit w T) (y : Bits V) : Trajectory w T :=
  fun t i => y (state.symm ⟨t, i⟩)

variable {M V : ℕ} (F L : Transition w)
variable (event : Fin M ≃ Event w T) (state : Fin V ≃ StateBit w T)
variable (response : Gates (M + w 0) V) (check : Fin M → Gates V 1)

theorem encodedSupport_map (e : Residual w T) :
    (encodedSupport (e ∘ event)).map event.toEmbedding = support e := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    exact (mem_support _ _).mpr ((mem_encodedSupport _ _).mp hi)
  · intro hv
    exact Finset.mem_map.mpr ⟨event.symm v, (mem_encodedSupport _ _).mpr (by
      simpa using (mem_support e v).mp hv), event.apply_symm_apply v⟩

theorem encodedSupport_card (e : Residual w T) :
    (encodedSupport (e ∘ event)).card = (support e).card := by
  rw [← encodedSupport_map event, Finset.card_map]

private theorem checks_iff
    (hresponse : ∀ u e, decodeTrajectory state (response.eval interpretation (Fin.append e u)) =
      forcedTrajectory L u (e ∘ event.symm))
    (hcheck : ∀ y i, (check i).eval interpretation y 0 = true ↔
      let v := event i
      let z := decodeTrajectory state y
      z v.1.succ v.2 = F v.1 (z v.1.castSucc) v.2)
    (u : Layer w 0) (e : Bits M) :
    (∀ i, (check i).eval interpretation
        (response.eval interpretation (Fin.append e u)) 0 = true) ↔
      e = actualResidual F L u ∘ event := by
  simp only [hcheck]
  let y := response.eval interpretation (Fin.append e u)
  have h := hresponse u e
  change (∀ i : Fin M, (decodeTrajectory state y) (event i).1.succ (event i).2 =
    F (event i).1 ((decodeTrajectory state y) (event i).1.castSucc) (event i).2) ↔ _
  rw [event.forall_congr_right (q := fun v : Event w T =>
    (decodeTrajectory state y) v.1.succ v.2 = F v.1 ((decodeTrajectory state y) v.1.castSucc) v.2),
    ← valid_iff_pointwise, h, valid_iff_eq_actualResidual]
  constructor
  · intro he
    exact funext fun i => by simpa using congrFun he (event i)
  · rintro rfl
    exact funext fun i => by simp

/-- The observation is a coordinate of the actual trajectory. The verifier
must check the true local rule at every event, including zero correction bits. -/
theorem compile_semantics
    (hresponse : ∀ u e, decodeTrajectory state (response.eval interpretation (Fin.append e u)) =
      forcedTrajectory L u (e ∘ event.symm))
    (hcheck : ∀ y i, (check i).eval interpretation y 0 = true ↔
      let v := event i
      let z := decodeTrajectory state y
      z v.1.succ v.2 = F v.1 (z v.1.castSucc) v.2)
    (obs : Fin V) (candidates : Fin N → Bits M) (u : Layer w 0) :
    let out := (compile response check obs candidates).eval interpretation u
    (out 0 = true ↔ ∃ j, candidates j = actualResidual F L u ∘ event) ∧
      out 1 = (out 0 && actualTrajectory F u (state obs).1 (state obs).2) := by
  dsimp only
  have hv := checks_iff F L event state response check hresponse hcheck u
  have ha : (compile response check obs candidates).eval interpretation u 0 = true ↔
      ∃ j, candidates j = actualResidual F L u ∘ event :=
    (compile_accept_iff response check obs candidates u).trans (exists_congr fun j => hv (candidates j))
  refine ⟨ha, Bool.eq_iff_iff.mpr ?_⟩
  rw [compile_value_true_iff, Bool.and_eq_true, ha]
  have hy (j : Fin N) (hj : candidates j = actualResidual F L u ∘ event) :
      response.eval interpretation (Fin.append (candidates j) u) obs =
        actualTrajectory F u (state obs).1 (state obs).2 := by
    have h := hresponse u (candidates j)
    rw [hj] at h
    have he : (actualResidual F L u ∘ event) ∘ event.symm = actualResidual F L u := by
      funext i
      simp
    rw [he, reconstruct_actualResidual] at h
    have hb := congrFun (congrFun h (state obs).1) (state obs).2
    simp only [decodeTrajectory, Sigma.eta, Equiv.symm_apply_apply] at hb
    rw [hj]
    exact hb
  constructor
  · rintro ⟨j, hj, hb⟩
    have he := (hv (candidates j)).mp hj
    exact ⟨⟨j, he⟩, (hy j he).symm ▸ hb⟩
  · rintro ⟨⟨j, hj⟩, hb⟩
    exact ⟨j, (hv (candidates j)).mpr hj, hy j hj ▸ hb⟩

end Semantics

end PredictionDepth.SparseCorrections
