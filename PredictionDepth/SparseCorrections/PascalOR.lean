import PredictionDepth.SparseCorrections.PascalResponse
import PredictionDepth.SparseCorrections.Certificate

/-!
# A uniform OR certificate against the Pascal reference

The independent OR evaluation is the disjunction of the (T+1) contributing
initial sites. The certificate verifies the complete two-sided cone even
though the observation only depends on its right half.
-/

namespace PredictionDepth.SparseCorrections.Pascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity Turing.MultiTapeTM
open BooleanReduction (orGate)

def orRule : Cone.Config 1 → Cone.Config 1 := applyNeighbors (· || ·)

theorem orRule_iterate_true_iff (x : Cone.Config 1) (t : ℕ) (i : ℤ) (a : Fin 1) :
    ((orRule^[t]) x) i a = true ↔ ∃ j : ℤ, i ≤ j ∧ j ≤ i + (t : ℤ) ∧ x j a = true := by
  induction t generalizing i with
  | zero =>
    simp only [Function.iterate_zero_apply, Nat.cast_zero, add_zero]
    constructor
    · exact fun h => ⟨i, le_rfl, le_rfl, h⟩
    · rintro ⟨j, hlo, hhi, h⟩
      rwa [le_antisymm hlo hhi]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    change (((orRule^[t]) x) i a || ((orRule^[t]) x) (i + 1) a) = true ↔ _
    rw [Bool.or_eq_true, ih, ih]
    constructor
    · rintro (⟨j, hj, hjt, hx⟩ | ⟨j, hj, hjt, hx⟩)
      all_goals exact ⟨j, by omega, by omega, hx⟩
    · rintro ⟨j, hj, hjt, hx⟩
      by_cases he : j = i
      · exact Or.inl ⟨j, hj, by omega, hx⟩
      · exact Or.inr ⟨j, by omega, by omega, hx⟩

/-- The reference differs from OR exactly when both predecessor bits are true. -/
theorem orResidual_eq (T : ℕ) (u : Layer (Width T) 0) (t : Fin T)
    (j : Fin (Width T (t.val + 1))) :
    actualResidual (Cone.transition 1 T orRule) (Cone.transition 1 T rule) u ⟨t, j⟩ =
      let y := actualLayer (Cone.transition 1 T orRule) u t.val
      y (predecessor t.isLt j 0) && y (predecessor t.isLt j 1) := by
  unfold actualResidual
  simp only [actualLayer]
  rw [orRule, transition_applyNeighbors t.isLt, rule, transition_applyNeighbors t.isLt]
  cases actualLayer (Cone.transition 1 T (applyNeighbors (· || ·))) u t.val
      (predecessor t.isLt j 0) <;>
    cases actualLayer (Cone.transition 1 T (applyNeighbors (· || ·))) u t.val
      (predecessor t.isLt j 1) <;> rfl

private abbrev encEvent := encPair encUnary encUnary

private def rawPredecessor (p : ℕ × ℕ) (d : Fin 2) : ℕ :=
  Cone.offset 1 1 p.1 (sourceTime p.1 p.2 - 1) + (sourcePosition p.1 p.2 + 1 + d.val)

private def rawOutput (p : ℕ × ℕ) : ℕ :=
  Cone.offset 1 1 p.1 (sourceTime p.1 p.2) + sourcePosition p.1 p.2

private theorem stateCount_pos (T : ℕ) : 0 < V T := by
  change 0 < Cone.stateCount 1 1 T
  rw [Cone.stateCount_eq]
  positivity

private def checkInput (p : ℕ × ℕ) (d : Fin 2) : Fin (V p.1) :=
  ⟨rawPredecessor p d % V p.1, Nat.mod_lt _ (stateCount_pos _)⟩

private def checkOutput (p : ℕ × ℕ) : Fin (V p.1) :=
  ⟨rawOutput p % V p.1, Nat.mod_lt _ (stateCount_pos _)⟩

private theorem checkInput_eq {T : ℕ} (t : Fin T) (j : Fin (Width T (t.val + 1))) (d : Fin 2) :
    checkInput (T, (Cone.eventIndex 1 1 T ⟨t, j⟩).val) d =
      Cone.stateIndex 1 1 T ⟨t.castSucc, predecessor t.isLt j d⟩ := by
  apply Fin.ext
  let k := Cone.stateIndex 1 1 T ⟨t.castSucc, predecessor t.isLt j d⟩
  have h : rawPredecessor (T, (Cone.eventIndex 1 1 T ⟨t, j⟩).val) d = k.val := by
    simp [rawPredecessor, sourceTime_event, sourcePosition_event, k,
      Cone.stateIndex_val, predecessor]
  change rawPredecessor (T, (Cone.eventIndex 1 1 T ⟨t, j⟩).val) d % V T = k.val
  rw [h, Nat.mod_eq_of_lt k.isLt]

private theorem checkOutput_eq {T : ℕ} (t : Fin T) (j : Fin (Width T (t.val + 1))) :
    checkOutput (T, (Cone.eventIndex 1 1 T ⟨t, j⟩).val) = Cone.stateIndex 1 1 T ⟨t.succ, j⟩ := by
  apply Fin.ext
  let k := Cone.stateIndex 1 1 T ⟨t.succ, j⟩
  have h : rawOutput (T, (Cone.eventIndex 1 1 T ⟨t, j⟩).val) = k.val := by
    simp [rawOutput, sourceTime_event, sourcePosition_event, k, Cone.stateIndex_val]
  change rawOutput (T, (Cone.eventIndex 1 1 T ⟨t, j⟩).val) % V T = k.val
  rw [h, Nat.mod_eq_of_lt k.isLt]

def orCheck (T : ℕ) (i : Fin (M T)) : Gates (V T) 1 :=
  equalCheck orGate (checkInput (T, i.val)) (checkOutput (T, i.val))

theorem orCheck_depth (T : ℕ) (i : Fin (M T)) : (orCheck T i).depth ≤ 5 :=
  (equalCheck_depth orGate _ _).trans (by simp)

private theorem decode_read {T : ℕ} (t : Fin (T + 1)) (i : Fin (Width T t.val))
    (y : Fin (V T) → Bool) :
    decodeTrajectory (Cone.stateIndex 1 1 T).symm y t i = y (Cone.stateIndex 1 1 T ⟨t, i⟩) :=
  rfl

theorem orCheck_correct (T : ℕ) (y : Fin (V T) → Bool) (i : Fin (M T)) :
    (orCheck T i).eval interpretation y 0 = true ↔
      let v := (Cone.eventIndex 1 1 T).symm i
      let z := decodeTrajectory (Cone.stateIndex 1 1 T).symm y
      z v.1.succ v.2 = Cone.transition 1 T orRule v.1 (z v.1.castSucc) v.2 := by
  rw [orCheck, equalCheck_true_iff]
  let v := (Cone.eventIndex 1 1 T).symm i
  let z := decodeTrajectory (Cone.stateIndex 1 1 T).symm y
  change y (checkOutput (T, i.val)) = orGate.eval interpretation (y ∘ checkInput (T, i.val)) 0 ↔
    z v.1.succ v.2 = Cone.transition 1 T orRule v.1 (z v.1.castSucc) v.2
  have h : (Cone.eventIndex 1 1 T ⟨v.1, v.2⟩).val = i.val := by simp [v, Sigma.eta]
  have ho := checkOutput_eq v.1 v.2
  have h₀ := checkInput_eq v.1 v.2 0
  have h₁ := checkInput_eq v.1 v.2 1
  rw [h] at ho h₀ h₁
  rw [BooleanReduction.orGate_eval, orRule, transition_applyNeighbors v.1.isLt]
  simp only [Function.comp_apply, ho, h₀, h₁, z, decode_read]

private theorem orCheck_code_logspace :
    ComputableInLogSpace (fun p : ℕ × ℕ =>
      if h : p.2 < M p.1 then (orCheck p.1 ⟨p.2, h⟩).code else ([], [])) encEvent encCode := by
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have hm := (Cone.eventCount_logspace 1 1).comp hT
  have hv := (Cone.stateCount_logspace 1 1).comp hT
  have hs := sourceTime_logspace
  have hj := sourcePosition_logspace
  have ho := (Cone.offset_logspace 1 1).comp (hT.pair hs)
  have hprev := (Cone.offset_logspace 1 1).comp
    (hT.pair (hs.unarySub (ComputableInLogSpace.const 1)))
  have hout : ComputableInLogSpace rawOutput encEvent encUnary := ho.unaryAdd hj
  have hin (d : Fin 2) : ComputableInLogSpace (fun p => rawPredecessor p d) encEvent encUnary :=
    hprev.unaryAdd ((hj.unaryAdd (ComputableInLogSpace.const 1)).unaryAdd
      (ComputableInLogSpace.const d.val))
  have hc := equalCheck_code_logspace orGate (inputs := checkInput) (out := checkOutput)
    hv (fun d => ((hin d).unaryMod hv).unaryToBinary) (hout.unaryMod hv)
  refine ((hi.unaryLt hm).ite hc (ComputableInLogSpace.const ([], []))).congr_fun ?_
  intro p
  simp only [Function.comp_apply, decide_eq_true_eq]
  split_ifs <;> rfl

private theorem origin_in_window (T : ℕ) : Cone.InWindow 1 T T 0 := by
  simp [Cone.InWindow, Cone.radius]

def observation (T : ℕ) : Fin (V T) :=
  Cone.stateIndex 1 1 T ⟨Fin.last T, Cone.encodeBit 1 1 T T 0 (origin_in_window T) 0⟩

private theorem observation_val (T : ℕ) : (observation T).val = Cone.offset 1 1 T T := by
  rw [observation, Cone.stateIndex_val]
  simp [Cone.encodeBit, Cone.siteIndex, Cone.radius, finProdFinEquiv]

def orLayout : UniformLayout 1 1 where
  events := M
  states := V
  response := circuit
  check := orCheck
  observe := observation
  eventsUniform := Cone.eventCount_logspace 1 1
  statesUniform := Cone.stateCount_logspace 1 1
  responseUniform := circuit_code_logspace
  checkUniform := orCheck_code_logspace
  observeUniform := ((Cone.offset_logspace 1 1).comp
    (ComputableInLogSpace.id.pair ComputableInLogSpace.id)).congr_fun observation_val
  eventCoefficient := 3
  eventDegree := 2
  eventBound := Cone.eventCount_polynomial 1 1
  responseConstant := 3
  responseFactor := 8
  responseDepth := circuit_depth_logarithmic
  checkDepth := 5
  checkBound := orCheck_depth

def orLayoutCorrect : orLayout.Correct orRule rule where
  event T := (Cone.eventIndex 1 1 T).symm
  state T := (Cone.stateIndex 1 1 T).symm
  response T u e := by
    funext t j
    exact circuit_correct T u e t j
  check := orCheck_correct

theorem value_eq_observation (T : ℕ) (x : Cone.Config 1) :
    orLayoutCorrect.value T (Cone.restrict 1 T 0 x) = ((orRule^[T]) x) 0 0 := by
  let b : StateBit (Width T) T := ⟨Fin.last T, Cone.encodeBit 1 1 T T 0 (origin_in_window T) 0⟩
  have hobs : orLayoutCorrect.state T (orLayout.observe T) = b :=
    (Cone.stateIndex 1 1 T).symm_apply_apply b
  let read (c : StateBit (Width T) T) :=
    actualTrajectory (Cone.transition 1 T orRule) (Cone.restrict 1 T 0 x) c.1 c.2
  calc
    orLayoutCorrect.value T (Cone.restrict 1 T 0 x) = read b := congrArg read hobs
    _ = ((orRule^[T]) x) 0 0 := by
      change actualTrajectory (Cone.transition 1 T orRule) (Cone.restrict 1 T 0 x)
        (Fin.last T) (Cone.encodeBit 1 1 T T 0 _ 0) = _
      have hlocal : Geometry.Local 1 orRule := applyNeighbors_local _
      rw [Cone.finiteTrajectory_eq_restrict_iterate hlocal _ x rfl]
      exact Cone.restrict_encodeBit ((orRule^[T]) x) 0 (origin_in_window T) 0

def rightHalf (T : ℕ) (i : Fin (T + 1)) : Fin (Width T 0) :=
  ⟨T + i.val, by
    have hi := i.isLt
    simp only [coneWidth, Nat.sub_zero, one_mul, mul_one]
    omega⟩

/-- Direct evaluation of the OR observation, independently of reconstruction. -/
def directOR (T : ℕ) (u : Layer (Width T) 0) : Bool :=
  decide (∃ i : Fin (T + 1), u (rightHalf T i) = true)

theorem value_eq_directOR (T : ℕ) (u : Layer (Width T) 0) :
    orLayoutCorrect.value T u = directOR T u := by
  let x := Cone.extend 1 T 0 u
  have hx : Cone.restrict 1 T 0 x = u := Cone.restrict_extend u
  rw [← hx, value_eq_observation]
  apply Bool.eq_iff_iff.mpr
  rw [orRule_iterate_true_iff, directOR, decide_eq_true_eq, hx]
  simp only [zero_add]
  constructor
  · rintro ⟨j, hlo, hhi, hj⟩
    let i : Fin (T + 1) := ⟨j.toNat, by omega⟩
    have hw : Cone.InWindow 1 T 0 j := by
      simp only [Cone.InWindow, Cone.radius, Nat.sub_zero, one_mul]
      omega
    have hidx : rightHalf T i = Cone.encodeBit 1 1 T 0 j hw 0 := by
      apply Fin.ext
      change T + j.toNat = 0 + 1 * (j + (1 * (T - 0) : ℕ)).toNat
      simp only [Nat.sub_zero, one_mul, zero_add]
      omega
    exact ⟨i, by simpa [x, Cone.extend, hw, hidx] using hj⟩
  · rintro ⟨i, hi⟩
    refine ⟨i.val, by omega, by have := i.isLt; omega, ?_⟩
    have hw : Cone.InWindow 1 T 0 (i.val : ℤ) := by
      have := i.isLt
      simp only [Cone.InWindow, Cone.radius, Nat.sub_zero, one_mul]
      omega
    have hidx : rightHalf T i = Cone.encodeBit 1 1 T 0 (i.val : ℤ) hw 0 := by
      apply Fin.ext
      change T + i.val = 0 + 1 * ((i.val : ℤ) + (1 * (T - 0) : ℕ)).toNat
      simp only [Nat.sub_zero, one_mul, zero_add]
      omega
    simpa [x, Cone.extend, hw, ← hidx] using hi

theorem orPredictor_correct (k T : ℕ) (u : Layer (Width T) 0) :
    let y := (orLayout.unknownPredictor k T).eval interpretation u
    (y 0 = true ↔ Sparse (UniformLayout.residual (R := 1) orRule rule T u) k) ∧
      y 1 = (y 0 && directOR T u) := by
  simpa only [value_eq_directOR] using orLayoutCorrect.unknown k T u

theorem orPrediction_mem_uniformNC_one (k : ℕ) :
    UniformLayout.coneLanguage (fun T u =>
      Sparse (UniformLayout.residual (R := 1) orRule rule T u) k) ∈ UniformNCLevel 1 ∧
    UniformLayout.coneLanguage (fun T u =>
      Sparse (UniformLayout.residual (R := 1) orRule rule T u) k ∧
      directOR T u = true) ∈ UniformNCLevel 1 := by
  simpa only [value_eq_directOR] using
    orLayoutCorrect.unknown_mem_uniformNC_one (by decide) (by decide) k

end PredictionDepth.SparseCorrections.Pascal
