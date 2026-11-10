import PredictionDepth.SparseCorrections.Compiler
import PredictionDepth.SparseCorrections.EnumerationCode

/-! Logspace-uniform NC¹ for fixed unknown budgets and logarithmic schedules. -/

namespace PredictionDepth.SparseCorrections

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity CodeLogspace Turing.MultiTapeTM

private theorem listBits_logspace {α : Type} {enc : α ↪ List Bool} {m : α → ℕ}
    {bit : α → ℕ → Bool} (hm : ComputableInLogSpace m enc encUnary)
    (hb : ComputableInLogSpace (fun p : α × ℕ => bit p.1 p.2)
      (encPair enc encUnary) encBool) :
    ComputableInLogSpace (fun a => List.ofFn (fun j : Fin (m a) => bit a j.val)) enc encBits := by
  have hword : ComputableInLogSpace (fun p : α × ℕ => [bit p.1 p.2])
      (encPair enc encUnary) encBits := hb.congr (fun _ => rfl)
  exact (LogspaceBatch.flatMap_range hm hword).congr_fun fun a => by
    rw [← List.map_eq_flatMap, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
    rfl

/-- The circuit interface for a fixed local system. The semantic contract
for these circuits is kept separate from their serialization. -/
structure UniformLayout (q R : ℕ) where
  events : ℕ → ℕ
  states : ℕ → ℕ
  response : ∀ T, Gates (events T + inputWidth q R T) (states T)
  check : ∀ T, Fin (events T) → Gates (states T) 1
  observe : ∀ T, Fin (states T)
  eventsUniform : ComputableInLogSpace events encUnary encUnary
  statesUniform : ComputableInLogSpace states encUnary encUnary
  responseUniform : ComputableInLogSpace (fun T => (response T).code) encUnary encCode
  checkUniform : ComputableInLogSpace
    (fun p : ℕ × ℕ => if h : p.2 < events p.1 then (check p.1 ⟨p.2, h⟩).code else ([], []))
    (encPair encUnary encUnary) encCode
  observeUniform : ComputableInLogSpace (fun T => (observe T).val) encUnary encUnary
  eventCoefficient : ℕ
  eventDegree : ℕ
  eventBound : ∀ T, events T + 1 ≤ eventCoefficient * (T + 1) ^ eventDegree
  responseConstant : ℕ
  responseFactor : ℕ
  responseDepth : ∀ T, (response T).depth ≤ responseConstant + responseFactor * Nat.clog 2 (T + 1)
  checkDepth : ℕ
  checkBound : ∀ T j, (check T j).depth ≤ checkDepth

namespace UniformLayout

variable {q R : ℕ}

def unknownPredictor (A : UniformLayout q R) (k T : ℕ) : Gates (inputWidth q R T) 2 :=
  compile (A.response T) (A.check T) (A.observe T) (unknownCandidates (A.events T) k)

theorem unknownPredictor_code_logspace (A : UniformLayout q R) (k : ℕ) :
    ComputableInLogSpace (fun T => (A.unknownPredictor k T).code) encUnary encCode := by
  let N (T : ℕ) := (A.events T + 1) ^ k
  have hN : ComputableInLogSpace N encUnary encUnary :=
    fixedPower_logspace (A.eventsUniform.unaryAdd (ComputableInLogSpace.const 1)) k
  have ht := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  have hpair := ComputableInLogSpace.fst (encPair encUnary encUnary) encUnary
  have hi := ComputableInLogSpace.snd (encPair encUnary encUnary) encUnary
  have hbit := digitBit_logspace ((A.eventsUniform.comp ht).comp hpair) (hj.comp hpair) hi k
  have h := ((hj.comp hpair).unaryLt ((hN.comp ht).comp hpair)).bool_and hbit
  apply compile_code_logspace (inputWidth_logspace q R) A.eventsUniform A.statesUniform hN
    A.responseUniform A.checkUniform A.observeUniform
  refine (listBits_logspace
    (bit := fun p i => decide (p.2 < N p.1) && unknownBit (A.events p.1) k p.2 i)
    (A.eventsUniform.comp ht) h).congr_fun ?_
  intro p
  congr 1
  funext i
  by_cases hn : p.2 < N p.1 <;> simp [N, hn, unknownCandidates, unknownBit]

private theorem clog_bound {m T C d : ℕ} (h : m ≤ C * (T + 1) ^ d) :
    Nat.clog 2 m ≤ Nat.clog 2 C + d * Nat.clog 2 (T + 1) := by
  have hmul := clog_mul_bound (by decide : 1 < (2 : ℕ)) C ((T + 1) ^ d)
  have hpow := clog_power_bound (b := 2) (n := T + 1) (by decide) d
  exact (Nat.clog_mono_right 2 h).trans (hmul.trans (Nat.add_le_add_left hpow _))

theorem unknownLanguage_mem_uniformNC_one (A : UniformLayout q R) (k : ℕ) (lane : Fin 2) :
    lengthLanguage (A.unknownPredictor k) lane ∈ UniformNCLevel 1 := by
  apply lengthLanguage_mem_uniformNC_one _ _ (A.unknownPredictor_code_logspace k)
    (A.responseConstant + A.checkDepth + 6 + (2 + 2 * k) * Nat.clog 2 A.eventCoefficient)
    (A.responseFactor + (2 + 2 * k) * A.eventDegree)
  intro T
  have hb := clog_bound (A.eventBound T)
  have hm := Nat.clog_mono_right 2 (Nat.le_succ (A.events T))
  have hp := clog_power_bound (b := 2) (n := A.events T + 1) (by decide) k
  have hd := compile_depth (A.response T) (A.check T) (A.observe T)
    (unknownCandidates (A.events T) k) (A.checkBound T)
  unfold unknownPredictor
  exact hd.trans (by nlinarith [A.responseDepth T])

/-- Addresses are given independently of the input bits. The total worker
is used only at slots below the listed count. -/
structure Schedule (A : UniformLayout q R) where
  count : ℕ → ℕ
  address : ℕ × ℕ → ℕ
  inRange : ∀ T j, j < count T → address (T, j) < A.events T
  countUniform : ComputableInLogSpace count encUnary encUnary
  addressUniform : ComputableInLogSpace address (encPair encUnary encUnary) encUnary
  logConstant : ℕ
  logFactor : ℕ
  countBound : ∀ T, count T ≤ logConstant + logFactor * Nat.log 2 (T + 1)

def Schedule.slot {A : UniformLayout q R} (J : Schedule A) (T : ℕ) (i : Fin (J.count T)) :
    Fin (A.events T) :=
  ⟨J.address (T, i.val), J.inRange T i.val i.isLt⟩

def scheduledPredictor (A : UniformLayout q R) (J : Schedule A) (T : ℕ) :
    Gates (inputWidth q R T) 2 :=
  compile (A.response T) (A.check T) (A.observe T) (scheduledCandidates (J.slot T))

private theorem Schedule.clock {A : UniformLayout q R} (J : Schedule A) (T : ℕ) :
    2 ^ J.count T ≤ 2 ^ J.logConstant * (T + 1) ^ J.logFactor := by
  calc
    2 ^ J.count T ≤ 2 ^ (J.logConstant + J.logFactor * Nat.log 2 (T + 1)) :=
      Nat.pow_le_pow_right (by decide) (J.countBound T)
    _ = 2 ^ J.logConstant * (2 ^ Nat.log 2 (T + 1)) ^ J.logFactor := by
      rw [pow_add, Nat.mul_comm J.logFactor, pow_mul]
    _ ≤ 2 ^ J.logConstant * (T + 1) ^ J.logFactor :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) _)

theorem scheduledPredictor_code_logspace (A : UniformLayout q R) (J : Schedule A) :
    ComputableInLogSpace (fun T => (A.scheduledPredictor J T).code) encUnary encCode := by
  let N (T : ℕ) := 2 ^ J.count T
  have hid : ComputableInLogSpace (fun T : ℕ => T) encUnary encUnary := ComputableInLogSpace.id
  have hB := (ComputableInLogSpace.const (2 ^ J.logConstant)).unaryMul
    (fixedPower_logspace (hid.unaryAdd (ComputableInLogSpace.const 1)) J.logFactor)
  have hN : ComputableInLogSpace N encUnary encUnary :=
    scheduledCount_logspace J.countUniform hB J.clock
  have ht := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  have hpair := ComputableInLogSpace.fst (encPair encUnary encUnary) encUnary
  have hi := ComputableInLogSpace.snd (encPair encUnary encUnary) encUnary
  let e := encPair (encPair encUnary encUnary) encUnary
  have ht' := ht.comp hpair
  have hs := J.addressUniform.comp
    ((ht'.comp (ComputableInLogSpace.fst e encUnary)).pair
      (ComputableInLogSpace.snd e encUnary))
  have hbit := scheduledBit_logspace (J.countUniform.comp ht') (hj.comp hpair) hi hs
  have h := ((hj.comp hpair).unaryLt (hN.comp ht')).bool_and hbit
  apply compile_code_logspace (inputWidth_logspace q R) A.eventsUniform A.statesUniform hN
    A.responseUniform A.checkUniform A.observeUniform
  refine (listBits_logspace
    (bit := fun p i => decide (p.2 < N p.1) &&
      (List.range (J.count p.1)).any (fun j => (J.address (p.1, j) == i) && p.2.testBit j))
    (A.eventsUniform.comp ht) h).congr_fun ?_
  intro p
  congr 1
  funext i
  dsimp only [N, Function.comp_apply]
  by_cases hn : p.2 < 2 ^ J.count p.1
  · rw [dite_eq_left hn]
    simp only [hn, decide_true, Bool.true_and, scheduledCandidates]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, List.any_eq_true, List.mem_range, Bool.and_eq_true,
      beq_iff_eq, Schedule.slot, Fin.ext_iff]
    exact ⟨fun ⟨j, hji, hb⟩ => ⟨j.val, j.isLt, hji, hb⟩,
      fun ⟨j, hj, hji, hb⟩ => ⟨⟨j, hj⟩, hji, hb⟩⟩
  · simp [hn]

theorem scheduledLanguage_mem_uniformNC_one (A : UniformLayout q R) (J : Schedule A) (lane : Fin 2) :
    lengthLanguage (A.scheduledPredictor J) lane ∈ UniformNCLevel 1 := by
  apply lengthLanguage_mem_uniformNC_one _ _ (A.scheduledPredictor_code_logspace J)
    (A.responseConstant + A.checkDepth + 6 + 2 * Nat.clog 2 A.eventCoefficient + 2 * J.logConstant)
    (A.responseFactor + 2 * A.eventDegree + 2 * J.logFactor)
  intro T
  have hb := clog_bound (A.eventBound T)
  have hm := Nat.clog_mono_right 2 (Nat.le_succ (A.events T))
  have hj := (J.countBound T).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left J.logFactor (Nat.log_le_clog 2 (T + 1))) _)
  have hd := compile_depth (A.response T) (A.check T) (A.observe T)
    (scheduledCandidates (J.slot T)) (A.checkBound T)
  rw [Nat.clog_pow _ _ (by decide)] at hd
  unfold scheduledPredictor
  exact hd.trans (by nlinarith [A.responseDepth T])

end UniformLayout
end PredictionDepth.SparseCorrections
