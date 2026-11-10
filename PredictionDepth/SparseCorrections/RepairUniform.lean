import PredictionDepth.SparseCorrections.Uniform
import PredictionDepth.SparseCorrections.LayerChecks
import PredictionDepth.SparseCorrections.RepairCode

/-! Uniform chronological repair for bit budgets and update-layer budgets. -/

namespace PredictionDepth.SparseCorrections.RepairUniform

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity Turing.MultiTapeTM
open FrozenPascal (negateBank notGate wireBit)

/-- The event partition and circuit for identifying failed blocks, with
generators for both the aggregate circuit and its event-to-block addresses. -/
structure UniformBlocks (events : ℕ → ℕ) where
  count : ℕ → ℕ
  failFlags : ∀ T, Gates (events T) (count T)
  block : ∀ T, Fin (events T) → Fin (count T)
  countUniform : ComputableInLogSpace count encUnary encUnary
  flagsUniform : ComputableInLogSpace (fun T => (failFlags T).code) encUnary encCode
  blockAddress : ℕ × ℕ → ℕ
  addressUniform : ComputableInLogSpace blockAddress (encPair encUnary encUnary) encUnary
  address_eq : ∀ T j, (block T j).val = blockAddress (T, j.val)
  depthConstant : ℕ
  depthFactor : ℕ
  depthBound : ∀ T, (failFlags T).depth + 2 * Nat.clog 2 (count T) ≤
    depthConstant + depthFactor * Nat.clog 2 (T + 1)

private theorem clog_le_polynomial {m T C d : ℕ} (h : m ≤ C * (T + 1) ^ d) :
    Nat.clog 2 m ≤ (Nat.clog 2 C + d) * (Nat.clog 2 (T + 1) + 1) := by
  have hl := (Nat.log_le_clog 2 T).trans (Nat.clog_mono_right 2 (Nat.le_succ T))
  exact (clog_of_polynomial_bound h).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hl 1))

private theorem negateBank_depth (m : ℕ) : (negateBank m).depth ≤ 1 := by
  apply Circuit.depth_pi_le
  intro j
  exact (Circuit.depth_comp_le notGate (wireBit j)).trans (by simp [notGate])

/-- One repair block per residual bit. -/
def UniformBlocks.bits {q R : ℕ} (A : UniformLayout q R) : UniformBlocks A.events where
  count := A.events
  failFlags := fun T => negateBank (A.events T)
  block := fun _ j => j
  countUniform := A.eventsUniform
  flagsUniform := RepairCircuit.negateBank_code_logspace.comp A.eventsUniform
  blockAddress := Prod.snd
  addressUniform := ComputableInLogSpace.snd encUnary encUnary
  address_eq := fun _ _ => rfl
  depthConstant := 1 + 2 * (Nat.clog 2 A.eventCoefficient + A.eventDegree)
  depthFactor := 2 * (Nat.clog 2 A.eventCoefficient + A.eventDegree)
  depthBound := by
    intro T
    have hm := clog_le_polynomial ((Nat.le_succ _).trans (A.eventBound T))
    have hn := negateBank_depth (A.events T)
    simp only [Nat.mul_add, Nat.mul_one] at hm
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at *
    omega

@[simp] theorem UniformBlocks.bits_failFlags_eval {q R : ℕ} (A : UniformLayout q R)
    (T : ℕ) (p : Fin (A.events T) → Bool) (j : Fin (A.events T)) :
    ((UniformBlocks.bits A).failFlags T).eval interpretation p j = !p j := by
  simp [UniformBlocks.bits, negateBank, notGate, interpretation]

/-- One repair block per update layer in the dense cone layout. -/
def UniformBlocks.layers (q R : ℕ) : UniformBlocks (Cone.eventCount q R) where
  count := id
  failFlags := LayerChecks.failFlags q R
  block := LayerChecks.eventBlock q R
  countUniform := ComputableInLogSpace.id
  flagsUniform := LayerChecks.failFlags_code_logspace q R
  blockAddress := LayerChecks.blockAddress q R
  addressUniform := LayerChecks.blockAddress_logspace q R
  address_eq := fun T j => (LayerChecks.blockAddress_eq q R T j).symm
  depthConstant := 2 * (Nat.clog 2 (q * (R + 1) + 1) + 2) + 3
  depthFactor := 2 * (Nat.clog 2 (q * (R + 1) + 1) + 2) + 2
  depthBound := by
    intro T
    have hm := clog_le_polynomial ((Nat.le_succ _).trans (Cone.eventCount_polynomial q R T))
    have ht : Nat.clog 2 T ≤ Nat.clog 2 (T + 1) :=
      Nat.clog_mono_right 2 (Nat.le_succ T)
    have hb := LayerChecks.failFlags_depth q R T
    simp only [id_eq, Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.mul_assoc] at *
    omega

variable {q R : ℕ}

def predictor (A : UniformLayout q R) (B : UniformBlocks A.events)
    (budget : ℕ → ℕ) (T : ℕ) : Gates (inputWidth q R T) 2 :=
  RepairCircuit.compile (A.response T) (A.check T) (B.failFlags T) (B.block T)
    (A.observe T) (budget T)

theorem predictor_code_logspace (A : UniformLayout q R) (B : UniformBlocks A.events)
    {budget : ℕ → ℕ} (hbudget : ComputableInLogSpace budget encUnary encUnary) :
    ComputableInLogSpace (fun T => (predictor A B budget T).code) encUnary encCode :=
  RepairCircuit.compile_code_logspace (inputWidth_logspace q R) A.eventsUniform A.statesUniform
    B.countUniform hbudget A.responseUniform A.checkUniform B.flagsUniform B.addressUniform
    B.address_eq A.observeUniform

/-- The number of rounds multiplies a logarithmic bound for a round and for
the final verifier. The constants depend only on the fixed layout. -/
theorem predictor_depth (A : UniformLayout q R) (B : UniformBlocks A.events) :
    ∃ C K, ∀ (budget : ℕ → ℕ) (T : ℕ),
      (predictor A B budget T).depth ≤ (budget T + 1) * (C + K * Nat.clog 2 (T + 1)) := by
  let a := Nat.clog 2 A.eventCoefficient + A.eventDegree
  let C := A.responseConstant + A.checkDepth + B.depthConstant + 2 * a + 10
  let K := A.responseFactor + B.depthFactor + 2 * a
  refine ⟨C, K, fun budget T => ?_⟩
  let l := Nat.clog 2 (T + 1)
  have he : Nat.clog 2 (A.events T) ≤ a * (l + 1) :=
    clog_le_polynomial ((Nat.le_succ _).trans (A.eventBound T))
  have hr := A.responseDepth T
  have hb := B.depthBound T
  change (A.response T).depth ≤ A.responseConstant + A.responseFactor * l at hr
  change (B.failFlags T).depth + 2 * Nat.clog 2 (B.count T) ≤
    B.depthConstant + B.depthFactor * l at hb
  have hs : (A.response T).depth + A.checkDepth + (B.failFlags T).depth +
      2 * Nat.clog 2 (B.count T) + 10 ≤ C + K * l := by
    dsimp only [C, K]
    simp only [Nat.add_mul] at *
    omega
  have hf : (A.response T).depth + A.checkDepth + 2 * Nat.clog 2 (A.events T) + 5 ≤
      C + K * l := by
    dsimp only [C, K]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at *
    omega
  have hc := RepairCircuit.compile_depth (A.response T) (A.check T) (B.failFlags T) (B.block T)
    (A.observe T) (budget T) (A.checkBound T)
  have ht := Nat.add_le_add (Nat.mul_le_mul_left (budget T) hs) hf
  exact hc.trans (by simpa only [Nat.add_mul, Nat.one_mul] using ht)

/-- Both output lanes give uniform NC¹ languages at a fixed round budget. -/
theorem fixedLanguage_mem_uniformNC_one (A : UniformLayout q R) (B : UniformBlocks A.events)
    (k : ℕ) (lane : Fin 2) :
    lengthLanguage (predictor A B (fun _ => k)) lane ∈ UniformNCLevel 1 := by
  obtain ⟨C, K, hd⟩ := predictor_depth A B
  apply lengthLanguage_mem_uniformNC_one _ lane
    (predictor_code_logspace A B (ComputableInLogSpace.const k)) ((k + 1) * C) ((k + 1) * K)
  intro T
  simpa only [Nat.mul_add, ← Nat.mul_assoc] using hd (fun _ => k) T

/-- An indexed logarithmic round budget gives uniform NC² for either output. -/
theorem logLanguage_mem_uniformNC_two (A : UniformLayout q R) (B : UniformBlocks A.events)
    (budget : ℕ → ℕ) (hbudgetUniform : ComputableInLogSpace budget encUnary encUnary)
    (C K : ℕ) (hbudget : ∀ T, budget T ≤ C + K * Nat.clog 2 (T + 1)) (lane : Fin 2) :
    lengthLanguage (predictor A B budget) lane ∈ UniformNCLevel 2 := by
  obtain ⟨D, F, hd⟩ := predictor_depth A B
  apply lengthLanguage_mem_uniformNCLevel _ lane (predictor_code_logspace A B hbudgetUniform)
    2 ((C + 1) * D) ((C + 1) * F + K * D + K * F)
  intro T
  let l := Nat.clog 2 (T + 1)
  have hle : l ≤ l ^ 2 := by
    cases l with
    | zero => decide
    | succ l =>
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ (Nat.succ_pos l)
  have hk : budget T + 1 ≤ C + 1 + K * l := by
    have h : budget T ≤ C + K * l := hbudget T
    omega
  calc
    (predictor A B budget T).depth ≤ (budget T + 1) * (D + F * l) := hd budget T
    _ ≤ (C + 1 + K * l) * (D + F * l) := Nat.mul_le_mul_right _ hk
    _ = (C + 1) * D + (((C + 1) * F + K * D) * l + K * F * l ^ 2) := by ring
    _ ≤ (C + 1) * D + ((C + 1) * F + K * D + K * F) * l ^ 2 := by
      rw [Nat.add_mul ((C + 1) * F + K * D) (K * F) (l ^ 2)]
      exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left _ hle) _) _

end PredictionDepth.SparseCorrections.RepairUniform
