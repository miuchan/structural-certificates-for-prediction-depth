import PredictionDepth.FrozenPascal.UniformClassification
import PredictionDepth.Complexity.PredictionReduction

/-! Uniformly translating controls can be frozen again by reflecting a moving
frame. Stays and hops exchange roles, with an offset of one between the
control and data tracks. -/

namespace PredictionDepth.TransportedBranching

open FrozenPascal
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition StandardComplexity Turing.MultiTapeTM

/-- Move controls one site per step and keep the two-branch data rule. -/
def step {Q : Type*} (stay hop : Q → Bool) (x : Config Q) : Config Q :=
  (fun i => x.1 (i + 1), (FrozenPascal.step stay hop x).2)

/-- Reflect around `origin`, offsetting the controls by one site. -/
def reverseFrame {Q : Type*} (origin : ℤ) (x : Config Q) : Config Q :=
  (fun i => x.1 (origin - i - 1), fun i => x.2 (origin - i))

theorem reverseFrame_step {Q : Type*} (stay hop : Q → Bool) (x : Config Q) (origin : ℤ) :
    reverseFrame origin (step stay hop x) =
      FrozenPascal.step hop stay (reverseFrame (origin + 1) x) := by
  have h (i : ℤ) : origin + 1 - i - 1 = origin - i := by omega
  have h' (i : ℤ) : origin + 1 - (i + 1) = origin - i := by omega
  apply Prod.ext <;> funext i
  · simp [reverseFrame, step, FrozenPascal.step, h]
  · simp [reverseFrame, step, FrozenPascal.step, h, h', show origin + 1 - i = origin - i + 1 by omega,
      add_comm]

/-- A transported iterate is a frozen iterate in the reflected frame, with
the two guards exchanged. -/
theorem reverseFrame_iterate {Q : Type*} (stay hop : Q → Bool) (T : ℕ)
    (x : Config Q) (origin : ℤ) :
    reverseFrame origin ((step stay hop)^[T] x) =
      (FrozenPascal.step hop stay)^[T] (reverseFrame (origin + T) x) := by
  induction T generalizing origin with
  | zero => simp
  | succ T ih =>
    rw [Function.iterate_succ_apply', reverseFrame_step, ih, Function.iterate_succ_apply']
    congr 3
    omega

/-- No control at the far endpoint of the window can be read within `T` updates. -/
private theorem frozen_window {Q : Type*} (stay hop : Q → Bool) (T : ℕ)
    (x y : Config Q) (i : ℤ)
    (hc : ∀ j : ℤ, i ≤ j → j < i + T → x.1 j = y.1 j)
    (hd : ∀ j : ℤ, i ≤ j → j ≤ i + T → x.2 j = y.2 j) :
    ((FrozenPascal.step stay hop)^[T] x).2 i =
      ((FrozenPascal.step stay hop)^[T] y).2 i := by
  induction T generalizing i with
  | zero => exact hd i (by omega) (by omega)
  | succ T ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [FrozenPascal.step, iterate_control]
    rw [hc i (by omega) (by omega),
      ih i (fun j h₁ h₂ => hc j h₁ (by omega)) (fun j h₁ h₂ => hd j h₁ (by omega)),
      ih (i + 1) (fun j h₁ h₂ => hc j (by omega) (by omega))
        (fun j h₁ h₂ => hd j (by omega) (by omega))]

/-- Reflect the data window and reflect the first `T` control words with the
one-site offset. The unused final control is wired to site zero. -/
def reverseWire {q : ℕ} (T : ℕ) : Fin (RawWidth q (T + 1)) → Fin (RawWidth q (T + 1)) :=
  Fin.addCases
    (fun k =>
      let p := (finProdFinEquiv : Fin (T + 1) × Fin q ≃ Fin ((T + 1) * q)).symm k
      controlWire ⟨T - 1 - p.1.val, by omega⟩ p.2)
    (fun k => rawDataWire k.rev)

/-- Use the classified frozen predictor with exchanged guards and the reversed
window wiring. -/
def prediction {q : ℕ} (stay hop : Gates q 1) (T : ℕ) : Gates (RawWidth q (T + 1)) 1 :=
  (classifiedPrediction hop stay T).comp (Circuit.wiring signature (reverseWire T))

theorem prediction_correct {q : ℕ} (stay hop : Gates q 1) (T : ℕ) (x : Config (Bits q)) :
    (prediction stay hop T).eval interpretation (rawSample x (T + 1)) 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
  let input := rawSample x (T + 1) ∘ reverseWire T
  rw [prediction, Circuit.eval_comp, Circuit.eval_wiring]
  change (classifiedPrediction hop stay T).eval interpretation input 0 = _
  rw [← rawSample_decodeRaw input, classifiedPrediction_correct]
  have he := congrArg (fun y : Config (Bits q) => y.2 0)
    (reverseFrame_iterate (guard stay) (guard hop) T x 0)
  simp only [reverseFrame, sub_zero, zero_add] at he
  rw [he]
  congr 1
  apply frozen_window
  · intro j hj hT
    let k : Fin (T + 1) := ⟨j.toNat, by omega⟩
    have hk : (k.val : ℤ) = j := Int.toNat_of_nonneg hj
    funext b
    rw [← hk, ← rawSample_control (decodeRaw input) k, rawSample_decodeRaw]
    simp only [input, Function.comp_apply, reverseWire, controlWire,
      Fin.addCases_left, Equiv.symm_apply_apply]
    rw [← controlWire, rawSample_control]
    have hi : ((T - 1 - k.val : ℕ) : ℤ) = (T : ℤ) - k.val - 1 := by
      rw [Int.ofNat_sub (show k.val ≤ T - 1 by omega), Int.ofNat_sub (show 1 ≤ T by omega)]
      omega
    exact congrArg (fun i : ℤ => x.1 i b) hi
  · intro j hj hT
    let k : Fin (T + 1) := ⟨j.toNat, by omega⟩
    have hk : (k.val : ℤ) = j := Int.toNat_of_nonneg hj
    apply (Equiv.injective ofBoolRing)
    rw [← hk, ← rawSample_data (decodeRaw input) k, rawSample_decodeRaw]
    simp only [input, Function.comp_apply, reverseWire, rawDataWire, Fin.addCases_right]
    rw [← rawDataWire, rawSample_data]
    congr 2
    have hrev : k.rev.val = T - k.val := by simp [Fin.rev]
    rw [hrev, Int.ofNat_sub (by omega)]

theorem prediction_depth {q : ℕ} (stay hop : Gates q 1) (T : ℕ) :
    (prediction stay hop T).depth ≤ (classifiedPrediction hop stay T).depth :=
  (Circuit.depth_comp_le _ _).trans (by simp)

theorem prediction_size {q : ℕ} (stay hop : Gates q 1) (T : ℕ) :
    (prediction stay hop T).size = (classifiedPrediction hop stay T).size := by
  simp [prediction]

/-- Observation on every finite window, interpreted by the existing extension. -/
def transportedObservation {q : ℕ} (stay hop : Gates q 1) :
    WindowPrediction (fun T => RawWidth q (T + 1)) (fun _ => 1) :=
  fun T x _ => ofBoolRing (((step (guard stay) (guard hop))^[T] (decodeRaw x)).2 0)

def frozenObservation {q : ℕ} (stay hop : Gates q 1) :
    WindowPrediction (fun T => RawWidth q (T + 1)) (fun _ => 1) :=
  fun T x _ => ofBoolRing (((FrozenPascal.step (guard stay) (guard hop))^[T] (decodeRaw x)).2 0)

/-- The reflected frame is a reduction to the frozen observation with exchanged
guards. It does not require the rewire to be a permutation. -/
def reduction {q : ℕ} (stay hop : Gates q 1) :
    PredictionReduction (transportedObservation stay hop) (frozenObservation hop stay) where
  targetTime := id
  encodeInput T := Circuit.wiring signature (reverseWire T)
  decodeOutput _ := Circuit.wiring signature id
  correct := by
    intro T x
    funext i
    rw [show i = 0 from Subsingleton.elim _ _]
    change frozenObservation hop stay T (x ∘ reverseWire T) 0 = transportedObservation stay hop T x 0
    have h := prediction_correct stay hop T (decodeRaw x)
    rw [rawSample_decodeRaw, prediction, Circuit.eval_comp, Circuit.eval_wiring,
      ← rawSample_decodeRaw (x ∘ reverseWire T), classifiedPrediction_correct] at h
    exact h

theorem reduction_compile_eq_prediction {q : ℕ} (stay hop : Gates q 1) (T : ℕ) :
    (reduction stay hop).compile T (classifiedPrediction hop stay T) = prediction stay hop T := by
  change (Circuit.wiring signature id).comp (prediction stay hop T) = prediction stay hop T
  apply Circuit.code_injective
  rw [← compCode_code, Circuit.code_wiring_id]
  simp [compCode, compCodeWire, Circuit.code, List.ofFn_succ]

private def reverseReference (q : ℕ) (p : ℕ × ℕ) : ℕ :=
  let span := (p.1 + 1) * q
  if p.2 < span then (p.1 - 1 - p.2 / q) * q + p.2 % q
  else span + (p.1 - (p.2 - span))

private theorem reverseWire_val (q T : ℕ) (i : Fin (RawWidth q (T + 1))) :
    (reverseWire T i).val = reverseReference q (T, i.val) := by
  induction i using Fin.addCases with
  | left i =>
    simp only [reverseWire, Fin.addCases_left, reverseReference, Fin.val_castAdd, i.isLt, ite_true]
    simp [controlWire, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  | right i =>
    have hi : ¬ (T + 1) * q + i.val < (T + 1) * q := by omega
    simp [reverseWire, reverseReference, rawDataWire, Fin.rev, hi]

theorem reverseWiring_code_logspace (q : ℕ) :
    ComputableInLogSpace (fun T => (Circuit.wiring signature (reverseWire (q := q) T)).code)
      encUnary encCode := by
  have ht := ComputableInLogSpace.fst encUnary encUnary
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have hspan := (ht.unaryAdd (ComputableInLogSpace.const 1)).unaryMulConst q
  have hleft := ((ht.unarySub (ComputableInLogSpace.const 1)).unarySub
    (hi.unaryDiv (ComputableInLogSpace.const q))).unaryMulConst q
  have hl := hleft.unaryAdd (hi.unaryMod (ComputableInLogSpace.const q))
  have hr := hspan.unaryAdd (ht.unarySub (hi.unarySub hspan))
  have hg : ComputableInLogSpace (reverseReference q) (encPair encUnary encUnary) encNat :=
    ((hi.unaryLt hspan).ite hl.unaryToBinary hr.unaryToBinary).congr_fun (fun _ => by
      simp only [reverseReference, decide_eq_true_eq])
  exact UniformWeight.wiring_logspace (UniformGuards.rawWidth_succ_logspace q) hg (reverseWire_val q)

theorem prediction_code_logspace {q : ℕ} (stay hop : Gates q 1) :
    ComputableInLogSpace (fun T => (prediction stay hop T).code) encUnary encCode := by
  have hr := (reduction stay hop).compile_code_logspace (UniformGuards.rawWidth_succ_logspace q)
    ComputableInLogSpace.id (reverseWiring_code_logspace q)
    (ComputableInLogSpace.const ((Circuit.wiring signature (id : Fin 1 → Fin 1)).code))
    (classifiedPrediction_code_logspace hop stay)
  exact hr.congr_fun fun T => congrArg Circuit.code (reduction_compile_eq_prediction stay hop T).symm

theorem prediction_uniform {q : ℕ} (stay hop : Gates q 1) :
    LogspaceUniform (UniformGuards.lift (prediction stay hop)) :=
  UniformGuards.lift_uniform (prediction stay hop) (prediction_code_logspace stay hop)

end PredictionDepth.TransportedBranching
