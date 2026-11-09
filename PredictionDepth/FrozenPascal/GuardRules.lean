import PredictionDepth.FrozenPascal.PathWitness
import PredictionDepth.FrozenPascal.Window

/-!
# The rule family on raw control words

Each cell has a fixed-size Boolean control word and one evolving data bit.
Any two fixed Boolean circuits on a control word can select the stay and hop
coefficients. The predictor evaluates them in parallel across the input
window before applying the frozen-control path construction.
-/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open Linear (F₂)
open scoped BigOperators

abbrev RawWidth (q m : ℕ) := m * q + m

def controlWire (i : Fin m) (j : Fin q) : Fin (RawWidth q m) :=
  Fin.castAdd m (finProdFinEquiv (i, j))

def rawDataWire {q : ℕ} (i : Fin m) : Fin (RawWidth q m) := Fin.natAdd (m * q) i

def rawSample (x : Config (Bits q)) (m : ℕ) : Bits (RawWidth q m) :=
  joinBits (fun i : Fin (m * q) => x.1 (finProdFinEquiv.symm i).1.val (finProdFinEquiv.symm i).2)
    (fun i : Fin m => ofBoolRing (x.2 i.val))

@[simp] theorem rawSample_control (x : Config (Bits q)) (i : Fin m) (j : Fin q) :
    rawSample x m (controlWire i j) = x.1 i.val j := by
  simp only [rawSample, controlWire, joinBits_left, Equiv.symm_apply_apply]

@[simp] theorem rawSample_data (x : Config (Bits q)) (i : Fin m) :
    rawSample x m (rawDataWire i) = ofBoolRing (x.2 i.val) := by
  simp only [rawSample, rawDataWire, joinBits_right]

/-- Extend a raw window by zero controls and data. The prediction theorems
already show that the choice of extension does not affect the answer. -/
def decodeRaw (x : Bits (RawWidth q m)) : Config (Bits q) :=
  (fun i j => extendTrack (fun k : Fin m => x (controlWire k j)) i,
    fun i => bit (extendTrack (x ∘ rawDataWire) i))

theorem rawSample_decodeRaw (x : Bits (RawWidth q m)) : rawSample (decodeRaw x) m = x := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · let p : Fin m × Fin q := finProdFinEquiv.symm i
    have hi : controlWire p.1 p.2 = Fin.castAdd m i := by
      change Fin.castAdd m (finProdFinEquiv p) = Fin.castAdd m i
      rw [show finProdFinEquiv p = i from Equiv.apply_symm_apply finProdFinEquiv i]
    rw [← hi, rawSample_control]
    exact extendTrack_fin (fun k : Fin m => x (controlWire k p.2)) p.1
  · change rawSample (decodeRaw x) m (rawDataWire i) = x (rawDataWire i)
    rw [rawSample_data]
    change ofBoolRing (bit (extendTrack (x ∘ rawDataWire) (i.val : ℤ))) = _
    rw [extendTrack_fin]
    change ofBoolRing (bit (x (rawDataWire i))) = x (rawDataWire i)
    cases x (rawDataWire i) <;> rfl

def guard (c : Gates q 1) (a : Bits q) : Bool := c.eval interpretation a 0

def guardBank (c : Gates q 1) (m : ℕ) : Gates (RawWidth q m) m :=
  Circuit.pi fun i => c.comp (Circuit.wiring signature (controlWire i))

theorem guardBank_eval (c : Gates q 1) (x : Config (Bits q)) (m : ℕ) :
    (guardBank c m).eval interpretation (rawSample x m) =
      fun i : Fin m => guard c (x.1 i.val) := by
  funext i
  simp only [guardBank, Circuit.eval_pi, Circuit.eval_comp, Circuit.eval_wiring, guard]
  have he : rawSample x m ∘ controlWire i = x.1 i.val := by
    funext j
    exact rawSample_control x i j
  rw [he]

def preprocess (stay hop : Gates q 1) (m : ℕ) : Gates (RawWidth q m) (InputWidth m) :=
  (guardBank stay m).append ((guardBank hop m).append (Circuit.wiring signature rawDataWire))

theorem preprocess_eval (stay hop : Gates q 1) (x : Config (Bits q)) (m : ℕ) :
    (preprocess stay hop m).eval interpretation (rawSample x m) = sample (guard stay) (guard hop) x m := by
  rw [preprocess, Circuit.eval_append, Circuit.eval_append, guardBank_eval, guardBank_eval,
    Circuit.eval_wiring]
  have hd : rawSample x m ∘ rawDataWire = fun i : Fin m => ofBoolRing (x.2 i.val) := by
    funext i
    exact rawSample_data x i
  rw [hd]
  rfl

theorem guardBank_depth (c : Gates q 1) (m : ℕ) : (guardBank c m).depth ≤ c.depth := by
  apply Circuit.depth_pi_le
  intro i
  exact (Circuit.depth_comp_le _ _).trans (by simp)

theorem guardBank_size (c : Gates q 1) (m : ℕ) : (guardBank c m).size = m * c.size := by
  simp [guardBank]

theorem preprocess_depth (stay hop : Gates q 1) (m : ℕ) :
    (preprocess stay hop m).depth ≤ max stay.depth hop.depth := by
  apply (Circuit.depth_append_le _ _).trans
  apply max_le
  · exact (guardBank_depth stay m).trans (le_max_left _ _)
  · apply (Circuit.depth_append_le _ _).trans
    exact max_le ((guardBank_depth hop m).trans (le_max_right _ _)) (by simp)

theorem preprocess_size (stay hop : Gates q 1) (m : ℕ) :
    (preprocess stay hop m).size = m * (stay.size + hop.size) := by
  simp [preprocess, guardBank_size, Nat.mul_add]

/-- Exact finite-time prediction for the raw inputs of any fixed pair of guards. -/
def guardedPrediction (stay hop : Gates q 1) (T : ℕ) : Gates (RawWidth q (T + 1)) 1 :=
  (predictionCircuit T).comp (preprocess stay hop (T + 1))

theorem guardedPrediction_correct (stay hop : Gates q 1) (x : Config (Bits q)) (T : ℕ) :
    (guardedPrediction stay hop T).eval interpretation (rawSample x (T + 1)) 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
  rw [guardedPrediction, Circuit.eval_comp, preprocess_eval, predictionCircuit_correct, observe,
    sample_prediction (guard stay) (guard hop) x (Nat.lt_succ_self T)]

theorem guardedPrediction_depth (stay hop : Gates q 1) (T : ℕ) :
    (guardedPrediction stay hop T).depth ≤
      7 + 33 * Nat.clog 2 (T + 2) + max stay.depth hop.depth :=
  (Circuit.depth_comp_le _ _).trans (Nat.add_le_add
    (predictionCircuit_depth T) (preprocess_depth stay hop (T + 1)))

theorem guardedPrediction_size (stay hop : Gates q 1) (T : ℕ) :
    (guardedPrediction stay hop T).size ≤
      113 * (T + 2) ^ 4 + (T + 1) * (stay.size + hop.size) := by
  rw [guardedPrediction, Circuit.size_comp, preprocess_size]
  exact Nat.add_le_add_left (predictionCircuit_size T) _ |>.trans_eq (Nat.add_comm _ _)

/-- Even allowing an arbitrary control-only offset, the local data rule
cannot be affine with fixed data coefficients when the stay guard varies. -/
theorem guarded_rule_nonaffine (stay hop : Gates q 1) (a b : Bits q)
    (ha : guard stay a = false) (hb : guard stay b = true) :
    ¬ ∃ (g : Bits q → F₂) (c d : F₂), ∀ a v u,
      bit (guard stay a) * v + bit (guard hop a) * u = g a + c * v + d * u := by
  rintro ⟨g, c, d, h⟩
  apply nonaffine_local (guard stay) a b ha hb
  exact ⟨g, c, fun a v => by simpa using h a v 0⟩

end PredictionDepth.FrozenPascal
