import CslibFrontier.Computability.Circuit.Encoding.Layer
import CslibFrontier.Computability.Circuit.Boolean.DepthTime

/-!
# Regular layers as real serialized circuits

The constructor checks arity, predecessor bounds and output bounds. The depth
proof works directly on CSLib's sequential circuit-code evaluator, interpreted
over gate depths. A full stage is parallel even though its code is a list.
-/

namespace PredictionDepth.StandardComplexity.LayerCode
open Cslib.Circuits Cslib.Circuits.Boolean

abbrev Gate := Op × List ℕ

def layer (width : ℕ) (gate : ℕ → ℕ → Gate) (t : ℕ) : List Gate :=
  (List.range width).map (gate t)

def layers (width : ℕ) (gate : ℕ → ℕ → Gate) (steps : ℕ) : List Gate :=
  (List.range steps).flatMap (layer width gate)

@[simp] theorem layers_zero (width : ℕ) (gate : ℕ → ℕ → Gate) :
    layers width gate 0 = [] := rfl

theorem layers_succ (width : ℕ) (gate : ℕ → ℕ → Gate) (steps : ℕ) :
    layers width gate (steps + 1) = layers width gate steps ++ layer width gate steps := by
  simp [layers, List.range_succ]

@[simp] theorem layer_length (width : ℕ) (gate : ℕ → ℕ → Gate) (t : ℕ) :
    (layer width gate t).length = width := by simp [layer]

@[simp] theorem layers_length (width : ℕ) (gate : ℕ → ℕ → Gate) (steps : ℕ) :
    (layers width gate steps).length = steps * width := by
  induction steps with
  | zero => simp
  | succ steps ih => simp [layers_succ, ih, Nat.succ_mul]

/-- Gate-index arithmetic for the streaming serializer. -/
theorem layers_eq_map_range {width : ℕ} (hw : 0 < width) (gate : ℕ → ℕ → Gate)
    (steps : ℕ) :
    layers width gate steps =
      (List.range (steps * width)).map (fun q => gate (q / width) (q % width)) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [layers_succ, Nat.succ_mul, List.range_add, List.map_append, ← ih, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      have hj' : j < width := List.mem_range.mp hj
      simp only [Function.comp_apply]
      congr 1
      · rw [Nat.add_comm (steps * width) j, Nat.add_mul_div_right _ _ hw,
          Nat.div_eq_of_lt hj']
        omega
      · simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj']

/-- The local requirements on a parallel stage: every argument is a wire that
already exists before the stage starts. -/
def Valid (inputs width steps : ℕ) (gate : ℕ → ℕ → Gate) : Prop :=
  ∀ t < steps, ∀ j < width,
    (gate t j).2.length = signature.Arity (gate t j).1 ∧
      ∀ i ∈ (gate t j).2, i < inputs + t * width

theorem valid_prefix {n w T : ℕ} {gate : ℕ → ℕ → Gate}
    (h : Valid n w (T + 1) gate) : Valid n w T gate := by
  intro t ht j hj
  exact h t (by omega) j hj

theorem isCodeFrom {n w T : ℕ} {gate : ℕ → ℕ → Gate}
    (h : Valid n w T gate) : Program.IsCodeFrom signature n 0 (layers w gate T) := by
  induction T with
  | zero => trivial
  | succ T ih =>
      rw [layers_succ, Program.isCodeFrom_append]
      refine ⟨ih (valid_prefix h), ?_⟩
      simp only [layers_length, Nat.zero_add]
      apply Program.isCodeFrom_of_forall
      intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
      exact h T (by omega) j (List.mem_range.mp hj)

def code (width : ℕ) (gate : ℕ → ℕ → Gate) (steps : ℕ) (outputs : List ℕ) :=
  (layers width gate steps, outputs)

/-- Decode the verified finite gate table into an actual CSLib circuit. -/
def circuit {n w T m : ℕ} {gate : ℕ → ℕ → Gate} {outputs : List ℕ}
    (h : Valid n w T gate) (hm : outputs.length = m)
    (ho : ∀ i ∈ outputs, i < n + T * w) : Circuit signature n m :=
  (Circuit.ofCode n m (code w gate T outputs)).get
    (Circuit.isSome_ofCode_iff.mpr ⟨isCodeFrom h, hm, by simpa [code] using ho⟩)

theorem circuit_code {n w T m : ℕ} {gate : ℕ → ℕ → Gate} {outputs : List ℕ}
    (h : Valid n w T gate) (hm : outputs.length = m)
    (ho : ∀ i ∈ outputs, i < n + T * w) :
    (circuit h hm ho).code = code w gate T outputs :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

theorem circuit_size {n w T m : ℕ} {gate : ℕ → ℕ → Gate} {outputs : List ℕ}
    (h : Valid n w T gate) (hm : outputs.length = m)
    (ho : ∀ i ∈ outputs, i < n + T * w) : (circuit h hm ho).size = T * w := by
  rw [← Circuit.length_code_fst, circuit_code]
  exact layers_length w gate T

theorem evalCode_depth_le {n w T : ℕ} {gate : ℕ → ℕ → Gate}
    (h : Valid n w T gate) :
    ∀ v ∈ evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0)
      (layers w gate T), v ≤ T := by
  induction T with
  | zero =>
      intro v hv
      change v ∈ List.replicate n 0 at hv
      have := (List.mem_replicate.mp hv).2
      omega
  | succ T ih =>
      rw [layers_succ, evalCode_append]
      apply le_of_mem_evalCode_depth_layer
      · intro g hg i hi
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
        simpa only [length_evalCode, List.length_replicate, layers_length] using
          (h T (by omega) j (List.mem_range.mp hj)).2 i hi
      · exact ih (valid_prefix h)
      · intro g _
        exact le_rfl

theorem circuit_depth_le {n w T m : ℕ} {gate : ℕ → ℕ → Gate} {outputs : List ℕ}
    (h : Valid n w T gate) (hm : outputs.length = m)
    (ho : ∀ i ∈ outputs, i < n + T * w) : (circuit h hm ho).depth ≤ T := by
  rw [← Circuit.depthWith_one]
  apply Circuit.depthWith_le_of_evalCode
  rw [circuit_code]
  exact evalCode_depth_le h

end PredictionDepth.StandardComplexity.LayerCode
