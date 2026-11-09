import PredictionDepth.Complexity.UniformComposition.Chain
import PredictionDepth.Complexity.OutputNormalization

/-! Typed sequential composition and its native logspace generator. -/

namespace PredictionDepth.StandardComplexity.UniformComposition

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM CodeLogspace CodeLogspaceFamilies OutputNormalization

def circuitChain {n W : ℕ} (initial : Circuit signature n W)
    (steps : List (Circuit signature W W)) : Circuit signature n W :=
  steps.foldl (fun c s => s.comp c) initial

def normalizedChain {n W : ℕ} (initial : Circuit signature n W)
    (steps : List (Circuit signature W W)) : Circuit signature n W :=
  circuitChain (normalizeOutputs initial) (steps.map normalizeOutputs)

theorem circuitChain_code {n W : ℕ} (initial : Circuit signature n W)
    (steps : List (Circuit signature W W)) :
    (circuitChain initial steps).code = sequentialCodes n initial.code (steps.map Circuit.code) := by
  induction steps generalizing initial with
  | nil => rfl
  | cons s steps ih =>
    simpa only [circuitChain, sequentialCodes, List.foldl_cons, List.map_cons, compCode_code] using
      ih (s.comp initial)

theorem circuitChain_eval {n W : ℕ} (initial : Circuit signature n W)
    (steps : List (Circuit signature W W)) (x : Fin n → Bool) :
    (circuitChain initial steps).eval interpretation x =
      steps.foldl (fun v s => s.eval interpretation v) (initial.eval interpretation x) := by
  induction steps generalizing initial with
  | nil => rfl
  | cons s steps ih =>
    simpa only [circuitChain, List.foldl_cons, Circuit.eval_comp] using ih (s.comp initial)

theorem normalizedChain_eval {n W : ℕ} (initial : Circuit signature n W)
    (steps : List (Circuit signature W W)) (x : Fin n → Bool) :
    (normalizedChain initial steps).eval interpretation x =
      (circuitChain initial steps).eval interpretation x := by
  simp only [normalizedChain, circuitChain_eval, normalizeOutputs_eval, List.foldl_map]

theorem circuitChain_size {n W : ℕ} (initial : Circuit signature n W)
    (steps : List (Circuit signature W W)) :
    (circuitChain initial steps).size = initial.size + (steps.map Circuit.size).sum := by
  induction steps generalizing initial with
  | nil => simp [circuitChain]
  | cons s steps ih =>
    simpa only [circuitChain, List.foldl_cons, List.map_cons, List.sum_cons,
      Circuit.size_comp, Nat.add_assoc] using ih (s.comp initial)

theorem circuitChain_depth {n W : ℕ} (initial : Circuit signature n W)
    (steps : List (Circuit signature W W)) :
    (circuitChain initial steps).depth ≤ initial.depth + (steps.map Circuit.depth).sum := by
  induction steps generalizing initial with
  | nil => simp [circuitChain]
  | cons s steps ih =>
    change (circuitChain (s.comp initial) steps).depth ≤ _
    apply (ih (s.comp initial)).trans
    have h := Circuit.depth_comp_le s initial
    simp only [List.map_cons, List.sum_cons]
    omega

theorem normalizedChain_size {n W : ℕ} (initial : Circuit signature n W)
    (steps : List (Circuit signature W W)) :
    (normalizedChain initial steps).size =
      initial.size + W + (steps.map (fun c => c.size + W)).sum := by
  simp only [normalizedChain, circuitChain_size, normalizeOutputs_size, List.map_map,
    Function.comp_def]

theorem normalizedChain_depth {n W : ℕ} (initial : Circuit signature n W)
    (steps : List (Circuit signature W W)) :
    (normalizedChain initial steps).depth ≤
      initial.depth + 1 + (steps.map (fun c => c.depth + 1)).sum := by
  apply (circuitChain_depth (normalizeOutputs initial) (steps.map normalizeOutputs)).trans
  apply Nat.add_le_add (normalizeOutputs_depth_le initial)
  simp only [List.map_map]
  apply List.sum_le_sum
  intro j hj
  exact normalizeOutputs_depth_le j

/-- Normalization as a total operation on raw descriptions. The typed
normalization theorem establishes its semantics on well-formed circuits. -/
def normalizeCode (n W : ℕ) (c : RawCode) : RawCode :=
  (c.1 ++ c.2.map (fun i => (.and, [i, i])),
    (List.range W).map (fun i => n + c.1.length + i))

theorem normalizeCode_eq {n W : ℕ} (c : Circuit signature n W) :
    normalizeCode n W c.code = (normalizeOutputs c).code := by
  rw [normalizeOutputs_code, normalizeCode, Circuit.length_code_fst]

section Generator
variable {α : Type} {enc : α ↪ List Bool} {n W : α → ℕ}

theorem normalizeCode_logspace {code : α → RawCode}
    (hn : ComputableInLogSpace n enc encUnary) (hW : ComputableInLogSpace W enc encUnary)
    (hc : ComputableInLogSpace code enc encCode) :
    ComputableInLogSpace (fun a => normalizeCode (n a) (W a) (code a)) enc encCode := by
  have href := ComputableInLogSpace.snd enc encNat
  have hcopies := mapWithInput 0 hc.snd'
    ((ComputableInLogSpace.const (encMid := encOp) Op.and).pair
      (href.listCons (href.listCons (ComputableInLogSpace.const ([] : List ℕ)))))
  have hbase := hn.unaryAdd (ComputableInLogSpace.listLength.comp hc.fst')
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hout := map_range hW (((hbase.comp hp).unaryAdd hi).unaryToBinary)
  exact (hc.fst'.listAppend hcopies).pair hout

/-- Uniform local templates yield the actual normalized chain generator.
The entire growing circuit is not an input or an assumed uniform family. -/
theorem normalizedChain_logspace {initial : ∀ a, Circuit signature (n a) (W a)}
    {steps : ∀ a, List (Circuit signature (W a) (W a))}
    (hn : ComputableInLogSpace n enc encUnary) (hW : ComputableInLogSpace W enc encUnary)
    (hi : ComputableInLogSpace (fun a => (initial a).code) enc encCode)
    (hs : ComputableInLogSpace (fun a => (steps a).map Circuit.code) enc (encList encCode)) :
    ComputableInLogSpace (fun a => (normalizedChain (initial a) (steps a)).code) enc encCode := by
  have hinit := normalizeOutputs_logspace hn hW hi
  have hp := ComputableInLogSpace.fst enc encCode
  have hc := ComputableInLogSpace.snd enc encCode
  have hnorm := normalizeCode_logspace (hW.comp hp) (hW.comp hp) hc
  have hsteps := mapWithInput ([], []) hs hnorm
  have hsteps' : ComputableInLogSpace
      (fun a => ((steps a).map normalizeOutputs).map Circuit.code) enc (encList encCode) := by
    refine hsteps.congr_fun ?_
    intro a
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro c _
    exact (normalizeCode_eq c).symm
  have h := sequentialCodes_logspace hn hW hinit hsteps'
    (fun a => normalizeOutputs_consecutive (initial a))
    (fun a c hc => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
      exact normalizeOutputs_consecutive s)
    (fun a c hc => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
      rw [Circuit.length_code_fst]
      exact circuit_boundedReferences t)
  exact h.congr_fun fun a => circuitChain_code _ _

end Generator
end PredictionDepth.StandardComplexity.UniformComposition
