import PredictionDepth.Complexity.UniformComposition.TypedChain
import PredictionDepth.Complexity.UniformComposition.Schedule
import PredictionDepth.Complexity.UniformNC

/-!
# Actual uniformity of the repeated-squaring compiler

The exponent is supplied as a logspace-generated binary word. Its numeric
value is never stored by the generator. It rereads the digits backwards and
streams square/seed-multiply-or-identity templates, then uses the normalized
chain compiler. No uniformity premise is imposed on the final predictor.
-/

namespace PredictionDepth.StandardComplexity.UniformComposition

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM CodeLogspace CodeLogspaceFamilies

theorem range_reverse_getD (w : List Bool) :
    (List.range w.length).map (fun j => w.getD (w.length - (j + 1)) false) = w.reverse := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    have hj' : j < w.length := by simpa using hj
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse]
    rw [List.getD_eq_getElem _ _ (show w.length - (j + 1) < w.length by omega)]
    congr 1
    omega

section Generator
variable {α : Type} {enc : α ↪ List Bool} {n W : α → ℕ} {bits : α → List Bool}
  {initial : ∀ a, Circuit signature (n a) (W a)}
  {square multiplySeed : ∀ a, Circuit signature (W a) (W a)}
  {observation : ∀ a, Circuit signature (W a) 1}

/-- The width need not be an independent oracle: the typed initialization
code already lists exactly one output reference per working register bit. -/
theorem width_logspace_of_initialization
    (hi : ComputableInLogSpace (fun a => (initial a).code) enc encCode) :
    ComputableInLogSpace W enc encUnary :=
  (ComputableInLogSpace.listLength.comp hi.snd').congr_fun fun a => by simp [Circuit.code]

/-- Reverse the exponent digits by indexed rereads, without retaining the
binary word itself in workspace. The result is a framed list of Boolean data. -/
theorem reverseBits_logspace (hb : ComputableInLogSpace bits enc encBits) :
    ComputableInLogSpace (fun a => (bits a).reverse) enc (encList encBool) := by
  have hlen := bitsLength.comp hb
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hindex := (hlen.comp hp).unarySub (hi.unaryAdd (ComputableInLogSpace.const 1))
  have hread := (ComputableInLogSpace.bitsHeadD false).comp ((hb.comp hp).bitsDrop' hindex)
  have hread' : ComputableInLogSpace
      (fun p : α × ℕ => (bits p.1).getD ((bits p.1).length - (p.2 + 1)) false)
      (encPair enc encUnary) encBool := hread.congr_fun fun p => by
    simp [List.getD_eq_getElem?_getD]
  exact (map_range hlen hread').congr_fun fun a => (range_reverse_getD (bits a)).symm

theorem identityCode_logspace (hW : ComputableInLogSpace W enc encUnary) :
    ComputableInLogSpace
      (fun a => (Circuit.wiring signature (id : Fin (W a) → Fin (W a))).code) enc encCode := by
  have hout := map_range hW (ComputableInLogSpace.snd enc encUnary).unaryToBinary
  have hcode := (ComputableInLogSpace.const (encMid := encList encGate)
    ([] : List (Op × List ℕ))).pair hout
  exact hcode.congr_fun fun a => by simp [Circuit.code_wiring_id]

/-- The complete two-stage-per-bit template list is generated in logspace
from the time digits and the two primitive templates. -/
theorem stages_logspace
    (hW : ComputableInLogSpace W enc encUnary)
    (hb : ComputableInLogSpace bits enc encBits)
    (hs : ComputableInLogSpace (fun a => (square a).code) enc encCode)
    (hm : ComputableInLogSpace (fun a => (multiplySeed a).code) enc encCode) :
    ComputableInLogSpace
      (fun a => (stages (square a) (multiplySeed a) (bits a)).map Circuit.code)
      enc (encList encCode) := by
  have hrev := reverseBits_logspace hb
  have hp := ComputableInLogSpace.fst enc encBool
  have hv := ComputableInLogSpace.snd enc encBool
  have hid := identityCode_logspace hW
  have hchoice := hv.ite (hm.comp hp) (hid.comp hp)
  have hworker := (hs.comp hp).listCons
    (hchoice.listCons (ComputableInLogSpace.const ([] : List RawCode)))
  have h := flatMapWithInput false hrev hworker
  refine h.congr_fun ?_
  intro a
  simp only [stages, bitSteps, List.map_map, List.map_flatMap, Function.comp_def]
  apply List.flatMap_congr
  intro b _
  cases b <;> rfl

/-- The actual final Boolean predictor code is produced by a finite-state
logspace transducer from only the primitive generators and time digits. -/
theorem predictor_code_logspace
    (hn : ComputableInLogSpace n enc encUnary) (hW : ComputableInLogSpace W enc encUnary)
    (hb : ComputableInLogSpace bits enc encBits)
    (hi : ComputableInLogSpace (fun a => (initial a).code) enc encCode)
    (hs : ComputableInLogSpace (fun a => (square a).code) enc encCode)
    (hm : ComputableInLogSpace (fun a => (multiplySeed a).code) enc encCode)
    (ho : ComputableInLogSpace (fun a => (observation a).code) enc encCode) :
    ComputableInLogSpace
      (fun a => ((observation a).comp
        (normalizedChain (initial a) (stages (square a) (multiplySeed a) (bits a)))).code)
      enc encCode :=
  circuit_comp_logspace hn (normalizedChain_logspace hn hW hi (stages_logspace hW hb hs hm)) ho

/-- The arity header is included in the generated output, not supplied by an
uncharged external convention. -/
theorem predictor_encoding_logspace
    (hn : ComputableInLogSpace n enc encUnary) (hW : ComputableInLogSpace W enc encUnary)
    (hb : ComputableInLogSpace bits enc encBits)
    (hi : ComputableInLogSpace (fun a => (initial a).code) enc encCode)
    (hs : ComputableInLogSpace (fun a => (square a).code) enc encCode)
    (hm : ComputableInLogSpace (fun a => (multiplySeed a).code) enc encCode)
    (ho : ComputableInLogSpace (fun a => (observation a).code) enc encCode) :
    ComputableInLogSpace
      (fun a => (⟨n a, (observation a).comp
        (normalizedChain (initial a) (stages (square a) (multiplySeed a) (bits a)))⟩ :
          Σ n, Circuit signature n 1)) enc (encCircuit 1) :=
  (hn.pair (predictor_code_logspace hn hW hb hi hs hm ho)).congr (fun _ => rfl)

end Generator

/-- A standard unary-length-indexed uniform family, with no final-family
uniformity premise. -/
theorem predictor_uniform {W : ℕ → ℕ} {bits : ℕ → List Bool}
    {initial : ∀ n, Circuit signature n (W n)}
    {square multiplySeed : ∀ n, Circuit signature (W n) (W n)}
    {observation : ∀ n, Circuit signature (W n) 1}
    (hW : ComputableInLogSpace W encUnary encUnary)
    (hb : ComputableInLogSpace bits encUnary encBits)
    (hi : ComputableInLogSpace (fun n => (initial n).code) encUnary encCode)
    (hs : ComputableInLogSpace (fun n => (square n).code) encUnary encCode)
    (hm : ComputableInLogSpace (fun n => (multiplySeed n).code) encUnary encCode)
    (ho : ComputableInLogSpace (fun n => (observation n).code) encUnary encCode) :
    LogspaceUniform (fun n => (observation n).comp
      (normalizedChain (initial n) (stages (square n) (multiplySeed n) (bits n)))) :=
  predictor_encoding_logspace ComputableInLogSpace.id hW hb hi hs hm ho

/-- A halting logspace generator also supplies a polynomial size bound on
every circuit it emits. This is derived from real output-length complexity. -/
theorem uniform_size_polynomial {F : BooleanCircuitFamily} (hF : LogspaceUniform F) :
    PolynomiallyBounded (fun n => (F n).size) := by
  obtain ⟨C, d, hlen⟩ := hF.polyBounded_length.exists_le
  apply PolynomiallyBounded.of_forall_le C d
  intro n
  have h := Circuit.size_le_length_encCircuit encOp (⟨n, F n⟩ : Σ n, Circuit signature n 1)
  exact h.trans (by simpa only [encUnary_apply, List.length_replicate] using hlen n)

end PredictionDepth.StandardComplexity.UniformComposition
