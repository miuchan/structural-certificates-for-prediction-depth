import PredictionDepth.CompiledComposition
import PredictionDepth.Complexity.CodeLogspace
import CslibFrontier.Computability.Circuit.CompositionDepth

/-! A costed directional reduction between predictions on explicit windows. -/

namespace PredictionDepth

open FastComposition (Bits)
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM

/-- A time-indexed prediction on a specified finite input and output encoding. -/
abbrev WindowPrediction (n out : ℕ → ℕ) :=
  (T : ℕ) → Bits (n T) → Bits (out T)

/-- Reduce a source observation to a target observation by a time map and
explicit circuits for the input and output maps. -/
structure PredictionReduction {n m p q : ℕ → ℕ}
    (source : WindowPrediction n p) (target : WindowPrediction m q) where
  targetTime : ℕ → ℕ
  encodeInput : (T : ℕ) → Circuit signature (n T) (m (targetTime T))
  decodeOutput : (T : ℕ) → Circuit signature (q (targetTime T)) (p T)
  correct : ∀ T x,
    (decodeOutput T).eval interpretation (target (targetTime T)
      ((encodeInput T).eval interpretation x)) = source T x

namespace PredictionReduction

variable {n m p q : ℕ → ℕ} {source : WindowPrediction n p} {target : WindowPrediction m q}
variable (reduction : PredictionReduction source target)

/-- Compile a target predictor for the selected time into a source predictor. -/
def compile (T : ℕ) (c : Circuit signature (m (reduction.targetTime T))
    (q (reduction.targetTime T))) : Circuit signature (n T) (p T) :=
  (reduction.decodeOutput T).comp (c.comp (reduction.encodeInput T))

theorem compile_correct (T : ℕ) {c : Circuit signature (m (reduction.targetTime T))
    (q (reduction.targetTime T))} (hc : ∀ x, c.eval interpretation x = target (reduction.targetTime T) x)
    (x : Bits (n T)) : (reduction.compile T c).eval interpretation x = source T x := by
  simp only [compile, Circuit.eval_comp, hc, reduction.correct]

theorem compile_depth (T : ℕ) (c : Circuit signature (m (reduction.targetTime T))
    (q (reduction.targetTime T))) :
    (reduction.compile T c).depth ≤
      (reduction.encodeInput T).depth + c.depth + (reduction.decodeOutput T).depth := by
  have h := Circuit.depth_comp_le (reduction.decodeOutput T) (c.comp (reduction.encodeInput T))
  have h' := Circuit.depth_comp_le c (reduction.encodeInput T)
  unfold compile
  omega

theorem compile_size (T : ℕ) (c : Circuit signature (m (reduction.targetTime T))
    (q (reduction.targetTime T))) :
    (reduction.compile T c).size =
      (reduction.encodeInput T).size + c.size + (reduction.decodeOutput T).size := by
  simp [compile]

/-- The reduction can transfer a lower bound on its source to its target
after charging the translation costs. -/
theorem source_lower_le_target_cost (T L : ℕ)
    (lower : ∀ c : Circuit signature (n T) (p T),
      (∀ x, c.eval interpretation x = source T x) → L ≤ c.depth)
    {c : Circuit signature (m (reduction.targetTime T)) (q (reduction.targetTime T))}
    (hc : ∀ x, c.eval interpretation x = target (reduction.targetTime T) x) :
    L ≤ (reduction.encodeInput T).depth + c.depth + (reduction.decodeOutput T).depth :=
  (lower (reduction.compile T c) (reduction.compile_correct T hc)).trans (reduction.compile_depth T c)

/-- The composed circuit has a real logspace serializer when the input
width, time map, and circuit codes can each be produced in logarithmic space. -/
theorem compile_code_logspace {C : (U : ℕ) → Circuit signature (m U) (q U)}
    (hn : ComputableInLogSpace n encUnary encUnary)
    (ht : ComputableInLogSpace reduction.targetTime encUnary encUnary)
    (hinput : ComputableInLogSpace (fun T => (reduction.encodeInput T).code) encUnary encCode)
    (houtput : ComputableInLogSpace (fun T => (reduction.decodeOutput T).code) encUnary encCode)
    (htarget : ComputableInLogSpace (fun U => (C U).code) encUnary encCode) :
    ComputableInLogSpace (fun T => (reduction.compile T (C (reduction.targetTime T))).code)
      encUnary encCode :=
  StandardComplexity.CodeLogspace.circuit_comp_logspace hn
    (StandardComplexity.CodeLogspace.circuit_comp_logspace hn hinput (htarget.comp ht)) houtput

/-- The serialized encoder lists every target input wire, so its output
width is polynomial in the unary source parameter. -/
theorem target_width_polyBounded
    (hinput : ComputableInLogSpace (fun T => (reduction.encodeInput T).code) encUnary encCode) :
    PolyBounded (fun T : ℕ => T) (fun T => m (reduction.targetTime T)) := by
  have hwidth : ComputableInLogSpace (fun T => m (reduction.targetTime T)) encUnary encUnary :=
    (ComputableInLogSpace.listLength.comp hinput.snd').congr_fun (fun T => by simp [Circuit.code])
  simpa only [encUnary_apply, List.length_replicate] using hwidth.polyBounded_length

end PredictionReduction
end PredictionDepth
