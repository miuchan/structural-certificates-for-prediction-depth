import PredictionDepth.Hardness
import CslibFrontier.Computability.Complexity.Classes.P
import CslibFrontier.Computability.Machines.Turing.TM2.Recoding

/-!
# Relating the auxiliary stack-machine predicate to standard P

The auxiliary development uses mathlib's finite-alphabet TM2 machines. This
forward simulation theorem embeds those machine witnesses into the concrete
multitape notion used by the standard complexity layer.
-/

namespace PredictionDepth.StandardComplexity

open Turing.MultiTapeTM

/-- The finite-stack-alphabet auxiliary P predicate implies the standard
multitape P predicate, with the same raw binary input and one-bit answer. -/
theorem stack_InP_implies_standard_P {A : Hardness.DecisionProblem} (h : Hardness.InP A) :
    {x | A x = true} ∈ Cslib.Complexity.P encBits := by
  obtain ⟨c, hc⟩ := h
  let : ∀ k, Finite (c.tm.Γ k) := hc
  let c' : Turing.TM2ComputableInPolyTime encBits encBool A := c
  exact ⟨A, c'.computableInPolyTime, fun _ => Iff.rfl⟩

end PredictionDepth.StandardComplexity
