import PredictionDepth.Hardness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Complexity.Classes.LogSpace

/-!
# Concrete logarithmic-space computation

This module instantiates the earlier reduction interface using actual
finite-state, binary multitape machines. The imported composition theorem
constructs a machine which recomputes intermediate output symbols on demand;
composition closure is not an assumption of this module.
-/

namespace PredictionDepth.StandardComplexity

open Turing.MultiTapeTM

abbrev Word := List Bool

/-- The concrete standard logspace predicate on binary words. -/
abbrev Logspace (f : Word → Word) : Prop := ComputableInLogSpace f encBits encBits

theorem logspace_id : Logspace id := ComputableInLogSpace.id

/-- Closure obtained from the verified finite-machine recomputation compiler. -/
theorem logspace_comp {f g : Word → Word} (hf : Logspace f) (hg : Logspace g) :
    Logspace (g ∘ f) := hg.comp hf

/-- A genuine instance of the auxiliary abstract reduction interface. -/
def logspaceReductionSystem : Hardness.ReductionSystem where
  Admissible := Logspace
  identity_admissible := logspace_id
  compose_admissible := fun _ _ hf hg => logspace_comp hf hg

/-- Unary clock generation and state encoding can be checked independently.
Their concatenation, with a zero delimiter, is again computable in logspace. -/
theorem encodeQuery_logspace {α : Type} {enc : α ↪ List Bool}
    {time : α → ℕ} {payload : α → Word}
    (ht : ComputableInLogSpace time enc encUnary)
    (hp : ComputableInLogSpace payload enc encBits) :
    ComputableInLogSpace (fun a => Hardness.encodeQuery (time a) (payload a)) enc encBits := by
  have hz : ComputableInLogSpace (fun _ : α => [false]) enc encBits :=
    ComputableInLogSpace.const [false]
  have hs : ComputableInLogSpace (fun a => false :: payload a) enc encBits :=
    hz.append hp (fun _ => rfl)
  exact ht.append hs (fun _ => rfl)

/-- The full emitted query has polynomial length as a theorem of the machine model. -/
theorem logspace_output_polynomial {α : Type} {enc : α ↪ List Bool} {f : α → Word}
    (hf : ComputableInLogSpace f enc encBits) :
    PolyBounded (fun a => (enc a).length) (fun a => (f a).length) :=
  hf.polyBounded_length

end PredictionDepth.StandardComplexity
