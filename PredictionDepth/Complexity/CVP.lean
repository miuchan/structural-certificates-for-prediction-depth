import CslibFrontier.Computability.Complexity.Problems.CircuitValue.Completeness

/-!
# The standard circuit-value problem

This module exposes the **proved**, machine-based CVP completeness theorem used
by the prediction framework. It does not assume that CVP is P-hard.

The imported development defines a binary encoding with topologically ordered
De Morgan gates, proves polynomial-time evaluation by a finite-control binary
multitape Turing machine, constructs computation-tableau circuits for arbitrary
polynomial-time deciders, and implements their serializer in logarithmic space.
The target circuit retains the encoded source instance as its primary inputs.

Provenance: cslib-frontier, commit
`3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d`,
`CslibFrontier/Computability/Complexity/Problems/CircuitValue/Completeness.lean`.
The dependency is built and checked by Lean; source-level statements alone are
not used as an external theorem oracle.
-/

namespace PredictionDepth.StandardComplexity

open Cslib.Circuits Cslib.Circuits.Boolean

/-- A well-formed, single-output Boolean circuit and an assignment to its inputs. -/
abbrev CVPInstance := Σ n, Circuit signature n 1 × (Fin n → Bool)

/-- Binary gate-reference encoding, with the input assignment included. -/
abbrev cvpEncoding : CVPInstance ↪ List Bool := Cslib.Complexity.encCircuitValue

/-- The actual finite circuit evaluator, not an arbitrary source language. -/
def cvpAccept (c : CVPInstance) : Bool := c.2.1.eval interpretation c.2.2 0

abbrev CVP : Set CVPInstance := Cslib.Complexity.CircuitValue

theorem mem_CVP (c : CVPInstance) : c ∈ CVP ↔ cvpAccept c = true := Iff.rfl

/-- The serialized circuit evaluator is implemented in polynomial time. -/
theorem cvp_mem_P : CVP ∈ Cslib.Complexity.P cvpEncoding :=
  Cslib.Complexity.CircuitValue.mem_P

/-- Every polynomial-time decision problem has a genuine logspace reduction to CVP. -/
theorem reduces_to_CVP_of_mem_P {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ Cslib.Complexity.P enc) :
    Cslib.Complexity.LogSpaceReducible enc cvpEncoding A CVP :=
  Cslib.Complexity.CircuitValue.logSpaceReducible_of_mem_P hA

/-- Ladner's CVP hardness theorem, with no hardness premise or added axiom. -/
theorem cvp_logSpaceHard :
    Cslib.Complexity.LogSpaceHard @Cslib.Complexity.P cvpEncoding CVP :=
  Cslib.Complexity.CircuitValue.logSpaceHard

/-- CVP is P-complete under the actual finite-machine logspace reductions. -/
theorem cvp_logSpaceComplete :
    Cslib.Complexity.LogSpaceComplete @Cslib.Complexity.P cvpEncoding CVP :=
  Cslib.Complexity.CircuitValue.logSpaceComplete

end PredictionDepth.StandardComplexity
