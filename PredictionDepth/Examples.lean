import PredictionDepth.Linear
import PredictionDepth.ORAutomaton

/-!
# Concrete kernel-checked regression examples

The general results are proved in the imported modules. These closed instances
exercise time zero, empty OR, endpoints of the light cone, nontrivial matrix
evolution, and the explicit finite dependency data. `decide` uses kernel-checked
proofs; no native evaluation axiom is used.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace PredictionDepth.Examples
open FastComposition

example : (orCircuit 0).eval (fun i => Fin.elim0 i) = false := by decide +kernel
example : (orCircuit 0).gateCount = 0 := by decide +kernel
example : (orCircuit 1).eval (fun _ => true) = true := by decide +kernel
example : (orCircuit 1).gateCount = 0 := by decide +kernel
example : Nat.clog 2 5 = 3 := by decide +kernel

example : ORAutomaton.prediction 0 (fun _ => true) = true := by decide +kernel
example : ORAutomaton.prediction 1 (fun i => decide (i = 0)) = true := by decide +kernel
example : ORAutomaton.prediction 2 (fun i => decide (i = 4)) = true := by decide +kernel
example : ORAutomaton.prediction 2 (fun _ => false) = false := by decide +kernel
example : (ORAutomaton.optimalCircuit 2).eval (fun i => decide (i = 4)) = true := by decide +kernel

example : (boolOr_dependencyWitness 3).coordinates.card = 3 := by decide +kernel
example : boolOr 3 ((boolOr_dependencyWitness 3).left 1) = false := by decide +kernel
example : boolOr 3 ((boolOr_dependencyWitness 3).right 1) = true := by decide +kernel
example : (boolOr_dependencyWitness 3).left 1 2 =
    (boolOr_dependencyWitness 3).right 1 2 := by decide +kernel

/-- A genuinely mixing binary linear map: `(x₀,x₁) ↦ (x₀+x₁,x₀)`. -/
def fibonacciMatrix : Linear.BinaryMatrix 2 :=
  fun i j => if i = 0 ∨ j = 0 then 1 else 0

def initial2 : Bits 2 := fun i => decide (i = 0)

example : (Linear.predictor fibonacciMatrix 0 0).eval initial2 0 = true := by decide +kernel
example : (Linear.predictor fibonacciMatrix 1 1).eval initial2 0 = true := by decide +kernel
example : (Linear.predictor fibonacciMatrix 0 5).eval initial2 0 = false := by decide +kernel

example : (Linear.predictor fibonacciMatrix 0 13).eval initial2 0 = true := by
  rw [Linear.predictor_correct]
  decide +kernel

/-- A three-cell cyclic shift, encoded as a binary matrix. -/
def cyclicMatrix : Linear.BinaryMatrix 3 :=
  fun i j => if j.val = (i.val + 1) % 3 then 1 else 0

def initial3 : Bits 3 := fun i => decide (i = 0)

example : (Linear.predictor cyclicMatrix 0 0).eval initial3 0 = true := by decide +kernel
example : (Linear.predictor cyclicMatrix 2 1).eval initial3 0 = true := by decide +kernel
example : (Linear.predictor cyclicMatrix 1 5).eval initial3 0 = true := by
  rw [Linear.predictor_correct]
  decide +kernel

example : (Linear.predictor cyclicMatrix 2 13).eval initial3 0 = true := by
  rw [Linear.predictor_correct]
  decide +kernel

example : (Linear.predictor fibonacciMatrix 0 13).depth ≤ 20 := by
  exact (Linear.predictor_depth_le fibonacciMatrix 0 13).trans (by decide)

end PredictionDepth.Examples
