import PredictionDepth.Circuit
import PredictionDepth.CompiledComposition
import Mathlib.Tactic.FinCases

/-! Translations preserve the Boolean semantics of the two circuit presentations. -/
namespace PredictionDepth
open FastComposition

namespace BoundedCircuit

/-- Translate a binary formula to a compositional Boolean circuit. -/
def toBinary {n d : ℕ} : BoundedCircuit 2 n d → BinaryCircuit n 1
  | .input i => .wire (fun _ => .inr i)
  | .constant a => .wire (fun _ => .inl a)
  | .gate op args => .seq (.parallel (toBinary (args 0)) (toBinary (args 1)))
      (.gate (fun a b => op ![a, b]))

theorem toBinary_eval {n d : ℕ} (c : BoundedCircuit 2 n d) (x : BooleanInput n) :
    c.toBinary.eval x 0 = c.eval x := by
  induction c with
  | input i => rfl
  | constant a => rfl
  | gate op args ih =>
    simp only [toBinary, BinaryCircuit.eval, eval]
    change op ![(args 0).toBinary.eval x 0, (args 1).toBinary.eval x 0] = _
    rw [ih 0, ih 1]
    congr 1
    funext i
    fin_cases i <;> rfl

theorem toBinary_depth {n d : ℕ} (c : BoundedCircuit 2 n d) : c.toBinary.depth ≤ d := by
  induction c with
  | input i => simp [toBinary, BinaryCircuit.depth]
  | constant a => simp [toBinary, BinaryCircuit.depth]
  | @gate d op args ih =>
    simp only [toBinary, BinaryCircuit.depth]
    exact Nat.add_le_add_right (max_le (ih 0) (ih 1)) 1

theorem toBinary_gateCount {n d : ℕ} (c : BoundedCircuit 2 n d) :
    c.toBinary.gateCount = c.gateCount := by
  induction c with
  | input i => rfl
  | constant a => rfl
  | gate op args ih =>
    simp [toBinary, BinaryCircuit.gateCount, gateCount, ih, Fin.sum_univ_two,
      Nat.add_comm]

/-- Count all formula-description nodes and wiring entries, as well as gates. -/
theorem toBinary_descriptionSize {n d : ℕ} (c : BoundedCircuit 2 n d) :
    c.toBinary.descriptionSize = 5 * c.gateCount + 2 := by
  induction c with
  | input i => rfl
  | constant a => rfl
  | gate op args ih =>
    simp only [toBinary, BinaryCircuit.descriptionSize, gateCount, ih, Fin.sum_univ_two]
    omega

end BoundedCircuit
end PredictionDepth
