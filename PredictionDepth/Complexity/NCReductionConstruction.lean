import PredictionDepth.Complexity.UniformNC
import PredictionDepth.Complexity.UniformOR
import CslibFrontier.Computability.Circuit.Boolean.CodeSubstitution
import CslibFrontier.Computability.Circuit.Pi

/-!
# The circuit used for arbitrary logspace reductions

All possible output lengths up to a polynomial bound are considered. The
length predicate selects the matching target circuit, so the reducer's output
length need not be determined by the input length.
-/

namespace PredictionDepth.StandardComplexity.ReductionConstruction
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM

abbrev Query := ℕ × List Bool
abbrev queryEncoding : Query ↪ List Bool := encPair encUnary encBits

def queryPrefix (j : ℕ) : List Bool := frame (encUnary j)

@[simp] theorem queryPrefix_length (j : ℕ) : (queryPrefix j).length = 2 * j + 1 := by
  simp [queryPrefix, length_frame]

theorem queryEncoding_eq (j : ℕ) (x : List Bool) :
    queryEncoding (j, x) = queryPrefix j ++ x := rfl

/-- Fix the query index while retaining all live bits of the original input. -/
def prefixed (F : BooleanCircuitFamily) (n j : ℕ) : Circuit signature n 1 :=
  prefixCircuit (queryPrefix j) (F ((queryPrefix j).length + n))

/-- All `m` bits of the reduction's output, evaluated on shared source inputs. -/
def bitBank (F : BooleanCircuitFamily) (n m : ℕ) : Circuit signature n m :=
  Circuit.pi (fun j : Fin m => prefixed F n j.val)

/-- One candidate output length. Its target answer is gated by an independently
computed exact length test. -/
def branch (target bits lengthTest : BooleanCircuitFamily) (n m : ℕ) : Circuit signature n 1 :=
  (Circuit.oneGate (σ := signature) .and id).comp
    (((target m).comp (bitBank bits n m)).append (prefixed lengthTest n m))

/-- The resulting circuit tests every length `0,...,bound n`, including empty
outputs, then ORs the selected answer. -/
def family (target bits lengthTest : BooleanCircuitFamily) (bound : ℕ → ℕ) :
    BooleanCircuitFamily := fun n =>
  (UniformOR.family (bound n + 1)).comp
    (Circuit.pi fun m : Fin (bound n + 1) => branch target bits lengthTest n m.val)

end PredictionDepth.StandardComplexity.ReductionConstruction
