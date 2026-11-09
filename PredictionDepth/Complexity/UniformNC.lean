import CslibFrontier.Computability.Complexity.Problems.CircuitValue
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
import Mathlib.Data.Nat.Log

/-!
# Standard logspace-uniform NC

One circuit-family witness must satisfy polynomial size, polylogarithmic depth,
and genuine logspace uniformity. This is not an intersection of two classes
with unrelated circuit-family witnesses. Uniformity means generation of the
finite serialized circuits by a finite-state multitape Turing transducer on
unary input length, under CSLib's logarithmic work-space bound.

The containment in `P` uses CSLib's proved logspace-to-polynomial-time simulation
and its sequential evaluator for encoded Boolean circuits. It is not assumed.
-/

namespace PredictionDepth.StandardComplexity

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM

/-- One De Morgan circuit for every input length, including zero. -/
abbrev BooleanCircuitFamily := (n : ℕ) → Circuit signature n 1

/-- Standard logspace uniformity, with unary input length and the complete
finite circuit encoding (arity, gate list, wiring, output) charged as output. -/
def LogspaceUniform (F : BooleanCircuitFamily) : Prop :=
  ComputableInLogSpace (fun n => (⟨n, F n⟩ : Σ n, Circuit signature n 1))
    encUnary (encCircuit 1)

/-- Evaluate exactly the member indexed by the input length. -/
def evaluateFamily (F : BooleanCircuitFamily) (x : List Bool) : Bool :=
  (F x.length).eval interpretation (BitString.ofList x.length x) 0

/-- Correctness on all words, so malformed word encodings do not hide a promise. -/
def FamilyDecides (F : BooleanCircuitFamily) (L : Set (List Bool)) : Prop :=
  ∀ x, x ∈ L ↔ evaluateFamily F x = true

/-- Uniform `NC^k`: the constants and generator are fixed for the entire family. -/
def UniformNCLevel (k : ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (F : BooleanCircuitFamily) (c : ℕ),
    FamilyDecides F L ∧ PolynomiallyBounded (fun n => (F n).size) ∧
      (∀ n, (F n).depth ≤ c * (Nat.log 2 n + 1) ^ k) ∧ LogspaceUniform F}

/-- Standard uniform NC is the union over fixed polylogarithmic exponents. -/
def UniformNC : Set (Set (List Bool)) := {L | ∃ k, L ∈ UniformNCLevel k}

/-- The concrete generator and circuit evaluator compose into a polynomial-time
machine. The full generated circuit encoding is included in the computation. -/
theorem LogspaceUniform.evaluate_computableInPolyTime {F : BooleanCircuitFamily}
    (hF : LogspaceUniform F) :
    ComputableInPolyTime (evaluateFamily F) encBits encBool := by
  have hgen : ComputableInPolyTime
      (fun x : List Bool => (⟨x.length, F x.length⟩ : Σ n, Circuit signature n 1))
      encBits (encCircuit 1) :=
    hF.computableInPolyTime.comp ComputableInPolyTime.length_bits
  exact computableInPolyTime_evalCircuit hgen ComputableInPolyTime.id'

/-- A halting logarithmic-space transducer has polynomially long output, so
its explicitly printed circuit family automatically has polynomial gate size. -/
theorem LogspaceUniform.polynomialSize {F : BooleanCircuitFamily} (hF : LogspaceUniform F) :
    PolynomiallyBounded (fun n => (F n).size) := by
  obtain ⟨A, d, h⟩ := hF.polyBounded_length.exists_le
  refine Cslib.polynomiallyBounded_iff_le.mpr ⟨A, d, ?_⟩
  intro n
  apply (Circuit.size_le_length_encCircuit encOp ⟨n, F n⟩).trans
  simpa only [encUnary_apply, List.length_replicate] using h n

theorem mem_uniformNCLevel_of_uniform {F : BooleanCircuitFamily} {L : Set (List Bool)}
    {k c : ℕ} (hF : LogspaceUniform F) (hdec : FamilyDecides F L)
    (hdepth : ∀ n, (F n).depth ≤ c * (Nat.log 2 n + 1) ^ k) : L ∈ UniformNCLevel k :=
  ⟨F, c, hdec, hF.polynomialSize, hdepth, hF⟩

/-- Standard `NC^k ⊆ P`, with actual machine-defined computation predicates. -/
theorem uniformNCLevel_subset_P (k : ℕ) : UniformNCLevel k ⊆ P encBits := by
  rintro L ⟨F, c, hdec, _, _, huniform⟩
  exact ⟨evaluateFamily F, huniform.evaluate_computableInPolyTime, hdec⟩

/-- Standard `NC ⊆ P`, without external complexity-class inclusion hypotheses. -/
theorem uniformNC_subset_P : UniformNC ⊆ P encBits := by
  rintro L ⟨k, hk⟩
  exact uniformNCLevel_subset_P k hk

theorem uniformNCLevel_mono {i j : ℕ} (hij : i ≤ j) :
    UniformNCLevel i ⊆ UniformNCLevel j := by
  rintro L ⟨F, c, hdec, hsize, hdepth, huniform⟩
  refine ⟨F, c, hdec, hsize, ?_, huniform⟩
  intro n
  exact (hdepth n).trans (Nat.mul_le_mul_left c
    (Nat.pow_le_pow_right (by omega : 1 ≤ Nat.log 2 n + 1) hij))

theorem uniformNCLevel_subset_uniformNC (k : ℕ) : UniformNCLevel k ⊆ UniformNC :=
  fun _ h => ⟨k, h⟩

end PredictionDepth.StandardComplexity
