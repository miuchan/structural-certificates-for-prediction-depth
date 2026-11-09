import PredictionDepth.Complexity.UniformComposition.Generator
import PredictionDepth.Complexity.UniformCompositionSemantics

/-!
# The uniform fast-composition criterion

This is the machine-level uniform version of Theorem A. The only generators
supplied by a user are the width, canonical binary time, and the four local
primitive templates. The final predictor's generator and polynomial size are
proved. The dynamics may have an infinite state space; only inputs and working
registers are finite bit vectors. Semantic obligations concern the executed
path, rather than all representations.
-/

namespace PredictionDepth.StandardComplexity.UniformComposition

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM FastComposition

/-- Structural data for a family of exact predictors, with genuine native
logspace generators for the local components. Binary time can be exponentially
large: the generator never needs to print it in unary. -/
structure UniformRegisterWitness {X : Type*} {R : ℕ → Type*} {F : X → X}
    (r : ∀ n, Realization X (R n) F) (input : ∀ n, Bits n → X)
    (observe : X → Bool) (T : ℕ → ℕ) where
  width : ℕ → ℕ
  witness : ∀ n, RegisterWitness (W := width n) (r n) (input n) observe (binaryDigits (T n))
  width_logspace : ComputableInLogSpace width encUnary encUnary
  timeBits_logspace : ComputableInLogSpace (fun n => binaryDigits (T n)) encUnary encBits
  initialization_logspace : ComputableInLogSpace
    (fun n => (witness n).initialization.code) encUnary encCode
  square_logspace : ComputableInLogSpace (fun n => (witness n).square.code) encUnary encCode
  multiplySeed_logspace : ComputableInLogSpace (fun n => (witness n).multiplySeed.code)
    encUnary encCode
  observation_logspace : ComputableInLogSpace (fun n => (witness n).observation.code)
    encUnary encCode

namespace UniformRegisterWitness

variable {X : Type*} {R : ℕ → Type*} {F : X → X}
  {r : ∀ n, Realization X (R n) F} {input : ∀ n, Bits n → X}
  {observe : X → Bool} {T : ℕ → ℕ}

/-- Constructor using only the primitive generators and binary time. The
working width is recovered in logspace from the initialization output list. -/
def ofPrimitiveGenerators (width : ℕ → ℕ)
    (witness : ∀ n, RegisterWitness (W := width n) (r n) (input n) observe (binaryDigits (T n)))
    (ht : ComputableInLogSpace (fun n => binaryDigits (T n)) encUnary encBits)
    (hi : ComputableInLogSpace (fun n => (witness n).initialization.code) encUnary encCode)
    (hs : ComputableInLogSpace (fun n => (witness n).square.code) encUnary encCode)
    (hm : ComputableInLogSpace (fun n => (witness n).multiplySeed.code) encUnary encCode)
    (ho : ComputableInLogSpace (fun n => (witness n).observation.code) encUnary encCode) :
    UniformRegisterWitness r input observe T :=
  ⟨width, witness, width_logspace_of_initialization hi, ht, hi, hs, hm, ho⟩

def family (w : UniformRegisterWitness r input observe T) : BooleanCircuitFamily :=
  fun n => (w.witness n).circuit

/-- Constructive uniformity of the complete predictor, derived from the local
generators by indexed rereading, normalization, and streamed code relocation. -/
theorem uniform (w : UniformRegisterWitness r input observe T) : LogspaceUniform w.family :=
  predictor_uniform w.width_logspace w.timeBits_logspace w.initialization_logspace
    w.square_logspace w.multiplySeed_logspace w.observation_logspace

/-- The full serialized output of a logspace generator is polynomially long,
so the generated predictor family has polynomially many gates. -/
theorem polynomial_size (w : UniformRegisterWitness r input observe T) :
    PolynomiallyBounded (fun n => (w.family n).size) := uniform_size_polynomial w.uniform

theorem correct (w : UniformRegisterWitness r input observe T) (n : ℕ) (x : Bits n) :
    (w.family n).eval interpretation x 0 = observe (F^[T n] (input n x)) :=
  (w.witness n).circuit_at_time_correct x

/-- An explicit integer bound including initialization, output normalization,
and decoding. Canonical bits are what justifies the logarithm of the time. -/
theorem depth_le (w : UniformRegisterWitness r input observe T) (n : ℕ) :
    (w.family n).depth ≤ (w.witness n).initialization.depth + 1 +
      2 * Nat.clog 2 (T n + 1) *
        (max (w.witness n).square.depth (w.witness n).multiplySeed.depth + 1) +
      (w.witness n).observation.depth :=
  predictor_logarithmic_depth _ _ _ _ (T n)

/-- Named cost bounds may replace the concrete primitive depths. -/
theorem depth_le_costs (w : UniformRegisterWitness r input observe T)
    (η δ ε : ℕ → ℕ)
    (hi : ∀ n, (w.witness n).initialization.depth ≤ η n)
    (hs : ∀ n, (w.witness n).square.depth ≤ δ n)
    (hm : ∀ n, (w.witness n).multiplySeed.depth ≤ δ n)
    (ho : ∀ n, (w.witness n).observation.depth ≤ ε n) (n : ℕ) :
    (w.family n).depth ≤ η n + 1 + 2 * Nat.clog 2 (T n + 1) * (δ n + 1) + ε n := by
  apply (w.depth_le n).trans
  have hmax := max_le (hs n) (hm n)
  have hmul := Nat.mul_le_mul_left (2 * Nat.clog 2 (T n + 1)) (Nat.add_le_add_right hmax 1)
  have := hi n
  have := ho n
  omega

/-- For positive primitive depth bounds, the normalization overhead preserves
the advertised `O(log T * δ + ε)` form, with preparation charged explicitly. -/
theorem depth_le_positive_costs (w : UniformRegisterWitness r input observe T)
    (η δ ε : ℕ → ℕ)
    (hi : ∀ n, (w.witness n).initialization.depth ≤ η n)
    (hs : ∀ n, (w.witness n).square.depth ≤ δ n)
    (hm : ∀ n, (w.witness n).multiplySeed.depth ≤ δ n)
    (ho : ∀ n, (w.witness n).observation.depth ≤ ε n)
    (hδ : ∀ n, 1 ≤ δ n) (n : ℕ) :
    (w.family n).depth ≤ η n + 1 + 4 * Nat.clog 2 (T n + 1) * δ n + ε n := by
  have h := w.depth_le_costs η δ ε hi hs hm ho n
  have hd := hδ n
  nlinarith [Nat.zero_le (Nat.clog 2 (T n + 1))]

/-- The total word language associated with this fixed time-by-length policy. -/
def language (_w : UniformRegisterWitness r input observe T) : Set (List Bool) :=
  {x | observe (F^[T x.length] (input x.length (BitString.ofList x.length x))) = true}

theorem decides (w : UniformRegisterWitness r input observe T) : FamilyDecides w.family w.language := by
  intro x
  change _ ↔ (w.family x.length).eval interpretation (BitString.ofList x.length x) 0 = true
  rw [w.correct]
  rfl

/-- Polylogarithmic primitive-cost bounds yield membership in standard uniform
NC, with the same constructed family witnessing size, depth and uniformity. -/
theorem mem_uniformNCLevel_of_cost (w : UniformRegisterWitness r input observe T) (c k : ℕ)
    (hcost : ∀ n, (w.witness n).initialization.depth + 1 +
      2 * Nat.clog 2 (T n + 1) *
        (max (w.witness n).square.depth (w.witness n).multiplySeed.depth + 1) +
      (w.witness n).observation.depth ≤ c * (Nat.log 2 n + 1) ^ k) :
    w.language ∈ UniformNCLevel k :=
  ⟨w.family, c, w.decides, w.polynomial_size, fun n => (w.depth_le n).trans (hcost n), w.uniform⟩

end UniformRegisterWitness
end PredictionDepth.StandardComplexity.UniformComposition
