import PredictionDepth.Complexity.UniformReachability
import PredictionDepth.Complexity.NCReductionPredicates
import PredictionDepth.Complexity.NCReductionSemantics
import PredictionDepth.Complexity.NCReductionUniform
import PredictionDepth.Complexity.NCReductionBounds
import PredictionDepth.Complexity.StandardHardness

/-!
# Standard NC closure and the conditional hardness obstruction

The proof uses actual logspace machines, the proved NC² simulation of their
scalar predicates, polynomial-size circuit banks for every possible output
length, and a native logspace generator for that same circuit family.
-/

namespace PredictionDepth.StandardComplexity
open Cslib Cslib.Complexity Turing.MultiTapeTM
open ReductionConstruction

/-- Uniform NC is closed under precomposition with every total logspace word
function. Its output length is allowed to vary among equal-length inputs. -/
theorem uniformNC_preimage {f : List Bool → List Bool} {B : Set (List Bool)}
    (hf : ComputableInLogSpace f encBits encBits) (hB : B ∈ UniformNC) :
    f ⁻¹' B ∈ UniformNC := by
  obtain ⟨kt, target, Ct, htarget, htargetSize, htargetDepth, htargetUniform⟩ := hB
  obtain ⟨bits, Cb, hbitsUniform, hbitsSize, hbitsDepth, hbitsCorrect⟩ :=
    logspace_bool_circuits (bitQuery_logspace hf)
  obtain ⟨lengthTest, Cl, hlengthUniform, hlengthSize, hlengthDepth, hlengthCorrect⟩ :=
    logspace_bool_circuits (lengthQuery_logspace hf)
  obtain ⟨A, d, hlength⟩ := hf.polyBounded_length.exists_le
  let bound (n : ℕ) := A * (n + 1) ^ d
  have hb : ∀ x, (f x).length ≤ bound x.length := by
    intro x
    simpa only [encBits_apply] using hlength x
  have hpoly : PolynomiallyBounded bound := by dsimp only [bound]; fun_prop
  have hclock : ComputableInLogSpace bound encUnary encUnary := polynomialClock_logspace A d
  have hbits := prefixed_bitQuery bits f hbitsCorrect
  have hlen := prefixed_lengthQuery lengthTest f hlengthCorrect
  obtain ⟨K, C, hdepth⟩ := family_polylogDepth hpoly htargetDepth hbitsDepth hlengthDepth
  exact ⟨K, family target bits lengthTest bound, C,
    family_decides_preimage hbits hlen htarget hb,
    family_polynomialSize hpoly htargetSize hbitsSize hlengthSize,
    hdepth, family_uniform htargetUniform hbitsUniform hlengthUniform hclock⟩

/-- Closure under standard logspace many-one reductions, proved from the
concrete generator and machine semantics rather than posited for a class. -/
theorem uniformNC_closed_logspace {A B : Set (List Bool)}
    (hAB : LogSpaceReducible encBits encBits A B) (hB : B ∈ UniformNC) : A ∈ UniformNC := by
  obtain ⟨f, hf, hcorrect⟩ := hAB
  have heq : A = f ⁻¹' B := Set.ext hcorrect
  rw [heq]
  exact uniformNC_preimage hf hB

/-- A standard P-hard problem in uniform NC would collapse the two classes. -/
theorem hard_in_uniformNC_implies_eq {A : Set (List Bool)}
    (hA : LogSpaceHard @P encBits A) (hNC : A ∈ UniformNC) : P encBits = UniformNC := by
  apply Set.Subset.antisymm
  · intro B hB
    exact uniformNC_closed_logspace (hA encBits B hB) hNC
  · exact uniformNC_subset_P

/-- The only unproved premise is the explicitly stated class separation. No
numerical linear or power-law depth lower bound is claimed. -/
theorem hard_not_uniformNC {A : Set (List Bool)}
    (hA : LogSpaceHard @P encBits A) (hne : P encBits ≠ UniformNC) : A ∉ UniformNC := by
  intro h
  exact hne (hard_in_uniformNC_implies_eq hA h)

namespace SimulationWitness

/-- Theorem B's conditional obstruction, now over fully machine-defined
standard P, logspace reductions, and logspace-uniform NC. -/
theorem prediction_not_uniformNC {X : Type*} {F : X → X} {observe : X → Bool}
    {decodeState : Word → X} (w : SimulationWitness F observe decodeState)
    (hne : P encBits ≠ UniformNC) : predictionLanguage F observe decodeState ∉ UniformNC :=
  hard_not_uniformNC w.prediction_P_hard hne

end SimulationWitness
end PredictionDepth.StandardComplexity
