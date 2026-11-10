import PredictionDepth.SparseCorrections.Compiler

/-! Small executable checks for the independent OR rule and empty horizons. -/

namespace PredictionDepth.SparseCorrections

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FrozenPascal (wireBit xorGate)
open BooleanReduction (orGate)

namespace ORFixture

/-- One update with the Pascal reference. The first input is the correction.
The other three inputs cover the radius-one initial window in spatial order. -/
private def response : Gates 4 4 :=
  let homogeneous := xorGate.comp (Circuit.wiring signature ![2, 3])
  let observed := xorGate.comp ((wireBit 0).append homogeneous)
  (Circuit.wiring signature (![1, 2, 3] : Fin 3 → Fin 4)).append observed

private def check : Fin 1 → Gates 4 1 := fun _ => equalCheck orGate ![1, 2] 3

private def predictor (k : ℕ) : Gates 3 2 :=
  compile response check 3 (unknownCandidates 1 k)

private def iterateOR (u : Fin 3 → Bool) : Bool := u 1 || u 2

/-- With one possible correction, the certified value agrees with direct OR
on every input. This evaluates the compiled circuit including both lanes. -/
theorem oneCorrection : ∀ u : Fin 3 → Bool,
    (predictor 1).eval interpretation u 0 = true ∧
      (predictor 1).eval interpretation u 1 = iterateOR u := by decide +kernel

/-- Zero correction fails exactly when both contributing bits are one. The
accepted zero observation and the rejected input can be distinguished. -/
theorem zeroCorrections : ∀ u : Fin 3 → Bool,
    (predictor 0).eval interpretation u 0 = !(u 1 && u 2) ∧
      (predictor 0).eval interpretation u 1 = (u 1 ^^ u 2) := by decide +kernel

/-- The empty schedule admits precisely the zero-residual candidate. -/
theorem emptySchedule (u : Fin 3 → Bool) :
    (compile response check 3 (scheduledCandidates (Fin.elim0 : Fin 0 → Fin 1))).eval interpretation u =
      (predictor 0).eval interpretation u := by
  have h : scheduledCandidates (Fin.elim0 : Fin 0 → Fin 1) = unknownCandidates 1 0 := by
    funext j i
    simp [scheduledCandidates, unknownCandidates, unknownBit]
  rw [h]
  rfl

/-- Exercise serialized wires, including constant substitution and the gate
offsets of the final reductions. -/
theorem code_agrees : ∀ (u : Fin 3 → Bool) (j : Fin 2),
    evalOutput (List.ofFn u) (predictor 1).code.1 (predictor 1).code.2[j.val]! =
      (predictor 1).eval interpretation u j := by decide +kernel

end ORFixture

private def enumeratesFullSupport (k : ℕ) : Bool :=
  (List.finRange (3 ^ k)).any fun j =>
    (List.ofFn (unknownCandidates 2 k j)).all id

/-- Two distinct addresses fill the entire two-bit support exactly at budget two. -/
theorem maximalSmallSupport :
    enumeratesFullSupport 1 = false ∧ enumeratesFullSupport 2 = true := by decide +kernel

private def emptyHorizon : Gates 1 2 :=
  compile (Circuit.id signature 1) (fun i : Fin 0 => i.elim0) 0 (unknownCandidates 0 0)

theorem emptyHorizon_predicts : ∀ u : Fin 1 → Bool,
    emptyHorizon.eval interpretation u 0 = true ∧ emptyHorizon.eval interpretation u 1 = u 0 :=
  by decide +kernel

end PredictionDepth.SparseCorrections
