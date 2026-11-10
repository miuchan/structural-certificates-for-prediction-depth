import PredictionDepth.SparseCorrections.CollisionCertificate
import CslibFrontier.Computability.Circuit.Evaluation

/-! Executable end-to-end checks of the response and verifier on two-collision inputs. -/

namespace PredictionDepth.SparseCorrections.Collision

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

private def encodedResidual (ell : ℕ) : Fin (Streaming.M (2 * ell)) → Bool :=
  exampleResidual ell ∘ (Cone.eventIndex 3 1 (2 * ell)).symm

private def directTrajectory (ell : ℕ) (j : Fin (Streaming.V (2 * ell))) : Bool :=
  let t := (Cone.stateIndex 3 1 (2 * ell)).symm j
  Cone.restrict 1 (2 * ell) t.1.val (Cell.bits ∘ (step^[t.1.val]) (initial ell)) t.2

private def checkExample (ell : ℕ) : Bool :=
  let T := 2 * ell
  let inputs := Vector.ofFn (Fin.append (encodedResidual ell) (exampleInput ell))
  let response := Streaming.circuit T
  let y := (response.evalVector interpretation inputs.get).get
  let values := List.ofFn y
  values == List.ofFn (directTrajectory ell) &&
    (List.ofFn (fun i => (check T i).eval interpretation y 0)).all id &&
    y (observation T) &&
    (if ell = 1 then
      let code := response.code
      let wires := evalCode interpretation false inputs.toList code.1
      code.2.map (wires.getD · false) == values
    else true)

-- Use the actual residual as input, then compare every output to direct iteration.
-- At the smallest distance, also compare the serialized and typed outputs.
#guard [1, 2, 3].all checkExample

private def omittedCorrection : Bool :=
  let missing := Cone.eventIndex 3 1 2 (secondA (ell := 1) (by decide))
  let actual := encodedResidual 1
  let guessed := fun i => decide (i ≠ missing) && actual i
  let y := ((Streaming.circuit 2).evalVector interpretation (Fin.append guessed (exampleInput 1))).get
  actual missing && (List.ofFn fun i => ((check 2 i).eval interpretation y 0 == decide (i ≠ missing))).all id

-- The second collision's returning particle is absent from the guess.
-- The local check at that zeroed coordinate fails even though all others pass.
#guard omittedCorrection

end PredictionDepth.SparseCorrections.Collision
