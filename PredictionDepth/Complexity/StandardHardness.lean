import PredictionDepth.Complexity.Logspace
import PredictionDepth.Complexity.CVP

/-!
# The simulation criterion over standard complexity classes

The source problem here is the concrete encoded circuit value problem. Its
P-completeness and the logspace composition machinery are imported proved
theorems, not extra parameters of the simulation criterion.
-/

namespace PredictionDepth.StandardComplexity

open Turing.MultiTapeTM Cslib.Complexity

/-- The Boolean prediction language on unary-time queries. -/
def predictionLanguage {X : Type*} (F : X → X) (observe : X → Bool)
    (decodeState : Word → X) : Set Word :=
  {q | Hardness.predictionProblem F observe decodeState q = true}

/-- Data to verify for a fixed system simulating circuit evaluation.

The encoder emits the *whole unary query* in logarithmic space. This actual
machine hypothesis automatically implies polynomial output length, hence
polynomial encoded initial state length and polynomial simulation time.
The target's membership in P is a separate hypothesis for completeness.
-/
structure SimulationWitness {X : Type*} (F : X → X) (observe : X → Bool)
    (decodeState : Word → X) where
  time : CVPInstance → ℕ
  payload : CVPInstance → Word
  query_logspace : ComputableInLogSpace
    (fun c => Hardness.encodeQuery (time c) (payload c)) cvpEncoding encBits
  correct : ∀ c, observe ((F^[time c]) (decodeState (payload c))) = cvpAccept c

namespace SimulationWitness

variable {X : Type*} {F : X → X} {observe : X → Bool} {decodeState : Word → X}

def query (w : SimulationWitness F observe decodeState) (c : CVPInstance) : Word :=
  Hardness.encodeQuery (w.time c) (w.payload c)

theorem query_correct (w : SimulationWitness F observe decodeState) (c : CVPInstance) :
    Hardness.predictionProblem F observe decodeState (w.query c) = cvpAccept c := by
  simpa [query] using w.correct c

theorem query_length_polynomial (w : SimulationWitness F observe decodeState) :
    PolyBounded (fun c => (cvpEncoding c).length) (fun c => (w.query c).length) :=
  w.query_logspace.polyBounded_length

/-- A unary time field cannot exceed the polynomially long emitted query. -/
theorem time_polynomial (w : SimulationWitness F observe decodeState) :
    PolyBounded (fun c => (cvpEncoding c).length) w.time :=
  w.query_length_polynomial.mono fun c => by
    simp only [query, Hardness.encodeQuery_length]
    omega

theorem payload_length_polynomial (w : SimulationWitness F observe decodeState) :
    PolyBounded (fun c => (cvpEncoding c).length) (fun c => (w.payload c).length) :=
  w.query_length_polynomial.mono fun c => by
    simp only [query, Hardness.encodeQuery_length]
    omega

/-- The concrete logspace reduction obtained from the simulation equality. -/
theorem reduction (w : SimulationWitness F observe decodeState) :
    LogSpaceReducible cvpEncoding encBits CVP (predictionLanguage F observe decodeState) := by
  refine ⟨w.query, w.query_logspace, ?_⟩
  intro c
  change c ∈ CVP ↔ Hardness.predictionProblem F observe decodeState (w.query c) = true
  rw [w.query_correct]
  exact mem_CVP c

/-- Theorem B: the prediction language is P-hard under standard logspace reductions. -/
theorem prediction_P_hard (w : SimulationWitness F observe decodeState) :
    LogSpaceHard @P encBits (predictionLanguage F observe decodeState) :=
  cvp_logSpaceHard.trans w.reduction

/-- Theorem B: a polynomial-time predictor with a simulation witness is P-complete. -/
theorem prediction_P_complete (w : SimulationWitness F observe decodeState)
    (hP : predictionLanguage F observe decodeState ∈ P encBits) :
    LogSpaceComplete @P encBits (predictionLanguage F observe decodeState) :=
  ⟨hP, w.prediction_P_hard⟩

/-- A convenient constructor from separate logspace clock and payload implementations. -/
def ofClockAndPayload (time : CVPInstance → ℕ) (payload : CVPInstance → Word)
    (ht : ComputableInLogSpace time cvpEncoding encUnary)
    (hp : ComputableInLogSpace payload cvpEncoding encBits)
    (hc : ∀ c, observe ((F^[time c]) (decodeState (payload c))) = cvpAccept c) :
    SimulationWitness F observe decodeState :=
  ⟨time, payload, encodeQuery_logspace ht hp, hc⟩

end SimulationWitness
end PredictionDepth.StandardComplexity
