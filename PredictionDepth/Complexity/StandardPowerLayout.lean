import PredictionDepth.Complexity.StandardPower

/-! Stable closed gate-index arithmetic for the regular power-network layout. -/
namespace PredictionDepth.StandardComplexity.StandardPower
open Cslib Cslib.Circuits Cslib.Circuits.Boolean

abbrev stageCount (N : ℕ) := N.size + 1

/-- Matrix entries at the start of a squaring block. At stage zero they are
primary inputs; later they are the zero-th lane of the preceding merge block. -/
def matrixWire (N stage entry : ℕ) : ℕ :=
  if stage = 0 then entry
  else N * N + (stage - 1) * layerWidth N + entry * width N

def productGateCode (N stage q : ℕ) : Op × List ℕ :=
  let entry := q / width N
  let k := q % width N
  if k < N then
    (.and, [matrixWire N stage ((entry / N) * N + k),
      matrixWire N stage (k * N + entry % N)])
  else (.const false, [])

def mergeGateCode (N stage q : ℕ) : Op × List ℕ :=
  let entry := q / width N
  let k := q % width N
  let base := N * N + (stage - 1) * layerWidth N + entry * width N
  if 2 * k + 1 < width N then (.or, [base + 2 * k, base + 2 * k + 1])
  else (.const false, [])

/-- Gate `q` of any prefix of the shared matrix-power network. -/
def powerGate (N q : ℕ) : Op × List ℕ :=
  let stage := q / layerWidth N
  let localIndex := q % layerWidth N
  if stage % stageCount N = 0 then productGateCode N stage localIndex
  else mergeGateCode N stage localIndex

def powerOutput (N rounds i : ℕ) : ℕ := matrixWire N (rounds * stageCount N) i

def powerCode (N rounds : ℕ) : List (Op × List ℕ) × List ℕ :=
  ((List.range (rounds * (stageCount N * layerWidth N))).map (powerGate N),
    (List.range (N * N)).map (powerOutput N rounds))

def acceptingGateCode (N start : ℕ) (accept : ℕ → Bool) (stage q : ℕ) : Op × List ℕ :=
  let k := q % width N
  if k < N then
    if accept k then
      let wire := matrixWire N stage (start * N + k)
      (.and, [wire, wire])
    else (.const false, [])
  else (.const false, [])

def deciderGate (N start : ℕ) (accept : ℕ → Bool) (q : ℕ) : Op × List ℕ :=
  let stage := q / layerWidth N
  let localIndex := q % layerWidth N
  if stage < N.size * stageCount N then powerGate N q
  else if stage % stageCount N = 0 then acceptingGateCode N start accept stage localIndex
  else mergeGateCode N stage localIndex

def deciderOutput (N start : ℕ) : ℕ :=
  N * N + ((stageCount N) ^ 2 - 1) * layerWidth N + (start * N + start) * width N

def deciderCode (N start : ℕ) (accept : ℕ → Bool) : List (Op × List ℕ) × List ℕ :=
  ((List.range ((stageCount N) ^ 2 * layerWidth N)).map (deciderGate N start accept),
    [deciderOutput N start])

end PredictionDepth.StandardComplexity.StandardPower
