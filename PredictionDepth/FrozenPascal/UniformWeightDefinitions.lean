import CslibFrontier.Computability.Circuit.Boolean.CarrySave

/-! Pure values for the regular carry-save counting network. -/
namespace PredictionDepth.FrozenPascal.UniformWeight
open Cslib Cslib.Circuits Cslib.Circuits.Boolean

abbrev Pair (w : ℕ) := BitString (w + w)
def zero (w : ℕ) : Pair w := fun _ => false

def combine (w : ℕ) (a b : Pair w) : Pair w :=
  (csa4to2 w).eval interpretation (Fin.append a b)

def extend {w P : ℕ} (v : Fin P → Pair w) (j : ℕ) : Pair w :=
  if h : j < P then v ⟨j, h⟩ else zero w

def mergeValues {w P : ℕ} (v : Fin P → Pair w) : Fin P → Pair w :=
  fun j => combine w (extend v (2 * j.val)) (extend v (2 * j.val + 1))

def reduceValues {w P : ℕ} : ℕ → (Fin P → Pair w) → Fin P → Pair w
  | 0, v => v
  | d + 1, v => mergeValues (reduceValues d v)

def leaves (n w P : ℕ) (x : BitString n) : Fin P → Pair w := fun j =>
  if h : j.val < n then (bitPairCircuit n w ⟨j.val, h⟩).eval interpretation x else zero w

end PredictionDepth.FrozenPascal.UniformWeight
