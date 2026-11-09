import PredictionDepth.FastComposition
import Cslib.Computability.Circuit.Boolean.Basic
import CslibFrontier.Computability.Circuit.CompositionDepth

/-! The fixed two-stage schedule for each binary exponent digit. -/

namespace PredictionDepth.StandardComplexity.UniformComposition
open Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition

inductive Instruction where
  | square
  | multiplySeed
  | keep
  deriving DecidableEq, Repr

def Instruction.advance : Instruction → Program → Program
  | .square, p => .square p
  | .multiplySeed, p => .multiplySeed p
  | .keep, p => p

def executeProgram (ops : List Instruction) (p : Program) : Program :=
  ops.foldl (fun p op => op.advance p) p

def bitPair (b : Bool) : List Instruction :=
  [.square, if b then .multiplySeed else .keep]

/-- The input digits are little endian; execution visits the most significant
digit first, using exactly two fixed-width stages per digit. -/
def bitSteps (bits : List Bool) : List Instruction := bits.reverse.flatMap bitPair

theorem bitSteps_cons (b : Bool) (bits : List Bool) :
    bitSteps (b :: bits) = bitSteps bits ++ bitPair b := by
  simp only [bitSteps, List.reverse_cons, List.flatMap_append, List.flatMap_singleton]

@[simp] theorem bitSteps_length (bits : List Bool) : (bitSteps bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      rw [bitSteps_cons, List.length_append, ih]
      simp only [bitPair, List.length_cons, List.length_nil]
      omega

theorem executeProgram_append (as bs : List Instruction) (p : Program) :
    executeProgram (as ++ bs) p = executeProgram bs (executeProgram as p) :=
  List.foldl_append

/-- The instruction schedule is exactly the semantic repeated-squaring
program already used in Theorem A. `keep` emits no mathematical operation. -/
theorem executeProgram_bitSteps (bits : List Bool) :
    executeProgram (bitSteps bits) .identity = compileBits bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      rw [bitSteps_cons, executeProgram_append, ih]
      cases b <;> rfl

def circuitFor {W : ℕ} (square multiplySeed : Circuit signature W W) :
    Instruction → Circuit signature W W
  | .square => square
  | .multiplySeed => multiplySeed
  | .keep => Circuit.wiring signature id

def stages {W : ℕ} (square multiplySeed : Circuit signature W W) (bits : List Bool) :
    List (Circuit signature W W) :=
  (bitSteps bits).map (circuitFor square multiplySeed)

@[simp] theorem stages_length {W : ℕ} (square multiplySeed : Circuit signature W W)
    (bits : List Bool) : (stages square multiplySeed bits).length = 2 * bits.length := by
  simp [stages]

theorem circuitFor_size_le {W : ℕ} (square multiplySeed : Circuit signature W W)
    (op : Instruction) : (circuitFor square multiplySeed op).size ≤
      max square.size multiplySeed.size := by
  cases op with
  | square => exact le_max_left _ _
  | multiplySeed => exact le_max_right _ _
  | keep => exact Nat.zero_le _

theorem circuitFor_depth_le {W : ℕ} (square multiplySeed : Circuit signature W W)
    (op : Instruction) : (circuitFor square multiplySeed op).depth ≤
      max square.depth multiplySeed.depth := by
  cases op with
  | square => exact le_max_left _ _
  | multiplySeed => exact le_max_right _ _
  | keep => simp [circuitFor]

theorem sum_map_le {α : Type*} (cost : α → ℕ) (as : List α) (B : ℕ)
    (h : ∀ a ∈ as, cost a ≤ B) : (as.map cost).sum ≤ as.length * B := by
  induction as with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      simpa only [Nat.add_comm] using
        Nat.add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

end PredictionDepth.StandardComplexity.UniformComposition
