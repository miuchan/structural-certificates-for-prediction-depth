import PredictionDepth.Complexity.LogspaceBatch.Trace
import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord.Native
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary

/-!
The streaming batch controller. It scans the original input once to learn its
length, then repeatedly executes a native machine on the virtual input
`frame original ++ unary index`. Only the index and native work configuration
are retained, and each output bit is emitted immediately.
-/

namespace PredictionDepth.StandardComplexity.LogspaceBatch

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal
open Turing.VirtualWord

/-- Fixed polynomial envelope for the number of batches. -/
def count (C d n : ℕ) : ℕ := C * (n + 1) ^ d

/-- The original input is not stored in this state. -/
abbrev State := Bool × ℕ × ℕ × SCfg

abbrev encState : State ↪ List Bool :=
  encPair encBool (encPair encNat (encPair encNat eCfg))

def scanState (D : Desc) (n : ℕ) : State := (false, n, 0, init D)
def itemState (n j : ℕ) (q : SCfg) : State := (true, n, j, q)

/-- Restore a virtual framed-input symbol from a single original-input read. -/
def symbol (n j q : ℕ) (b : Option Bool) : Option Bool :=
  if q < 2 * n then
    if q % 2 = 0 then some true else b
  else if q = 2 * n then some false
  else if q < 2 * n + 1 + j then some true else none

theorem symbol_correct (w : List Bool) (j q : ℕ) :
    symbol w.length j q (w[q / 2]?) = (frame w ++ List.replicate j true)[q]? := by
  by_cases hq : q < 2 * w.length
  · have hi : q / 2 < w.length := by omega
    by_cases he : q % 2 = 0
    · have h : q = 2 * (q / 2) := by omega
      rw [symbol, ite_eq_left hq, ite_eq_left he, h]
      exact (getElem?_frame_append w _ hi).1.symm
    · have h : q = 2 * (q / 2) + 1 := by omega
      rw [symbol, ite_eq_left hq, ite_eq_right he, h]
      rw [show (2 * (q / 2) + 1) / 2 = q / 2 by omega]
      simpa only [List.getElem?_eq_getElem hi] using
        (getElem?_frame_append w (List.replicate j true) hi).2.symm
  · by_cases he : q = 2 * w.length
    · rw [symbol, ite_eq_right hq, ite_eq_left he, he]
      exact (getElem?_frame_append_length _ _).symm
    · have h : q = 2 * w.length + 1 + (q - (2 * w.length + 1)) := by omega
      rw [symbol, ite_eq_right hq, ite_eq_right he, h, getElem?_frame_append_boundary]
      by_cases hj : q - (2 * w.length + 1) < j
      · simp only [List.getElem?_replicate, ite_eq_left hj]
        simp only [ite_eq_left (by omega : 2 * w.length + 1 + (q - (2 * w.length + 1)) <
          2 * w.length + 1 + j)]
      · simp only [List.getElem?_replicate, ite_eq_right hj]
        simp only [ite_eq_right (by omega : ¬ 2 * w.length + 1 + (q - (2 * w.length + 1)) <
          2 * w.length + 1 + j)]

def machine (D : Desc) (C d : ℕ) : QueryMachine State where
  init := scanState D 0
  query s := if s.1 then (Native.machine D).query s.2.2.2 / 2 else s.2.1
  next p :=
    if p.1.1 then
      if (Native.machine D).halted p.1.2.2.2 then
        itemState p.1.2.1 (p.1.2.2.1 + 1) (init D)
      else itemState p.1.2.1 p.1.2.2.1 ((Native.machine D).next
        (p.1.2.2.2, symbol p.1.2.1 p.1.2.2.1 ((Native.machine D).query p.1.2.2.2) p.2))
    else if p.2.isSome then scanState D (p.1.2.1 + 1)
      else itemState p.1.2.1 0 (init D)
  emit p := if p.1.1 && !(Native.machine D).halted p.1.2.2.2 then
    (Native.machine D).emit
      (p.1.2.2.2, symbol p.1.2.1 p.1.2.2.1 ((Native.machine D).query p.1.2.2.2) p.2)
    else []
  halted s := s.1 && decide (count C d s.2.1 ≤ s.2.2.1)
  finish _ := []

theorem scan_step (D : Desc) (C d : ℕ) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (machine D C d).step w (scanState D i) = scanState D (i + 1) := by
  simp [QueryMachine.step, QueryMachine.read, machine, scanState,
    List.getElem?_eq_getElem hi]

theorem scan_end (D : Desc) (C d : ℕ) (w : List Bool) :
    (machine D C d).step w (scanState D w.length) = itemState w.length 0 (init D) := by
  simp [QueryMachine.step, QueryMachine.read, machine, scanState]

theorem item_live (D : Desc) (C d n j : ℕ) (q : SCfg) (hj : j < count C d n) :
    (machine D C d).halted (itemState n j q) = false := by
  simp [machine, itemState, show ¬count C d n ≤ j by omega]

theorem item_step (D : Desc) (C d : ℕ) (w : List Bool) (j : ℕ) (q : SCfg)
    (hj : j < count C d w.length) (hq : (Native.machine D).halted q = false) :
    (machine D C d).step w (itemState w.length j q) =
      itemState w.length j ((Native.machine D).step (frame w ++ List.replicate j true) q) := by
  rw [QueryMachine.step, item_live D C d w.length j q hj]
  simp only [Bool.false_eq_true, ↓reduceIte, machine, itemState, hq,
    QueryMachine.read, QueryMachine.step, symbol_correct]

theorem item_emit (D : Desc) (C d : ℕ) (w : List Bool) (j : ℕ) (q : SCfg)
    (hq : (Native.machine D).halted q = false) :
    (machine D C d).emit (itemState w.length j q,
      (machine D C d).read w (itemState w.length j q)) =
      (Native.machine D).emit (q,
        (Native.machine D).read (frame w ++ List.replicate j true) q) := by
  simp only [machine, itemState, hq, Bool.not_false, Bool.true_and,
    ↓reduceIte, QueryMachine.read, symbol_correct]

theorem item_return (D : Desc) (C d : ℕ) (w : List Bool) (j : ℕ) (q : SCfg)
    (hj : j < count C d w.length) (hq : (Native.machine D).halted q = true) :
    (machine D C d).step w (itemState w.length j q) =
      itemState w.length (j + 1) (init D) := by
  rw [QueryMachine.step, item_live D C d w.length j q hj]
  simp only [Bool.false_eq_true, ↓reduceIte, machine, itemState, hq]

end PredictionDepth.StandardComplexity.LogspaceBatch
