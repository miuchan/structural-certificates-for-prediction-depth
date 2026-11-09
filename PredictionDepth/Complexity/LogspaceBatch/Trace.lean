import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Call

/-! Bounded streaming traces, with no accumulated output in the machine state. -/

namespace PredictionDepth.StandardComplexity.LogspaceBatch

open Turing

variable {σ : Type} (M : QueryMachine σ) (w : List Bool) (Inv : σ → Prop)

/-- A finite run together with its emitted word and a bound on every saved state.
The output word is a proof specification; it is never a component of `σ`. -/
structure Trace (start finish : σ) (out : List Bool) where
  time : ℕ
  reaches : M.runFrom w start time = finish
  live : ∀ i < time, M.halted (M.runFrom w start i) = false
  bounded : ∀ i ≤ time, Inv (M.runFrom w start i)
  emits : (List.range time).flatMap
    (fun i => M.emit (M.runFrom w start i, M.read w (M.runFrom w start i))) = out

namespace Trace

variable {M w Inv}

def refl (s : σ) (hs : Inv s) : Trace M w Inv s s [] where
  time := 0
  reaches := rfl
  live := by intro i hi; omega
  bounded := by
    intro i hi
    have : i = 0 := by omega
    simpa [this] using hs
  emits := rfl

def single (s : σ) (hs : Inv s) (hlive : M.halted s = false)
    (hnext : Inv (M.step w s)) :
    Trace M w Inv s (M.step w s) (M.emit (s, M.read w s)) where
  time := 1
  reaches := rfl
  live := by
    intro i hi
    have : i = 0 := by omega
    simpa [this] using hlive
  bounded := by
    intro i hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
    · exact hs
    · exact hnext
  emits := by simp

theorem finish_bounded {s t : σ} {out : List Bool} (h : Trace M w Inv s t out) : Inv t := by
  rw [← h.reaches]
  exact h.bounded _ le_rfl

def trans {s t u : σ} {a b : List Bool}
    (h : Trace M w Inv s t a) (h' : Trace M w Inv t u b) : Trace M w Inv s u (a ++ b) where
  time := h.time + h'.time
  reaches := by rw [QueryMachine.runFrom_add, h.reaches, h'.reaches]
  live := by
    intro i hi
    by_cases hlt : i < h.time
    · exact h.live i hlt
    · have he : i = h.time + (i - h.time) := by omega
      rw [he, QueryMachine.runFrom_add, h.reaches]
      exact h'.live _ (by omega)
  bounded := by
    intro i hi
    by_cases hle : i ≤ h.time
    · exact h.bounded i hle
    · have he : i = h.time + (i - h.time) := by omega
      rw [he, QueryMachine.runFrom_add, h.reaches]
      exact h'.bounded _ (by omega)
  emits := by
    rw [List.range_add, List.flatMap_append, List.flatMap_map, h.emits]
    congr 1
    simpa only [Function.comp_def, QueryMachine.runFrom_add, h.reaches] using h'.emits

def congr {s t t' : σ} {a a' : List Bool} (h : Trace M w Inv s t a)
    (ht : t = t') (ha : a = a') : Trace M w Inv s t' a' := ht ▸ ha ▸ h

theorem output {s t : σ} {out : List Bool} (h : Trace M w Inv s t out) :
    ({M with init := s} : QueryMachine σ).output w h.time = out ++ M.finish t := by
  rw [QueryMachine.output_eq_of_not_halted]
  · change ((List.range h.time).map
        (fun i => M.emit (M.runFrom w s i, M.read w (M.runFrom w s i)))).flatten ++
          M.finish (M.runFrom w s h.time) = _
    rw [← List.flatMap_def, h.emits, h.reaches]
  · exact h.live

end Trace
end PredictionDepth.StandardComplexity.LogspaceBatch
