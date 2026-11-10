import PredictionDepth.SparseCorrections.Semantics
import PredictionDepth.Linear
import Mathlib.LinearAlgebra.Pi

/-!
# Rectangular linear responses

An interval propagator composes linear transitions across their respective
layer widths. The full response sums the autonomous term and one propagated
impulse for each earlier update.
-/

namespace PredictionDepth.SparseCorrections

open Linear (F₂)
open scoped BigOperators

abbrev RingLayer (w : ℕ → ℕ) (t : ℕ) := Fin (w t) → F₂
abbrev LinearTransition (w : ℕ → ℕ) :=
  (t : ℕ) → RingLayer w t →ₗ[F₂] RingLayer w (t + 1)

variable {w : ℕ → ℕ} {T : ℕ}

def boolReference (L : LinearTransition w) : Transition w :=
  fun t u i => ofBoolRing (L t (fun j => toBoolRing (u j)) i)

/-- Interval propagators are zero for reversed intervals. -/
def propagator (L : LinearTransition w) (s : ℕ) :
    (t : ℕ) → RingLayer w s →ₗ[F₂] RingLayer w t
  | 0 => if h : s = 0 then h ▸ LinearMap.id else 0
  | t + 1 =>
    if h : s = t + 1 then h ▸ LinearMap.id else (L t).comp (propagator L s t)

@[simp] theorem propagator_diag (L : LinearTransition w) (s : ℕ) :
    propagator L s s = LinearMap.id := by
  cases s <;> simp [propagator]

theorem propagator_succ (L : LinearTransition w) {s t : ℕ} (h : s ≤ t) :
    propagator L s (t + 1) = (L t).comp (propagator L s t) := by
  have hne : s ≠ t + 1 := by omega
  simp [propagator, hne]

theorem propagator_comp (L : LinearTransition w) {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    (propagator L s t).comp (propagator L r s) = propagator L r t := by
  induction t, hst using Nat.le_induction with
  | base => simp
  | succ t hst ih =>
    rw [propagator_succ L hst, propagator_succ L (hrs.trans hst), LinearMap.comp_assoc, ih]

def forcingAt (e : Residual w T) (s : ℕ) : RingLayer w (s + 1) :=
  fun i => if h : s < T then toBoolRing (e ⟨⟨s, h⟩, i⟩) else 0

@[simp] theorem forcingAt_lt (e : Residual w T) {s : ℕ} (h : s < T) (i : Fin (w (s + 1))) :
    forcingAt e s i = toBoolRing (e ⟨⟨s, h⟩, i⟩) := by simp [forcingAt, h]

private theorem toBoolRing_xor (a b : Bool) :
    (toBoolRing (Bool.xor a b) : F₂) = toBoolRing a + toBoolRing b := by
  cases a <;> cases b <;> rfl

/-- The forced recurrence reconstructed by the sum of all interval responses. -/
theorem forcedLayer_eq_propagator_sum (L : LinearTransition w) (u : Layer w 0)
    (e : Residual w T) (t : ℕ) (ht : t ≤ T) :
    (fun i => toBoolRing (forcedLayer (boolReference L) u e t ht i)) =
      propagator L 0 t (fun j => toBoolRing (u j)) +
        ∑ s ∈ Finset.range t, propagator L (s + 1) t (forcingAt e s) := by
  induction t with
  | zero => simp [forcedLayer]
  | succ t ih =>
    have hlt : t < T := by omega
    have hrec :
        (fun i => toBoolRing (forcedLayer (boolReference L) u e (t + 1) ht i)) =
          L t (fun i => toBoolRing (forcedLayer (boolReference L) u e t (by omega) i)) +
            forcingAt e t := by
      funext i
      simp [forcedLayer, boolReference, toBoolRing_xor, hlt]
    rw [hrec, ih (by omega), map_add, map_sum, Finset.sum_range_succ,
      propagator_diag, LinearMap.id_apply, ← add_assoc, propagator_succ L (Nat.zero_le t)]
    congr 2
    apply Finset.sum_congr rfl
    intro s hs
    rw [propagator_succ L (Nat.succ_le_of_lt (Finset.mem_range.mp hs))]
    rfl

theorem forcedTrajectory_eq_propagator_sum (L : LinearTransition w) (u : Layer w 0)
    (e : Residual w T) (t : Fin (T + 1)) :
    (fun i => toBoolRing (forcedTrajectory (boolReference L) u e t i)) =
      propagator L 0 t.val (fun j => toBoolRing (u j)) +
        ∑ s ∈ Finset.range t.val, propagator L (s + 1) t.val (forcingAt e s) :=
  forcedLayer_eq_propagator_sum L u e t.val (by omega)

end PredictionDepth.SparseCorrections
