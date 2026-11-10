import PredictionDepth.SparseCorrections.Streaming
import Mathlib.Data.Set.Card

/-!
# Particle conservation and the two reflectors

Collision permutes tracks at a site, and streaming permutes space-track
coordinates. Removing either reflector makes the returning observation vanish.
-/

namespace PredictionDepth.SparseCorrections.Collision

def occupied (x : Config) : Set (ℤ × Fin 3) :=
  {p | (x p.1).bits p.2 = true}

private def trackCycle : Fin 3 ≃ Fin 3 where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by intro a; fin_cases a <;> rfl

private def collisionTrack (x : Cell) : Fin 3 ≃ Fin 3 :=
  if particles x = 2 then trackCycle else Equiv.refl _

private theorem collide_read (x : Cell) (a : Fin 3) :
    (collide x).bits a = x.bits (collisionTrack x a) := by
  rcases x with ⟨a₀, b₀, c₀⟩
  cases a₀ <;> cases b₀ <;> cases c₀ <;> fin_cases a <;> rfl

private def collisionSource (x : Config) : ℤ × Fin 3 ≃ ℤ × Fin 3 where
  toFun p := (p.1, collisionTrack (x p.1) p.2)
  invFun p := (p.1, (collisionTrack (x p.1)).symm p.2)
  left_inv := by intro p; simp
  right_inv := by intro p; simp

private def streamSource : ℤ × Fin 3 ≃ ℤ × Fin 3 where
  toFun p := (p.1 + Streaming.drift p.2, p.2)
  invFun p := (p.1 - Streaming.drift p.2, p.2)
  left_inv := by intro p; simp
  right_inv := by intro p; simp

private theorem occupied_collide (x : Config) :
    occupied (collide ∘ x) = collisionSource x ⁻¹' occupied x := by
  ext p
  exact iff_of_eq (congrArg (· = true) (collide_read (x p.1) p.2))

private theorem occupied_stream (x : Config) :
    occupied (stream x) = streamSource ⁻¹' occupied x := by
  ext p
  change (stream x p.1).bits p.2 = true ↔ (x (p.1 + Streaming.drift p.2)).bits p.2 = true
  have h := Streaming.bitStream_read (Cell.bits ∘ x) p.1 p.2
  rw [bitStream, lift_bits] at h
  exact iff_of_eq (congrArg (· = true) h)

/-- A collision-and-streaming update preserves both finiteness and particle count. -/
theorem preserves_population (x : Config) (hx : (occupied x).Finite) :
    (occupied (step x)).Finite ∧ (occupied (step x)).ncard = (occupied x).ncard := by
  rw [step, occupied_stream, occupied_collide, ← Equiv.image_symm_eq_preimage,
    ← Equiv.image_symm_eq_preimage]
  exact ⟨(hx.image _).image _, (Set.ncard_image_of_injective _ streamSource.symm.injective).trans
    (Set.ncard_image_of_injective _ (collisionSource x).symm.injective)⟩

theorem collision_discrepancy_count (x : Cell) :
    particles ((collide x).xor x) = if particles x = 2 then 2 else 0 := by
  rcases x with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

private def mark (i j : ℤ) : Bool := decide (i = j)

def withoutNear (ell t : ℕ) : Config :=
  fun i => ⟨mark i t, false, mark i (-(ell : ℤ))⟩

private def noFar (t : ℕ) : Config :=
  fun i => ⟨false, mark i (-(t : ℤ)), mark i 0⟩

private theorem withoutNear_step {ell : ℕ} (hell : 0 < ell) (t : ℕ) :
    step (withoutNear ell t) = withoutNear ell (t + 1) := by
  have h (i : ℤ) : collide (withoutNear ell t i) = withoutNear ell t i := by
    by_cases ha : i = (t : ℤ)
    · have hc : i ≠ -(ell : ℤ) := by omega
      simp [withoutNear, mark, ha, show (t : ℤ) ≠ -(ell : ℤ) by omega, collide]
    · simp only [withoutNear, mark, ha, decide_false]
      cases decide (i = -(ell : ℤ)) <;> rfl
  have he : collide ∘ withoutNear ell t = withoutNear ell t := funext h
  rw [step, he]
  funext i
  simp [stream, withoutNear, mark, show i - 1 = (t : ℤ) ↔ i = (t : ℤ) + 1 by omega]

private theorem noFar_step {t : ℕ} (ht : 0 < t) :
    step (noFar t) = noFar (t + 1) := by
  have h (i : ℤ) : collide (noFar t i) = noFar t i := by
    by_cases hb : i = -(t : ℤ)
    · simp [noFar, mark, hb, Nat.ne_of_gt ht, collide]
    · simp only [noFar, mark, hb, decide_false]
      cases decide (i = 0) <;> rfl
  have he : collide ∘ noFar t = noFar t := funext h
  rw [step, he]
  funext i
  simp [stream, noFar, mark, show i + 1 = -(t : ℤ) ↔ i = -((t : ℤ) + 1) by omega]

/-- Removing the reflector at zero lets the initial right-moving particle continue right. -/
theorem without_near_reflector {ell : ℕ} (hell : 0 < ell) :
    (((step^[2 * ell]) (withoutNear ell 0)) 0).a = false := by
  have h (t : ℕ) : ((step^[t]) (withoutNear ell 0)) = withoutNear ell t := by
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', ih, withoutNear_step hell]
  rw [h]
  simp [withoutNear, mark, Nat.ne_of_gt hell]

/-- With only the reflector at zero, the initial collision sends a particle left forever. -/
theorem without_far_reflector {ell : ℕ} (hell : 0 < ell) :
    (((step^[2 * ell]) (initial 0)) 0).a = false := by
  have h (t : ℕ) (ht : 0 < t) : ((step^[t]) (initial 0)) = noFar t := by
    induction t with
    | zero => omega
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      by_cases hz : t = 0
      · subst t
        rw [Function.iterate_zero_apply, step_initial]
        funext i
        change (⟨false, mark i (-1), mark i 0 || mark i 0⟩ : Cell) = ⟨false, mark i (-1), mark i 0⟩
        rw [Bool.or_self]
      · rw [ih (by omega), noFar_step (by omega)]
  rw [h _ (by omega)]
  rfl

end PredictionDepth.SparseCorrections.Collision
