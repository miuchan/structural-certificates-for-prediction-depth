import PredictionDepth.SparseCorrections.Collision
import PredictionDepth.SparseCorrections.Reconstruction

/-!
# Forced streaming

For a fixed output coordinate, its characteristic meets the initial layer
once and each earlier forcing layer once. All of these coordinates lie in
the common cone, and the result is the parity of exactly those wires.
-/

namespace PredictionDepth.SparseCorrections.Streaming

open Collision Linear
open scoped BigOperators

/-- Displacement of the source read in the preceding layer. -/
def drift : Fin 3 → ℤ := ![-1, 1, 0]

def source (t s : ℕ) (i : ℤ) (a : Fin 3) : ℤ :=
  i + ((t - s : ℕ) : ℤ) * drift a

theorem source_in_window {T t s : ℕ} (hst : s ≤ t) (ht : t ≤ T)
    {i : ℤ} (hi : Cone.InWindow 1 T t i) (a : Fin 3) :
    Cone.InWindow 1 T s (source t s i a) := by
  simp only [Cone.InWindow, Cone.radius, one_mul] at hi ⊢
  fin_cases a <;> simp [source, drift] <;> omega

theorem source_step {t s : ℕ} (hst : s ≤ t) (i : ℤ) (a : Fin 3) :
    source t s (i + drift a) a = source (t + 1) s i a := by
  fin_cases a <;> simp [source, drift] <;> omega

@[simp] theorem source_self (t : ℕ) (i : ℤ) (a : Fin 3) :
    source t t i a = i := by simp [source]

abbrev Width (T : ℕ) := coneWidth 3 1 T

def initWire {T t : ℕ} (ht : t ≤ T) {i : ℤ} (hi : Cone.InWindow 1 T t i) (a : Fin 3) :
    Fin (Width T 0) :=
  Cone.encodeBit 3 1 T 0 (source t 0 i a) (source_in_window (Nat.zero_le t) ht hi a) a

def eventWire {T t : ℕ} (ht : t ≤ T) {i : ℤ} (hi : Cone.InWindow 1 T t i) (a : Fin 3)
    (s : Fin t) : Event (Width T) T :=
  ⟨⟨s.val, by omega⟩, Cone.encodeBit 3 1 T (s.val + 1) (source t (s.val + 1) i a)
    (source_in_window (Nat.succ_le_of_lt s.isLt) ht hi a) a⟩

theorem bitStream_read (x : Cone.Config 3) (i : ℤ) (a : Fin 3) :
    bitStream x i a = x (i + drift a) a := by
  fin_cases a <;> simp [bitStream, Collision.lift, stream, Cell.bits, Cell.ofBits, drift, sub_eq_add_neg]

theorem stepSource_in_window {T t : ℕ} (ht : t < T) {i : ℤ}
    (hi : Cone.InWindow 1 T (t + 1) i) (a : Fin 3) :
    Cone.InWindow 1 T t (i + drift a) := by
  apply Cone.predecessor_in_window ht hi
  all_goals fin_cases a <;> simp [drift]
  all_goals omega

theorem finiteStream_read {T t : ℕ} (ht : t < T)
    (u : Layer (Width T) t) (i : ℤ) (hi : Cone.InWindow 1 T (t + 1) i) (a : Fin 3) :
    Cone.transition 1 T bitStream t u (Cone.encodeBit 3 1 T (t + 1) i hi a) =
      u (Cone.encodeBit 3 1 T t (i + drift a) (stepSource_in_window ht hi a) a) := by
  rw [Cone.transition, Cone.restrict_encodeBit, bitStream_read]
  simp [Cone.extend, stepSource_in_window ht hi a]

private theorem xor_to_add (a b : Bool) :
    (toBoolRing (Bool.xor a b) : F₂) = toBoolRing a + toBoolRing b := by
  rw [← Linear.addGate_eq_xor, Linear.addGate_ring]

/-- The forced response at a coordinate is the parity along its characteristic. -/
theorem forcedLayer_eq_characteristic {T : ℕ}
    (u : Layer (Width T) 0) (e : Residual (Width T) T)
    (t : ℕ) (ht : t ≤ T) (i : ℤ) (hi : Cone.InWindow 1 T t i) (a : Fin 3) :
    toBoolRing (forcedLayer (Cone.transition 1 T bitStream) u e t ht
      (Cone.encodeBit 3 1 T t i hi a)) =
      toBoolRing (u (initWire ht hi a)) + ∑ s : Fin t, toBoolRing (e (eventWire ht hi a s)) := by
  induction t generalizing i with
  | zero =>
    have h : initWire ht hi a = Cone.encodeBit 3 1 T 0 i hi a :=
      Cone.encodeBit_eq_iff.mpr ⟨source_self _ _ _, rfl⟩
    simp [forcedLayer, h]
  | succ t ih =>
    have hlt : t < T := by omega
    let j := i + drift a
    have hj : Cone.InWindow 1 T t j := stepSource_in_window hlt hi a
    change toBoolRing (Bool.xor
        (Cone.transition 1 T bitStream t (forcedLayer (Cone.transition 1 T bitStream) u e t
          hlt.le) (Cone.encodeBit 3 1 T (t + 1) i hi a))
        (e ⟨⟨t, hlt⟩, Cone.encodeBit 3 1 T (t + 1) i hi a⟩)) = _
    rw [xor_to_add, finiteStream_read hlt, ih hlt.le j hj, Fin.sum_univ_castSucc, ← add_assoc]
    have h₁ : initWire hlt.le hj a = initWire ht hi a :=
      Cone.encodeBit_eq_iff.mpr ⟨source_step (Nat.zero_le t) i a, rfl⟩
    have h₂ (s : Fin t) : eventWire hlt.le hj a s = eventWire ht hi a s.castSucc := by
      refine Sigma.ext ?_ ?_
      · rfl
      apply heq_of_eq
      exact Cone.encodeBit_eq_iff.mpr ⟨source_step (Nat.succ_le_of_lt s.isLt) i a, rfl⟩
    have h₃ : eventWire ht hi a (Fin.last t) =
        ⟨⟨t, hlt⟩, Cone.encodeBit 3 1 T (t + 1) i hi a⟩ := by
      refine Sigma.ext ?_ ?_
      · rfl
      apply heq_of_eq
      exact Cone.encodeBit_eq_iff.mpr ⟨source_self _ _ _, rfl⟩
    simp only [h₁, h₂, h₃]

theorem forcedTrajectory_eq_characteristic {T : ℕ}
    (u : Layer (Width T) 0) (e : Residual (Width T) T)
    (t : Fin (T + 1)) (i : ℤ) (hi : Cone.InWindow 1 T t.val i) (a : Fin 3) :
    toBoolRing (forcedTrajectory (Cone.transition 1 T bitStream) u e t
      (Cone.encodeBit 3 1 T t.val i hi a)) =
      toBoolRing (u (initWire (by omega) hi a)) +
        ∑ s : Fin t.val, toBoolRing (e (eventWire (by omega) hi a s)) :=
  forcedLayer_eq_characteristic u e t.val (by omega) i hi a

end PredictionDepth.SparseCorrections.Streaming
