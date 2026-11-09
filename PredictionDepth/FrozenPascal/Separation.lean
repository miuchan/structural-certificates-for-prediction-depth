import PredictionDepth.FrozenPascal.GuardRules

/-! Positive-time examples that distinguish the path and global decoder contracts. -/

namespace PredictionDepth.FrozenPascal

open FastComposition
open Linear (F₂)
open scoped BigOperators

def pulse : Config (Bool × Bool) :=
  (fun _ => (true, true), fun j => if j = 1 then 1 else 0)

def pulseInput (m : ℕ) : Bits (InputWidth m) := sample Prod.fst Prod.snd pulse m

theorem pulse_data (hm : 1 < m) (j : ℕ) :
    (initial (pulseInput m)).2 (j : ℤ) = if j = 1 then 1 else 0 := by
  by_cases hj : j < m
  · have h := extendTrack_fin (pulseInput m ∘ dataWire) (⟨j, hj⟩ : Fin m)
    change bit (extendTrack (pulseInput m ∘ dataWire) (j : ℤ)) = _
    rw [h]
    change bit (sample Prod.fst Prod.snd pulse m (dataWire ⟨j, hj⟩)) = _
    simp only [sample_data, bit_ofBoolRing]
    simp [pulse]
  · have hne : j ≠ 1 := by omega
    simp [initial, extendTrack, hj, hne]

theorem pulse_value (hm : 1 < m) (ht : 1 ≤ t) :
    ((step Prod.fst Prod.snd)^[t] (initial (pulseInput m))).2 0 = (t : F₂) := by
  rw [iterate_data]
  rw [Finset.sum_eq_single 1]
  · rw [show (0 : ℤ) + ↑(1 : ℕ) = ↑(1 : ℕ) by simp, pulse_data hm,
      ite_eq_left rfl, mul_one, pulseInput, sample_coefficient Prod.fst Prod.snd pulse hm]
    simp [coefficient, ht, pulse, enabled, edgeProduct, Nat.sub_add_cancel ht]
  · intro j _ hj
    rw [zero_add, pulse_data hm, ite_eq_right hj, mul_zero]
  · intro h
    exfalso
    exact h (Finset.mem_range.mpr (by omega))

theorem register_overflow (x : Bits (InputWidth m)) {u v : ℕ} (hu : m ≤ u) (hv : m ≤ v) :
    register m u x = register m v x := by
  unfold register
  congr 1
  funext i
  have hi := i.isLt
  have h₁ : i.val ≠ u := by omega
  have h₂ : i.val ≠ v := by omega
  simp [timeTag, h₁, h₂]

/-- For every positive prediction window, the truncated tags used by the
witness cannot support a decoder correct at every time on the same inputs. -/
theorem no_global_decoder (hm : 1 < m) :
    ¬ ∃ decode : Bits (RegisterWidth m) → Bool, ∀ u x,
      decode (register m u x) = observe ((step Prod.fst Prod.snd)^[u] (initial x)) := by
  rintro ⟨decode, hd⟩
  have hm₁ : 1 ≤ m := by omega
  have hm₂ : 1 ≤ m + 1 := by omega
  have he := hd m (pulseInput m)
  rw [register_overflow (pulseInput m) (le_refl m) (Nat.le_succ m), hd (m + 1) (pulseInput m)] at he
  have hc := congrArg bit he
  simp only [observe, bit_ofBoolRing, pulse_value hm hm₁, pulse_value hm hm₂, Nat.cast_add,
    Nat.cast_one] at hc
  have hz : (0 : F₂) = 1 := add_left_cancel (by simpa only [add_zero] using hc.symm)
  have hf : false = true := congrArg ofBoolRing hz
  cases hf

/-- A concrete nonaffine member has four control symbols. The stay guard is AND
and the hop guard is OR. Both coefficients are active on some symbols. -/
theorem and_or_rule_nonaffine :
    ¬ ∃ (g : Bits 2 → F₂) (c d : F₂), ∀ a v u,
      bit (a 0 && a 1) * v + bit (a 0 || a 1) * u = g a + c * v + d * u := by
  rintro ⟨g, c, d, h⟩
  apply nonaffine_local (fun a : Bits 2 => a 0 && a 1)
    (fun _ => false) (fun _ => true) rfl rfl
  exact ⟨g, c, fun a v => by simpa using h a v 0⟩

end PredictionDepth.FrozenPascal
