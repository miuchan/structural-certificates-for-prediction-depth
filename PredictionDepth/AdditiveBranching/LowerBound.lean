import PredictionDepth.AdditiveBranching.Summary
import CslibFrontier.Computability.Circuit.FanIn

/-! Fixing the initial control at the origin to one and the others to zero
makes the origin's data observation the parity of its entire data window. -/

namespace PredictionDepth.AdditiveBranching

open Cslib Cslib.Circuits
open FastComposition (Bits)
open FrozenPascal (bit bit_ofBoolRing extendTrack extendTrack_fin)
open Linear (F₂)
open scoped BigOperators

private def parityControl (i : ℤ) : F₂ := if i = 0 then 1 else 0

private def parityConfig (v : Bits (T + 1)) : FrozenPascal.Config F₂ :=
  (parityControl, fun i => bit (extendTrack v i))

private theorem coefficient_parityControl {T k : ℕ} (hk : k ≤ T) :
    coefficient parityControl 0 T k = 1 := by
  rcases lt_or_eq_of_le hk with h | rfl
  · have hSuffix : zeroSuffix parityControl 0 T k = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      have hj0 : j ≠ 0 := Nat.ne_of_gt ((Finset.mem_Ioo.mp hj).1.trans_le' (Nat.zero_le k))
      simp [parityControl, hj0]
    have hParity : trimmedParity parityControl 0 T = 1 := by
      rw [trimmedParity_eq_sum,
        Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr ((Nat.zero_le k).trans_lt h))]
      · simp [parityControl]
      · intro j _ hj
        simp [parityControl, hj]
    simp [coefficient, h, hSuffix, hParity]
  · simp

private theorem iterate_data_parity (v : Bits (T + 1)) :
    ((step^[T]) (parityConfig v)).2 0 = ∑ j, bit (v j) := by
  rw [iterate_data, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [parityConfig, coefficient_parityControl (Nat.le_of_lt_succ j.isLt)]

/-- The data wires of the interleaved window, including the bypassed terminal datum. -/
private def dataWire (j : Fin (T + 1)) : Fin (InputWidth T) :=
  Fin.lastCases (terminalWire T) (fun k => siteWire k 1) j

private theorem dataWire_injective : Function.Injective (dataWire (T := T)) := by
  have hindex (j : Fin (T + 1)) :
      (dataWire j).val = if j.val = T then 2 * T else 2 * j.val + 1 := by
    refine Fin.lastCases (by simp [dataWire, terminalWire]) (fun k => ?_) j
    simp [dataWire, siteWire, Nat.ne_of_lt k.isLt]
  intro i j h
  have hval := congrArg Fin.val h
  rw [hindex i, hindex j] at hval
  exact Fin.ext (by split at hval <;> split at hval <;> omega)

private theorem parity_samples_agree {T : ℕ} {u v : Bits (T + 1)} {i : Fin (T + 1)}
    (h : ∀ j, j ≠ i → u j = v j) (k : Fin (InputWidth T)) (hk : k ≠ dataWire i) :
    sample T (parityConfig u) k = sample T (parityConfig v) k := by
  by_cases hterminal : k.val = 2 * T
  · have he : k = terminalWire T := Fin.ext hterminal
    subst k
    have hne : Fin.last T ≠ i := fun h' => hk (by simp [← h', dataWire])
    simp only [sample_terminal, parityConfig]
    change ofBoolRing (bit (extendTrack u ((Fin.last T).val : ℤ))) = _
    rw [extendTrack_fin]
    change ofBoolRing (bit (u (Fin.last T))) =
      ofBoolRing (bit (extendTrack v ((Fin.last T).val : ℤ)))
    rw [extendTrack_fin, h _ hne]
  · by_cases hcontrol : k.val % 2 = 0
    · simp [sample, hterminal, hcontrol, parityConfig]
    · have hlt := k.isLt
      let j : Fin T := ⟨k.val / 2, by unfold InputWidth at hlt; omega⟩
      have he : k = siteWire j 1 := Fin.ext (by
        change k.val = 2 * (k.val / 2) + 1
        omega)
      rw [he] at hk ⊢
      have hne : j.castSucc ≠ i := fun h' => hk (by simp [← h', dataWire])
      simp only [sample_site, parityConfig]
      change ofBoolRing (bit (extendTrack u (j.castSucc.val : ℤ))) =
        ofBoolRing (bit (extendTrack v (j.castSucc.val : ℤ)))
      rw [extendTrack_fin, extendTrack_fin, h _ hne]

/-- Every correct predictor in the explicit window encoding has logarithmic
depth with fan-in at most two, regardless of gate basis or sharing. -/
theorem prediction_depth_lower_bound {σ : Signature} (I : Interpretation σ Bool)
    (T : ℕ) (c : Circuit σ (InputWidth T) 1) (hFan : c.FanInAtMost 2)
    (hc : ∀ x : FrozenPascal.Config F₂,
      c.eval I (sample T x) 0 = ofBoolRing ((step^[T] x).2 0)) :
    Nat.clog 2 (T + 1) ≤ c.depth := by
  let wires : Fin (T + 1) ↪ Fin (InputWidth T) := ⟨dataWire, dataWire_injective⟩
  have hParity (v : Bits (T + 1)) :
      bit (c.eval I (sample T (parityConfig v)) 0) = ∑ j, bit (v j) := by
    rw [hc, bit_ofBoolRing, iterate_data_parity]
  have hEssential (i : Fin (T + 1)) : EssentialAt (c.eval I) (wires i) := by
    let u : Bits (T + 1) := fun _ => false
    let v : Bits (T + 1) := fun j => decide (j = i)
    refine ⟨sample T (parityConfig u), sample T (parityConfig v),
      parity_samples_agree (fun j hj => by simp [u, v, hj]), ?_⟩
    intro h
    have hp := congrArg (fun b : Bits 1 => bit (b 0)) h
    change bit (c.eval I (sample T (parityConfig u)) 0) =
      bit (c.eval I (sample T (parityConfig v)) 0) at hp
    have hv : (∑ j, bit (v j)) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [v, hj]
      · simp
    rw [hParity, hParity, hv] at hp
    simp [u] at hp
  have h := c.essential_le_depth (show c.Computes I (c.eval I) from fun _ => rfl)
    (selected := Finset.univ.map wires)
    (fun k hk => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hk
      exact hEssential i) hFan
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
  simpa using h

end PredictionDepth.AdditiveBranching
