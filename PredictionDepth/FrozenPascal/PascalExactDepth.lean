import PredictionDepth.FrozenPascal.HomogeneousPascal
import CslibFrontier.Computability.Circuit.Boolean.KhrapchenkoDepth
import CslibFrontier.Computability.Circuit.Boolean.NegationNormalForm
import CslibFrontier.Computability.Circuit.Unfolding

/-! Exact pointwise depth for the homogeneous Pascal rule over De Morgan gates.
The uniform generator uses a separate, regular parity network. -/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open Linear (F₂)
open scoped BigOperators

private noncomputable def supportEquiv (T : ℕ) :
    Fin (2 ^ T.bitIndices.length) ≃ ↑(pascalSupport T) :=
  ((pascalSupport T).equivFinOfCardEq (pascalSupport_card T)).symm

private noncomputable def supportWire (q T : ℕ) :
    Fin (2 ^ T.bitIndices.length) ↪ Fin (RawWidth q (T + 1)) where
  toFun i := rawDataWire (supportEquiv T i).val
  inj' _ _ h := (supportEquiv T).injective (Subtype.ext
    (Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))))

private theorem support_parity (q T : ℕ) (u : Bits (RawWidth q (T + 1))) :
    bit (Cslib.parity (2 ^ T.bitIndices.length) (u ∘ supportWire q T)) =
      ∑ i ∈ pascalSupport T, bit (u (rawDataWire i)) := by
  let toBit : Bool →+ F₂ := ⟨⟨bit, rfl⟩, fun a b => by rw [Bool.add_eq_xor]; exact bit_xor a b⟩
  change toBit _ = _
  rw [Cslib.parity, parityOn_eq_sum, map_sum, ← Finset.sum_coe_sort (s := pascalSupport T)]
  exact Fintype.sum_equiv (supportEquiv T)
    (fun i => bit (u (supportWire q T i)))
    (fun i => bit (u (rawDataWire i.val))) (fun _ => rfl)

private theorem parity_not_monotone {n : ℕ} (hn : 2 ≤ n) : ¬ Monotone (Cslib.parity n) := by
  intro h
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let a : Bits n := fun _ => false
  let b : Bits n := Function.update a i true
  let c : Bits n := Function.update b j true
  have ha : Cslib.parity n a = false := map_zero (parityOnAddMonoidHom _)
  have hb : Cslib.parity n b = true := by
    change Cslib.parity n (Function.update a i !a i) = true
    simp [parity_update_not, ha]
  have hji : j ≠ i := fun heq => (by decide : (1 : ℕ) ≠ 0) (congrArg Fin.val heq)
  have hj : b j = false := by simp [b, a, hji]
  have hc : Cslib.parity n c = false := by
    simpa [hj, hb, c] using parity_update_not b j
  have hbc : b ≤ c := fun k => by by_cases hk : k = j <;> simp [c, hk]
  have hle := h hbc
  rw [hb, hc] at hle
  exact (by decide : ¬ true ≤ false) hle

/-- Equality in the binary leaf bound forces every internal node to be binary. -/
private theorem formula_monotone_of_full_leaves (F : Formula signature n)
    (h : 2 ^ F.depth ≤ F.leafSize) : Monotone (F.eval interpretation) := by
  induction F with
  | input i => exact fun _ _ hxy => hxy i
  | gate op args ih =>
    let d := Finset.univ.sup fun j => (args j).depth
    have hcap (j : Fin (signature.Arity op)) : (args j).leafSize ≤ 2 ^ d :=
      ((args j).leafSize_le_pow_depth Boolean.arity_le_two).trans
        (Nat.pow_le_pow_right (by decide)
          (Finset.le_sup (f := fun j => (args j).depth) (Finset.mem_univ j)))
    have hd (j : Fin (signature.Arity op)) : 2 ^ (args j).depth ≤ 2 ^ d :=
      Nat.pow_le_pow_right (by decide)
        (Finset.le_sup (f := fun j => (args j).depth) (Finset.mem_univ j))
    change 2 ^ (d + 1) ≤ ∑ j, (args j).leafSize at h
    rw [pow_succ] at h
    cases op with
    | const b =>
      simp at h
    | not =>
      rw [Fin.sum_univ_one] at h
      have harg := hcap 0
      have hp : 0 < 2 ^ d := pow_pos (by decide) _
      omega
    | and | or =>
      rw [Fin.sum_univ_two] at h
      have h₀ := ih 0 ((hd 0).trans (by have := hcap 1; omega))
      have h₁ := ih 1 ((hd 1).trans (by have := hcap 0; omega))
      intro x y hxy
      have le₀ := h₀ hxy
      have le₁ := h₁ hxy
      simp only [Formula.eval_gate, interpretation]
      all_goals first
        | exact Bool.le_and (fun ha => le₀ (Bool.and_le_left _ _ ha))
            (fun hb => le₁ (Bool.and_le_right _ _ hb))
        | exact Bool.or_le (fun ha => Bool.left_le_or _ _ (le₀ ha))
            (fun hb => Bool.right_le_or _ _ (le₁ hb))

/-- Counting NOT and constant gates as layers, a positive binary weight `p` forces depth `2p+1`.
At weight zero the bound is zero. -/
theorem homogeneous_prediction_deMorgan_depth_lower_bound (stay hop : Gates q 1)
    (hs : ∀ a, guard stay a = true) (hh : ∀ a, guard hop a = true)
    (T : ℕ) (c : Gates (RawWidth q (T + 1)) 1)
    (hc : ∀ x : Config (Bits q),
      c.eval interpretation (rawSample x (T + 1)) 0 =
        ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0)) :
    (if T.bitIndices.length = 0 then 0 else 2 * T.bitIndices.length + 1) ≤ c.depth := by
  classical
  by_cases hzero : T.bitIndices.length = 0
  · simp [hzero]
  simp only [hzero, ↓reduceIte]
  let p := T.bitIndices.length
  have hn : 2 ≤ 2 ^ p := (pow_one (2 : ℕ)) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  let _ : Nonempty (Fin (2 ^ p)) := ⟨⟨0, by omega⟩⟩
  let e := supportWire q T
  let r := Function.invFun e
  have hr : Function.LeftInverse r e := Function.leftInverse_invFun e.injective
  let F := c.toFormula 0
  have hF : (F.rename r).Computes interpretation (Cslib.parity (2 ^ p)) := by
    intro u
    apply bit_injective
    have hu : (u ∘ r) ∘ e = u := funext fun i => congrArg u (hr i)
    rw [Formula.eval_rename, Circuit.eval_toFormula, ← rawSample_decodeRaw (u ∘ r), hc,
      bit_ofBoolRing, homogeneous_prediction_sum stay hop hs hh, rawSample_decodeRaw,
      ← support_parity q T (u ∘ r), hu]
  have hleaves : 2 ^ (2 * p) ≤ F.leafSize := by
    rw [mul_comm, pow_mul, ← Formula.leafSize_rename r F]
    exact sq_le_leafSize_of_computes_parity hF
  by_contra hsmall
  have hdepth : F.depth ≤ 2 * p := (Circuit.depth_toFormula_le c 0).trans (by omega)
  have hmono : Monotone (F.eval interpretation) :=
    formula_monotone_of_full_leaves F ((Nat.pow_le_pow_right (by decide) hdepth).trans hleaves)
  apply parity_not_monotone hn
  intro u v huv
  rw [← hF u, ← hF v, Formula.eval_rename, Formula.eval_rename]
  exact hmono fun i => huv (r i)

/-- The per-time optimum is attained by a De Morgan circuit. -/
theorem homogeneous_prediction_deMorgan_exact_depth (stay hop : Gates q 1)
    (hs : ∀ a, guard stay a = true) (hh : ∀ a, guard hop a = true) (T : ℕ) :
    ∃ c : Gates (RawWidth q (T + 1)) 1,
      (∀ x : Config (Bits q), c.eval interpretation (rawSample x (T + 1)) 0 =
        ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0)) ∧
      c.depth = (if T.bitIndices.length = 0 then 0 else 2 * T.bitIndices.length + 1) := by
  by_cases hzero : T.bitIndices.length = 0
  · refine ⟨homogeneousPrediction q T, homogeneousPrediction_correct stay hop hs hh T, ?_⟩
    have hdepth := homogeneousPrediction_depth q T
    simpa [hzero] using hdepth
  let p := T.bitIndices.length
  obtain ⟨F, hF, hd⟩ := Boolean.exists_computes_depth_le_formulaDepth_add_one (Cslib.parity (2 ^ p))
  rw [formulaDepth_parity_two_pow] at hd
  let w := Circuit.wiring signature (supportWire q T)
  let c := F.toCircuit.comp w
  have hc (x : Config (Bits q)) : c.eval interpretation (rawSample x (T + 1)) 0 =
      ofBoolRing (((step (guard stay) (guard hop))^[T] x).2 0) := by
    apply bit_injective
    rw [bit_ofBoolRing, homogeneous_prediction_sum stay hop hs hh]
    simp only [c, w, Circuit.eval_comp, Circuit.eval_wiring, Formula.eval_toCircuit]
    rw [hF]
    exact support_parity q T _
  refine ⟨c, hc, le_antisymm ?_ (homogeneous_prediction_deMorgan_depth_lower_bound stay hop hs hh T c hc)⟩
  have hupper := (Circuit.depth_comp_le F.toCircuit w).trans
    (Nat.add_le_add (F.depth_toCircuit_le.trans hd) (show w.depth ≤ 0 by simp [w]))
  simpa [p, hzero] using hupper

end PredictionDepth.FrozenPascal
