import PredictionDepth.FrozenPascal.Decoder

/-! The predictor only reads the actual right-hand cone of the initial state. -/

namespace PredictionDepth.FrozenPascal

open FastComposition
open scoped BigOperators

/-- The sampled cone, with the two control predicates evaluated at each site. -/
def sample (stay hop : Q → Bool) (x : Config Q) (m : ℕ) : Bits (InputWidth m) :=
  joinBits (fun i : Fin m => stay (x.1 i.val))
    (joinBits (fun i : Fin m => hop (x.1 i.val)) (fun i : Fin m => ofBoolRing (x.2 i.val)))

@[simp] theorem sample_stay (stay hop : Q → Bool) (x : Config Q) (i : Fin m) :
    sample stay hop x m (stayWire i) = stay (x.1 i.val) := by simp [sample, stayWire]

@[simp] theorem sample_hop (stay hop : Q → Bool) (x : Config Q) (i : Fin m) :
    sample stay hop x m (hopWire i) = hop (x.1 i.val) := by simp [sample, hopWire]

@[simp] theorem sample_data (stay hop : Q → Bool) (x : Config Q) (i : Fin m) :
    sample stay hop x m (dataWire i) = ofBoolRing (x.2 i.val) := by
  simp only [sample, dataWire, joinBits_right]

theorem sample_coefficient (stay hop : Q → Bool) (x : Config Q) {m t k : ℕ} (hk : k < m) :
    coefficient Prod.fst Prod.snd (initial (sample stay hop x m)).1 0 t k =
      coefficient stay hop x.1 0 t k := by
  have hc : enabled Prod.fst (initial (sample stay hop x m)).1 0 k =
      enabled stay x.1 0 k := by
    rw [enabled_sum, enabled_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < m := (Finset.mem_range.mp hj).trans_le hk
    have he := extendTrack_fin (sample stay hop x m ∘ stayWire) (⟨j, hj'⟩ : Fin m)
    simpa only [initial, zero_add, Function.comp_apply, sample_stay] using congrArg Bool.toNat he
  have he : edgeProduct Prod.snd (initial (sample stay hop x m)).1 0 k =
      edgeProduct hop x.1 0 k := by
    rw [edgeProduct_prod, edgeProduct_prod]
    apply Finset.prod_congr rfl
    intro j hj
    have hj' : j < m := (Finset.mem_range.mp hj).trans hk
    have he := extendTrack_fin (sample stay hop x m ∘ hopWire) (⟨j, hj'⟩ : Fin m)
    simpa only [initial, zero_add, Function.comp_apply, sample_hop] using congrArg bit he
  simp [coefficient, hc, he]

/-- Any extension of the cone yields the same prediction. -/
theorem sample_prediction (stay hop : Q → Bool) (x : Config Q) {T m : ℕ} (hT : T < m) :
    ((step Prod.fst Prod.snd)^[T] (initial (sample stay hop x m))).2 0 =
      ((step stay hop)^[T] x).2 0 := by
  rw [iterate_data, iterate_data]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < m := (Finset.mem_range.mp hk).trans_le hT
  rw [sample_coefficient stay hop x hk']
  have he := extendTrack_fin (sample stay hop x m ∘ dataWire) (⟨k, hk'⟩ : Fin m)
  congr 1
  simpa only [initial, zero_add, Function.comp_apply, sample_data, bit_ofBoolRing] using
    congrArg bit he

end PredictionDepth.FrozenPascal
