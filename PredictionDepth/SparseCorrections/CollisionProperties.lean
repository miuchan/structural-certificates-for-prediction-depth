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

private theorem stream_read (x : Config) (i : ℤ) (a : Fin 3) :
    (stream x i).bits a = (x (i + Streaming.drift a)).bits a := by
  have h := Streaming.bitStream_read (Cell.bits ∘ x) i a
  rw [bitStream, lift_bits] at h
  exact h

private theorem occupied_stream (x : Config) :
    occupied (stream x) = streamSource ⁻¹' occupied x := by
  ext p
  change (stream x p.1).bits p.2 = true ↔ (x (p.1 + Streaming.drift p.2)).bits p.2 = true
  exact iff_of_eq (congrArg (· = true) (stream_read x p.1 p.2))

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

private def cellSupport (c : Cell) : Finset (Fin 3) :=
  Finset.univ.filter fun a => c.bits a = true

private theorem cellSupport_card (c : Cell) : (cellSupport c).card = particles c := by
  rcases c with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

private theorem collide_fixed (c : Cell) (h : particles c ≠ 2) : collide c = c := by
  rcases c with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> first | rfl | exact (h rfl).elim

private theorem two_tracks {c : Cell} (hc : particles c = 2) :
    ∃ a b : Fin 3, a ≠ b ∧ c.bits a = true ∧ c.bits b = true := by
  rcases c with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> revert hc <;> decide

private theorem at_collision_site {x : Config} (hf : (occupied x).Finite)
    (hn : (occupied x).ncard ≤ 2) {i : ℤ} (hi : particles (x i) = 2) :
    ∀ p ∈ occupied x, p.1 = i := by
  let e : Fin 3 ↪ ℤ × Fin 3 := ⟨fun a => (i, a), fun _ _ h => congrArg Prod.snd h⟩
  let s := (cellSupport (x i)).map e
  have hs : (s : Set (ℤ × Fin 3)) ⊆ occupied x := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hp
    exact (Finset.mem_filter.mp ha).2
  have he : (s : Set (ℤ × Fin 3)) = occupied x :=
    Set.eq_of_subset_of_ncard_le hs (by simpa [s, cellSupport_card, hi] using hn) hf
  intro p hp
  rw [← he] at hp
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hp
  rfl

private theorem stream_iterate_read (x : Config) (t : ℕ) (i : ℤ) (a : Fin 3) :
    (((stream^[t]) x) i).bits a = (x (i + t * Streaming.drift a)).bits a := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', stream_read, ih]
    congr 2
    push_cast
    ring

private theorem drift_injective : Function.Injective Streaming.drift := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide

/-- Any nonzero amount of streaming separates the tracks of particles
that all started at the same site. -/
private theorem separates {x : Config} {i : ℤ} (hx : ∀ p ∈ occupied x, p.1 = i)
    {t : ℕ} (ht : 0 < t) (j : ℤ) : particles (((stream^[t]) x) j) ≠ 2 := by
  intro hc
  obtain ⟨a, b, hab, ha, hb⟩ := two_tracks hc
  rw [stream_iterate_read] at ha hb
  have h₁ := hx (j + t * Streaming.drift a, a) ha
  have h₂ := hx (j + t * Streaming.drift b, b) hb
  have he : (t : ℤ) * Streaming.drift a = (t : ℤ) * Streaming.drift b :=
    add_left_cancel (h₁.trans h₂.symm)
  exact hab (drift_injective (mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt ht) he))

private theorem no_collision_after {x : Config} (hf : (occupied x).Finite)
    (hn : (occupied x).ncard ≤ 2) {i : ℤ} (hi : particles (x i) = 2)
    {t : ℕ} (ht : 0 < t) (j : ℤ) : particles (((step^[t]) x) j) ≠ 2 := by
  let z := collide ∘ x
  have hz : ∀ p ∈ occupied z, p.1 = i := by
    intro p hp
    apply at_collision_site hf hn hi ((collisionSource x) p)
    rwa [show occupied z = _ from occupied_collide x] at hp
  have hstep (t : ℕ) (ht : 0 < t) : (step^[t]) x = (stream^[t]) z := by
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases h : t = 0
      · subst t
        rfl
      · rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply', step]
        congr 1
        exact funext (fun j => collide_fixed _ (separates hz (by omega) j))
  rw [hstep t ht]
  exact separates hz ht j

private theorem iterate_population (x : Config) (hf : (occupied x).Finite) (t : ℕ) :
    (occupied ((step^[t]) x)).Finite ∧
      (occupied ((step^[t]) x)).ncard = (occupied x).ncard := by
  induction t with
  | zero => exact ⟨hf, rfl⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨(preserves_population _ ih.1).1, (preserves_population _ ih.1).2.trans ih.2⟩

/-- An initial population of at most two can have at most one collision in
the whole infinite space-time trajectory. -/
theorem collision_unique {x : Config} (hf : (occupied x).Finite)
    (hn : (occupied x).ncard ≤ 2) {t s : ℕ} {i j : ℤ}
    (ht : particles (((step^[t]) x) i) = 2) (hs : particles (((step^[s]) x) j) = 2) :
    t = s ∧ i = j := by
  have hnotLater {t s : ℕ} {i j : ℤ} (hts : t < s)
      (hc : particles (((step^[t]) x) i) = 2) : particles (((step^[s]) x) j) ≠ 2 := by
    have hp := iterate_population x hf t
    have h := no_collision_after hp.1 (hp.2 ▸ hn) hc (show 0 < s - t by omega) j
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hts.le] at h
    exact h
  have he : t = s := by
    rcases lt_trichotomy t s with h | h | h
    · exact False.elim (hnotLater h ht hs)
    · exact h
    · exact False.elim (hnotLater h hs ht)
  subst s
  have hp := iterate_population x hf t
  obtain ⟨a, _, _, ha, _⟩ := two_tracks hs
  exact ⟨rfl, (at_collision_site hp.1 (hp.2 ▸ hn) ht (j, a) ha).symm⟩

private theorem residual_at {T : ℕ} (x : Config) (t : Fin T) (j : ℤ)
    (hj : Cone.InWindow 1 T (t.val + 1) j) (a : Fin 3) :
    let y := (step^[t.val]) x
    let p := j + Streaming.drift a
    actualResidual (Cone.transition 1 T bitStep) (Cone.transition 1 T bitStream)
      (Cone.restrict 1 T 0 (Cell.bits ∘ x))
      (⟨t, Cone.encodeBit 3 1 T (t.val + 1) j hj a⟩ : Event (coneWidth 3 1 T) T) =
      ((collide (y p)).xor (y p)).bits a := by
  dsimp only
  rw [Cone.actualResidual_eq_restrict bitStep_local bitStream_local, bitStep_iterate,
    bitStep_iterate, bitStream, lift_bits, Function.iterate_succ_apply']
  change Bool.xor (step ((step^[t.val]) x) j |>.bits a)
    (stream ((step^[t.val]) x) j |>.bits a) = _
  rw [step, stream_read, stream_read, Cell.bits_xor]
  rfl

private theorem collision_of_discrepancy {c : Cell} {a : Fin 3}
    (h : ((collide c).xor c).bits a = true) : particles c = 2 := by
  by_contra hn
  rw [collide_fixed c hn, Cell.bits_xor, Bool.xor_self] at h
  exact Bool.false_ne_true h

/-- For any horizon, an infinite configuration containing at most two occupied
tracks has at most two residual bits in the whole observation cone. -/
theorem sparse_of_two_particles (x : Config) (hf : (occupied x).Finite)
    (hn : (occupied x).ncard ≤ 2) (T : ℕ) :
    Sparse (actualResidual (Cone.transition 1 T bitStep) (Cone.transition 1 T bitStream)
      (Cone.restrict 1 T 0 (Cell.bits ∘ x)) : Residual (coneWidth 3 1 T) T) 2 := by
  let e : Residual (coneWidth 3 1 T) T :=
    actualResidual (Cone.transition 1 T bitStep) (Cone.transition 1 T bitStream)
      (Cone.restrict 1 T 0 (Cell.bits ∘ x))
  change (support e).card ≤ 2
  have hres (t : Fin T) (j : ℤ) (hj : Cone.InWindow 1 T (t.val + 1) j) (a : Fin 3)
      (he : (⟨t, Cone.encodeBit 3 1 T (t.val + 1) j hj a⟩ : Event (coneWidth 3 1 T) T) ∈ support e) :
      let c := ((step^[t.val]) x) (j + Streaming.drift a)
      ((collide c).xor c).bits a = true :=
    (residual_at x t j hj a).symm.trans ((mem_support _ _).mp he)
  by_cases hc : ∃ (t : ℕ) (i : ℤ), particles (((step^[t]) x) i) = 2
  · obtain ⟨t, i, hi⟩ := hc
    let c := ((step^[t]) x) i
    let changed := cellSupport ((collide c).xor c)
    have hcard : changed.card = 2 := by
      rw [cellSupport_card, collision_discrepancy_count, ite_eq_left hi]
    let track (v : Event (coneWidth 3 1 T) T) : Fin 3 :=
      ((finProdFinEquiv.symm v.2 : Fin (2 * Cone.radius 1 T (v.1.val + 1) + 1) × Fin 3)).2
    have htrack (s : Fin T) (j : ℤ) (hj : Cone.InWindow 1 T (s.val + 1) j) (a : Fin 3) :
        track ⟨s, Cone.encodeBit 3 1 T (s.val + 1) j hj a⟩ = a := by
      exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply
        (Cone.siteIndex 1 T (s.val + 1) j hj, a))
    have haddr (s : Fin T) (j : ℤ) (hj : Cone.InWindow 1 T (s.val + 1) j) (a : Fin 3)
        (he : (⟨s, Cone.encodeBit 3 1 T (s.val + 1) j hj a⟩ : Event (coneWidth 3 1 T) T) ∈
          support e) : s.val = t ∧ j + Streaming.drift a = i :=
      collision_unique hf hn (collision_of_discrepancy (hres s j hj a he)) hi
    rw [← hcard]
    apply Finset.card_le_card_of_injOn track
    · rintro ⟨s, b⟩ hb
      obtain ⟨j, hj, a, rfl⟩ := Cone.exists_encodeBit (q := 3) (R := 1) (T := T) (t := s.val + 1) b
      rw [Finset.mem_coe, htrack]
      have he := hres s j hj a hb
      obtain ⟨ht, hj'⟩ := haddr s j hj a hb
      dsimp only at he
      rw [ht, hj'] at he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
    · rintro ⟨s, b⟩ hb ⟨s', b'⟩ hb' he
      obtain ⟨j, hj, a, rfl⟩ := Cone.exists_encodeBit (q := 3) (R := 1) (T := T) (t := s.val + 1) b
      obtain ⟨j', hj', a', rfl⟩ := Cone.exists_encodeBit (q := 3) (R := 1) (T := T) (t := s'.val + 1) b'
      rw [htrack, htrack] at he
      subst a'
      obtain ⟨hs, hj₁⟩ := haddr s j hj a hb
      obtain ⟨hs', hj₂⟩ := haddr s' j' hj' a hb'
      obtain rfl : s = s' := Fin.ext (hs.trans hs'.symm)
      obtain rfl : j = j' := add_right_cancel (hj₁.trans hj₂.symm)
      rfl
  · have hempty : support e = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨t, b⟩ hb
      obtain ⟨j, hj, a, rfl⟩ := Cone.exists_encodeBit (q := 3) (R := 1) (T := T) (t := t.val + 1) b
      exact hc ⟨t, j + Streaming.drift a, collision_of_discrepancy (hres t j hj a hb)⟩
    simp [hempty]

/-- Every encoded initial window with at most two occupied tracks satisfies
the two-bit certificate, independently of which tracks or sites are occupied. -/
theorem twoParticle_sparse (T : ℕ) (u : Layer (coneWidth 3 1 T) 0)
    (hu : (Finset.univ.filter fun b => u b = true).card ≤ 2) :
    Sparse (actualResidual (Cone.transition 1 T bitStep) (Cone.transition 1 T bitStream)
      u : Residual (coneWidth 3 1 T) T) 2 := by
  let x := Cell.ofBits ∘ Cone.extend 1 T 0 u
  let addr (b : Fin (coneWidth 3 1 T 0)) : ℤ × Fin 3 :=
    let p := (finProdFinEquiv.symm b : Fin (2 * Cone.radius 1 T 0 + 1) × Fin 3)
    (Cone.site 1 T 0 p.1, p.2)
  let s := Finset.univ.filter fun b => u b = true
  have hsubset : occupied x ⊆ addr '' (s : Set (Fin (coneWidth 3 1 T 0))) := by
    rintro ⟨i, a⟩ ha
    change (Cell.ofBits (Cone.extend 1 T 0 u i)).bits a = true at ha
    rw [Cell.bits_ofBits] at ha
    by_cases hi : Cone.InWindow 1 T 0 i
    · have he : u (Cone.encodeBit 3 1 T 0 i hi a) = true := by simpa [Cone.extend, hi] using ha
      refine ⟨Cone.encodeBit 3 1 T 0 i hi a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, ?_⟩
      have h := finProdFinEquiv.symm_apply_apply (Cone.siteIndex 1 T 0 i hi, a)
      exact (congrArg (fun p => (Cone.site 1 T 0 p.1, p.2)) h).trans
        (by rw [Cone.site_siteIndex])
    · simp [Cone.extend, hi] at ha
  have hs := s.finite_toSet
  have hn := (Set.ncard_le_ncard hsubset (hs.image addr)).trans (Set.ncard_image_le hs)
  have hx : Cell.bits ∘ x = Cone.extend 1 T 0 u := by
    funext i
    exact Cell.bits_ofBits _
  have h := sparse_of_two_particles x ((hs.image addr).subset hsubset)
    (hn.trans (by simpa only [Set.ncard_coe_finset] using hu)) T
  rwa [hx, Cone.restrict_extend] at h

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
