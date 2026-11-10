import PredictionDepth.Dynamics
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite semantics for sparse corrections

Each transition has its own input and output widths. A correction event is
indexed by its update time and by a bit in the *output* layer of that update.
The semantic verifier checks all update equations of the supplied trajectory.
-/

namespace PredictionDepth.SparseCorrections

abbrev Layer (w : ℕ → ℕ) (t : ℕ) := Fin (w t) → Bool
abbrev Transition (w : ℕ → ℕ) := (t : ℕ) → Layer w t → Layer w (t + 1)
abbrev Event (w : ℕ → ℕ) (T : ℕ) := (t : Fin T) × Fin (w (t.val + 1))
abbrev Residual (w : ℕ → ℕ) (T : ℕ) := Event w T → Bool
abbrev Trajectory (w : ℕ → ℕ) (T : ℕ) := (t : Fin (T + 1)) → Layer w t.val

variable {w : ℕ → ℕ} {T : ℕ}

def actualLayer (F : Transition w) (u : Layer w 0) : (t : ℕ) → Layer w t
  | 0 => u
  | t + 1 => F t (actualLayer F u t)

def actualTrajectory (F : Transition w) (u : Layer w 0) : Trajectory w T :=
  fun t => actualLayer F u t.val

def actualResidual (F L : Transition w) (u : Layer w 0) : Residual w T :=
  fun ⟨t, i⟩ => Bool.xor (actualLayer F u (t.val + 1) i) (L t.val (actualLayer F u t.val) i)

def support (e : Residual w T) : Finset (Event w T) := Finset.univ.filter (fun v => e v = true)

def Sparse (e : Residual w T) (k : ℕ) : Prop := (support e).card ≤ k

def Supported (e : Residual w T) (J : Finset (Event w T)) : Prop := support e ⊆ J

@[simp] theorem mem_support (e : Residual w T) (v : Event w T) :
    v ∈ support e ↔ e v = true := by simp [support]

def forcedLayer (L : Transition w) (u : Layer w 0) (e : Residual w T) :
    (t : ℕ) → t ≤ T → Layer w t
  | 0, _ => u
  | t + 1, ht => fun i =>
      Bool.xor (L t (forcedLayer L u e t (by omega)) i) (e ⟨⟨t, by omega⟩, i⟩)

def forcedTrajectory (L : Transition w) (u : Layer w 0) (e : Residual w T) :
    Trajectory w T :=
  fun t => forcedLayer L u e t.val (by omega)

@[simp] theorem forcedTrajectory_zero (L : Transition w) (u : Layer w 0) (e : Residual w T) :
    forcedTrajectory L u e 0 = u := rfl

@[simp] theorem actualTrajectory_zero (F : Transition w) (u : Layer w 0) :
    (actualTrajectory F u : Trajectory w T) 0 = u := rfl

@[simp] theorem forcedTrajectory_succ (L : Transition w) (u : Layer w 0) (e : Residual w T)
    (t : Fin T) (i : Fin (w (t.val + 1))) :
    forcedTrajectory L u e t.succ i =
      Bool.xor (L t (forcedTrajectory L u e t.castSucc) i) (e ⟨t, i⟩) := rfl

@[simp] theorem actualTrajectory_succ (F : Transition w) (u : Layer w 0)
    (t : Fin T) : (actualTrajectory F u : Trajectory w T) t.succ =
      F t ((actualTrajectory F u : Trajectory w T) t.castSucc) := rfl

/-- All output bits are checked, including those with a zero candidate correction. -/
def Valid (F : Transition w) (y : Trajectory w T) : Prop :=
  ∀ t : Fin T, y t.succ = F t (y t.castSucc)

theorem valid_iff_pointwise (F : Transition w) (y : Trajectory w T) :
    Valid F y ↔ ∀ v : Event w T, y v.1.succ v.2 = F v.1 (y v.1.castSucc) v.2 := by
  constructor
  · intro h v
    exact congrFun (h v.1) v.2
  · intro h t
    exact funext (fun i => h ⟨t, i⟩)

theorem actualTrajectory_valid (F : Transition w) (u : Layer w 0) :
    Valid F (actualTrajectory F u : Trajectory w T) := fun _ => rfl

/-- Determinism fixes every layer once the initial state and all local equations agree. -/
theorem eq_actualTrajectory_of_valid {F : Transition w} {u : Layer w 0}
    {y : Trajectory w T} (h₀ : y 0 = u) (h : Valid F y) :
    y = actualTrajectory F u := by
  funext t
  apply Fin.induction (motive := fun t => y t = actualTrajectory F u t) h₀
  intro s hs
  rw [h s, actualTrajectory_succ, hs]

private theorem xor_xor_cancel (a b : Bool) : Bool.xor a (Bool.xor b a) = b := by
  cases a <;> cases b <;> rfl

private theorem xor_recover (a b : Bool) : b = Bool.xor (Bool.xor a b) a := by
  cases a <;> cases b <;> rfl

theorem reconstruct_actualResidual (F L : Transition w) (u : Layer w 0) :
    forcedTrajectory L u (actualResidual F L u) = (actualTrajectory F u : Trajectory w T) := by
  funext t
  apply Fin.induction (motive := fun t => forcedTrajectory L u (actualResidual F L u) t =
    actualTrajectory F u t) rfl
  intro s hs
  funext i
  rw [forcedTrajectory_succ, hs]
  change Bool.xor (L s.val (actualLayer F u s.val) i)
      (Bool.xor (actualLayer F u (s.val + 1) i) (L s.val (actualLayer F u s.val) i)) = _
  exact xor_xor_cancel _ _

theorem valid_iff_eq_actualResidual (F L : Transition w) (u : Layer w 0) (e : Residual w T) :
    Valid F (forcedTrajectory L u e) ↔ e = actualResidual F L u := by
  constructor
  · intro h
    have hy := eq_actualTrajectory_of_valid (forcedTrajectory_zero L u e) h
    funext ⟨t, i⟩
    have hb := congrFun (congrFun hy t.succ) i
    rw [forcedTrajectory_succ, hy] at hb
    change Bool.xor (L t.val (actualLayer F u t.val) i) (e ⟨t, i⟩) =
      actualLayer F u (t.val + 1) i at hb
    change e ⟨t, i⟩ = Bool.xor (actualLayer F u (t.val + 1) i) (L t.val (actualLayer F u t.val) i)
    rw [← hb]
    exact xor_recover _ _
  · rintro rfl
    rw [reconstruct_actualResidual]
    exact actualTrajectory_valid F u

/-- A left-to-right spatial window, with consecutive tracks within each site. -/
def coneWidth (q R T t : ℕ) : ℕ := (2 * (R * (T - t)) + 1) * q

namespace Cone

abbrev Config (q : ℕ) := Geometry.Config (Fin q → Bool)

def radius (R T t : ℕ) : ℕ := R * (T - t)

def InWindow (R T t : ℕ) (i : ℤ) : Prop :=
  -(radius R T t : ℤ) ≤ i ∧ i ≤ (radius R T t : ℤ)

instance (R T t : ℕ) (i : ℤ) : Decidable (InWindow R T t i) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem predecessor_in_window {R T t : ℕ} {i j : ℤ} (ht : t < T)
    (hi : InWindow R T (t + 1) i) (h₁ : i - R ≤ j) (h₂ : j ≤ i + R) :
    InWindow R T t j := by
  have hsub : T - t = (T - (t + 1)) + 1 := by omega
  have hr : radius R T t = radius R T (t + 1) + R := by
    simp only [radius, hsub, Nat.mul_add, Nat.mul_one]
  unfold InWindow at hi ⊢
  omega

def site (R T t : ℕ) (j : Fin (2 * radius R T t + 1)) : ℤ :=
  j.val - (radius R T t : ℤ)

theorem site_in_window (R T t : ℕ) (j : Fin (2 * radius R T t + 1)) :
    InWindow R T t (site R T t j) := by
  have := j.isLt
  unfold InWindow site
  omega

def siteIndex (R T t : ℕ) (i : ℤ) (h : InWindow R T t i) :
    Fin (2 * radius R T t + 1) :=
  ⟨(i + radius R T t).toNat, by unfold InWindow at h; omega⟩

@[simp] theorem site_siteIndex (R T t : ℕ) (i : ℤ) (h : InWindow R T t i) :
    site R T t (siteIndex R T t i h) = i := by
  unfold InWindow at h
  change (((i + radius R T t).toNat : ℕ) : ℤ) - radius R T t = i
  omega

@[simp] theorem siteIndex_site (R T t : ℕ) (j : Fin (2 * radius R T t + 1))
    (h : InWindow R T t (site R T t j)) : siteIndex R T t (site R T t j) h = j := by
  apply Fin.ext
  simp [siteIndex, site]

def encodeBit (q R T t : ℕ) (i : ℤ) (h : InWindow R T t i) (a : Fin q) :
    Fin (coneWidth q R T t) :=
  finProdFinEquiv (siteIndex R T t i h, a)

theorem encodeBit_eq_iff {q R T t : ℕ} {i j : ℤ} {a b : Fin q}
    {hi : InWindow R T t i} {hj : InWindow R T t j} :
    encodeBit q R T t i hi a = encodeBit q R T t j hj b ↔ i = j ∧ a = b := by
  constructor
  · intro h
    have hp : (siteIndex R T t i hi, a) = (siteIndex R T t j hj, b) :=
      finProdFinEquiv.injective h
    exact ⟨by simpa using congrArg (fun p => site R T t p.1) hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem exists_encodeBit {q R T t : ℕ} (j : Fin (coneWidth q R T t)) :
    ∃ (i : ℤ) (hi : InWindow R T t i) (a : Fin q), j = encodeBit q R T t i hi a := by
  let p := (finProdFinEquiv.symm j : Fin (2 * radius R T t + 1) × Fin q)
  refine ⟨site R T t p.1, site_in_window _ _ _ _, p.2, ?_⟩
  unfold encodeBit
  rw [siteIndex_site]
  exact (finProdFinEquiv.apply_symm_apply j).symm

def restrict {q : ℕ} (R T t : ℕ) (x : Config q) : Layer (coneWidth q R T) t :=
  fun j =>
    let (k, a) := finProdFinEquiv.symm j
    x (site R T t k) a

def extend {q : ℕ} (R T t : ℕ) (u : Layer (coneWidth q R T) t) : Config q :=
  fun i a => if h : InWindow R T t i then u (encodeBit q R T t i h a) else false

@[simp] theorem restrict_encodeBit {q R T t : ℕ} (x : Config q) (i : ℤ)
    (h : InWindow R T t i) (a : Fin q) :
    restrict R T t x (encodeBit q R T t i h a) = x i a := by
  simp [restrict, encodeBit]

theorem extend_restrict_at {q R T t : ℕ} (x : Config q) (i : ℤ) (h : InWindow R T t i) :
    extend R T t (restrict R T t x) i = x i := by
  funext a
  simp [extend, h]

@[simp] theorem restrict_extend {q R T t : ℕ} (u : Layer (coneWidth q R T) t) :
    restrict R T t (extend R T t u) = u := by
  funext j
  let p := (finProdFinEquiv.symm j :
    Fin (2 * radius R T t + 1) × Fin q)
  change extend R T t u (site R T t p.1) p.2 = u j
  simp only [extend, site_in_window, dite_true, encodeBit, siteIndex_site]
  exact congrArg u (finProdFinEquiv.apply_symm_apply j)

def transition {q : ℕ} (R T : ℕ) (F : Config q → Config q) :
    Transition (coneWidth q R T) :=
  fun t u => restrict R T (t + 1) (F (extend R T t u))

theorem transition_restrict {q R T t : ℕ} {F : Config q → Config q} (hF : Geometry.Local R F)
    (ht : t < T) (x : Config q) :
    transition R T F t (restrict R T t x) = restrict R T (t + 1) (F x) := by
  funext j
  let p := (finProdFinEquiv.symm j :
    Fin (2 * radius R T (t + 1) + 1) × Fin q)
  change F (extend R T t (restrict R T t x)) (site R T (t + 1) p.1) p.2 =
    F x (site R T (t + 1) p.1) p.2
  apply congrFun
  apply hF
  intro k hk₁ hk₂
  exact extend_restrict_at x k (predecessor_in_window ht (site_in_window _ _ _ _) hk₁ hk₂)

/-- On every layer the finite evolution agrees with any infinite extension. -/
theorem finiteTrajectory_eq_restrict_iterate {q R T : ℕ} {F : Config q → Config q}
    (hF : Geometry.Local R F) (u : Layer (coneWidth q R T) 0) (x : Config q)
    (hx : restrict R T 0 x = u) (t : Fin (T + 1)) :
    (actualTrajectory (transition R T F) u : Trajectory (coneWidth q R T) T) t =
      restrict R T t.val ((F^[t.val]) x) := by
  induction t using Fin.induction with
  | zero => exact hx.symm
  | succ t ih =>
    rw [actualTrajectory_succ, ih]
    change transition R T F t.val (restrict R T t.val ((F^[t.val]) x)) =
      restrict R T (t.val + 1) ((F^[t.val + 1]) x)
    rw [Function.iterate_succ_apply', transition_restrict hF t.isLt]

/-- Both finite transitions agree with the corresponding infinite update on each output layer. -/
theorem actualResidual_eq_restrict {q R T : ℕ} {F L : Config q → Config q}
    (hF : Geometry.Local R F) (hL : Geometry.Local R L) (x : Config q)
    (t : Fin T) (i : ℤ) (hi : InWindow R T (t.val + 1) i) (a : Fin q) :
    actualResidual (transition R T F) (transition R T L) (restrict R T 0 x)
      ⟨t, encodeBit q R T (t.val + 1) i hi a⟩ =
      Bool.xor (((F^[t.val + 1]) x) i a) ((L ((F^[t.val]) x)) i a) := by
  have ht := finiteTrajectory_eq_restrict_iterate hF _ x rfl t.castSucc
  have hs := finiteTrajectory_eq_restrict_iterate hF _ x rfl t.succ
  change Bool.xor ((actualTrajectory (transition R T F) (restrict R T 0 x) :
    Trajectory (coneWidth q R T) T) t.succ (encodeBit q R T (t.val + 1) i hi a))
    (transition R T L t.val ((actualTrajectory (transition R T F) (restrict R T 0 x) :
      Trajectory (coneWidth q R T) T) t.castSucc) (encodeBit q R T (t.val + 1) i hi a)) = _
  rw [ht, hs]
  simp only [Fin.val_castSucc, Fin.val_succ, transition_restrict hL t.isLt, restrict_encodeBit]

end Cone
end PredictionDepth.SparseCorrections
