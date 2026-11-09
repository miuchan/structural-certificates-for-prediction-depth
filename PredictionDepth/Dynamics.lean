import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Int.Basic

/-!
# Discrete dynamics and geometric locality

Time is a natural number. `predict` fixes both a transition and an observation.
The locality results concern the *predictor's* wiring geometry, independently
of the dynamics it predicts; they do not impose a bound on arbitrary wiring.
-/

namespace PredictionDepth

def predict {X Y : Type*} (F : X → X) (O : X → Y) (T : ℕ) (x : X) : Y :=
  O ((F^[T]) x)

namespace Geometry

abbrev Config (A : Type*) := ℤ → A

/-- An output at `i` reads only the closed radius-`r` input interval at `i`. -/
def Local {A B : Type*} (r : ℕ) (f : Config A → Config B) : Prop :=
  ∀ x y i, (∀ j, i - (r : ℤ) ≤ j → j ≤ i + (r : ℤ) → x j = y j) →
    f x i = f y i

theorem local_id {A : Type*} : Local 0 (id : Config A → Config A) := by
  intro x y i h
  exact h i (by omega) (by omega)

theorem Local.comp {A B C : Type*} {r s : ℕ}
    {f : Config A → Config B} {g : Config B → Config C}
    (hg : Local s g) (hf : Local r f) : Local (r + s) (g ∘ f) := by
  intro x y i h
  apply hg
  intro j hj₁ hj₂
  apply hf
  intro k hk₁ hk₂
  apply h k <;> omega

/-- A depth-`d` predictor with per-layer radius `r` has radius at most `d*r`. -/
theorem Local.iterate {A : Type*} {r : ℕ} {f : Config A → Config A}
    (hf : Local r f) (d : ℕ) : Local (d * r) (f^[d]) := by
  induction d with
  | zero => simpa using (local_id : Local 0 (id : Config A → Config A))
  | succ d ih =>
    simpa [Function.iterate_succ', Nat.succ_mul, Nat.add_comm] using ih.comp hf

/-- Layers may have different local transition maps. The head executes last. -/
def runLayers {A : Type*} : List (Config A → Config A) → Config A → Config A
  | [] => id
  | f :: fs => f ∘ runLayers fs

theorem local_layers {A : Type*} {r : ℕ} (fs : List (Config A → Config A))
    (h : ∀ f ∈ fs, Local r f) : Local (fs.length * r) (runLayers fs) := by
  induction fs with
  | nil => simpa [runLayers] using (local_id : Local 0 (id : Config A → Config A))
  | cons f fs ih =>
    have hf := h f (by simp)
    have hfs := ih (fun g hg => h g (by simp [hg]))
    simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, runLayers] using hf.comp hfs

/-- Semantic influence at a single spatial coordinate. -/
def Influences {A B : Type*} (f : Config A → Config B) (source target : ℤ) : Prop :=
  ∃ x y, (∀ j, j ≠ source → x j = y j) ∧ f x target ≠ f y target

/-- Influence cannot cross a local map's dependency interval. -/
theorem influences_within {A B : Type*} {r : ℕ} {f : Config A → Config B}
    (hf : Local r f) {source target : ℤ} (h : Influences f source target) :
    target - (r : ℤ) ≤ source ∧ source ≤ target + (r : ℤ) := by
  by_contra hout
  obtain ⟨x, y, hxy, hneq⟩ := h
  apply hneq
  apply hf
  intro j hj₁ hj₂
  apply hxy
  intro heq
  subst j
  exact hout ⟨hj₁, hj₂⟩

theorem geometric_depth_bound {A B : Type*} {r d distance : ℕ}
    {f : Config A → Config B} (hf : Local (d * r) f)
    (h : Influences f (distance : ℤ) 0) : distance ≤ d * r := by
  have := (influences_within hf h).2
  omega

end Geometry
end PredictionDepth
