import PredictionDepth.SparseCorrections.Semantics
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# A reversible collision rule

A sitewise permutation changes only the weight-two triples. Streaming sends
the first track right, the second track left, and leaves the third stationary.
The example family uses the first collision to launch the second one.
-/

namespace PredictionDepth.SparseCorrections.Collision

@[ext] structure Cell where
  a : Bool
  b : Bool
  c : Bool
  deriving DecidableEq

abbrev Config := Geometry.Config Cell

def collide : Cell → Cell
  | ⟨true, true, false⟩ => ⟨true, false, true⟩
  | ⟨true, false, true⟩ => ⟨false, true, true⟩
  | ⟨false, true, true⟩ => ⟨true, true, false⟩
  | x => x

def uncollide (x : Cell) : Cell := collide (collide x)

theorem uncollide_collide (x : Cell) : uncollide (collide x) = x := by
  rcases x with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

theorem collide_uncollide (x : Cell) : collide (uncollide x) = x :=
  uncollide_collide x

def particles (x : Cell) : ℕ := x.a.toNat + x.b.toNat + x.c.toNat

theorem collide_particles (x : Cell) : particles (collide x) = particles x := by
  rcases x with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

def stream (x : Config) : Config :=
  fun i => ⟨(x (i - 1)).a, (x (i + 1)).b, (x i).c⟩

def unstream (x : Config) : Config :=
  fun i => ⟨(x (i + 1)).a, (x (i - 1)).b, (x i).c⟩

def step (x : Config) : Config := stream (collide ∘ x)

def unstep (x : Config) : Config := uncollide ∘ unstream x

theorem step_reversible : Function.LeftInverse unstep step ∧ Function.RightInverse unstep step := by
  have hs (x : Config) : unstream (stream x) = x := by
    funext i
    ext <;> simp [unstream, stream]
  have ht (x : Config) : stream (unstream x) = x := by
    funext i
    ext <;> simp [unstream, stream]
  constructor
  · intro x
    rw [unstep, step, hs]
    exact funext (fun i => uncollide_collide (x i))
  · intro x
    have h : collide ∘ unstep x = unstream x := funext (fun i => collide_uncollide _)
    rw [step, h, ht]

def Cell.xor (x y : Cell) : Cell :=
  ⟨Bool.xor x.a y.a, Bool.xor x.b y.b, Bool.xor x.c y.c⟩

theorem stream_xor (x y : Config) :
    stream (fun i => (x i).xor (y i)) = fun i => (stream x i).xor (stream y i) := rfl

theorem step_not_additive :
    ¬ ∀ x y : Config, step (fun i => (x i).xor (y i)) = fun i => (step x i).xor (step y i) := by
  intro h
  have h₀ := congrArg (fun z : Config => (z 0).b)
    (h (fun _ => ⟨true, false, false⟩) (fun _ => ⟨false, true, false⟩))
  contradiction

private def mark (i j : ℤ) : Bool := decide (i = j)

private theorem mark_of_eq {i j : ℤ} (h : i = j) : mark i j = true := by simp [mark, h]
private theorem mark_of_ne {i j : ℤ} (h : i ≠ j) : mark i j = false := by simp [mark, h]
private theorem mark_congr {i j k l : ℤ} (h : i = j ↔ k = l) : mark i j = mark k l := by
  simp [mark, h]

/-- Two fixed reflectors, at zero and at the strictly negative position `-ell`. -/
def initial (ell : ℕ) : Config :=
  fun i => ⟨mark i 0, false, mark i 0 || mark i (-(ell : ℤ))⟩

def outbound (ell t : ℕ) : Config :=
  fun i => ⟨false, mark i (-(t : ℤ)), mark i 0 || mark i (-(ell : ℤ))⟩

/-- The newly created right-moving particle returns while the other keeps moving left. -/
def returning (ell t : ℕ) : Config :=
  fun i => ⟨mark i ((t : ℤ) - 2 * ell), mark i (-(t : ℤ)), mark i 0⟩

private theorem collide_initial (ell : ℕ) (i : ℤ) :
    collide (initial ell i) = ⟨false, mark i 0, mark i 0 || mark i (-(ell : ℤ))⟩ := by
  by_cases hi : i = 0
  · simp only [initial, mark_of_eq hi, Bool.true_or, collide]
  · simp only [initial, mark_of_ne hi, Bool.false_or]
    cases mark i (-(ell : ℤ)) <;> rfl

theorem step_initial (ell : ℕ) : step (initial ell) = outbound ell 1 := by
  funext i
  simp only [step, stream, Function.comp_apply, collide_initial]
  have h : mark (i + 1) 0 = mark i (-((1 : ℕ) : ℤ)) := mark_congr (by omega)
  simp only [h, outbound]

private theorem collide_outbound_before {ell t : ℕ} (h₀ : 0 < t) (ht : t < ell) (i : ℤ) :
    collide (outbound ell t i) = outbound ell t i := by
  by_cases hi : i = -(t : ℤ)
  · have hn₀ : i ≠ 0 := by omega
    have hn₁ : i ≠ -(ell : ℤ) := by omega
    simp only [outbound, mark_of_eq hi, mark_of_ne hn₀, mark_of_ne hn₁, Bool.false_or, collide]
  · simp only [outbound, mark_of_ne hi]
    cases mark i 0 <;> cases mark i (-(ell : ℤ)) <;> rfl

theorem step_outbound_before {ell t : ℕ} (h₀ : 0 < t) (ht : t < ell) :
    step (outbound ell t) = outbound ell (t + 1) := by
  funext i
  simp only [step, stream, Function.comp_apply, collide_outbound_before h₀ ht]
  have h : mark (i + 1) (-(t : ℤ)) = mark i (-((t + 1 : ℕ) : ℤ)) :=
    mark_congr (by omega)
  simp only [outbound, h]

private theorem collide_outbound_at {ell : ℕ} (h : 0 < ell) (i : ℤ) :
    collide (outbound ell ell i) = ⟨mark i (-(ell : ℤ)), mark i (-(ell : ℤ)), mark i 0⟩ := by
  by_cases hi : i = -(ell : ℤ)
  · have hj : i ≠ 0 := by omega
    simp only [outbound, mark_of_eq hi, mark_of_ne hj, Bool.false_or, collide]
  · simp only [outbound, mark_of_ne hi, Bool.or_false]
    cases mark i 0 <;> rfl

theorem step_outbound_at {ell : ℕ} (h : 0 < ell) :
    step (outbound ell ell) = returning ell (ell + 1) := by
  funext i
  simp only [step, stream, Function.comp_apply, collide_outbound_at h]
  have ha : mark (i - 1) (-(ell : ℤ)) = mark i (((ell + 1 : ℕ) : ℤ) - 2 * ell) :=
    mark_congr (by omega)
  have hb : mark (i + 1) (-(ell : ℤ)) = mark i (-((ell + 1 : ℕ) : ℤ)) :=
    mark_congr (by omega)
  simp only [returning, ha, hb]

private theorem collide_returning_before {ell t : ℕ} (h₀ : ell < t) (ht : t < 2 * ell) (i : ℤ) :
    collide (returning ell t i) = returning ell t i := by
  by_cases ha : i = (t : ℤ) - 2 * ell
  · have hb : i ≠ -(t : ℤ) := by omega
    have hc : i ≠ 0 := by omega
    simp only [returning, mark_of_eq ha, mark_of_ne hb, mark_of_ne hc, collide]
  · by_cases hb : i = -(t : ℤ)
    · have hc : i ≠ 0 := by omega
      simp only [returning, mark_of_ne ha, mark_of_eq hb, mark_of_ne hc, collide]
    · simp only [returning, mark_of_ne ha, mark_of_ne hb]
      cases mark i 0 <;> rfl

theorem step_returning_before {ell t : ℕ} (h₀ : ell < t) (ht : t < 2 * ell) :
    step (returning ell t) = returning ell (t + 1) := by
  funext i
  simp only [step, stream, Function.comp_apply, collide_returning_before h₀ ht]
  have ha : mark (i - 1) ((t : ℤ) - 2 * ell) = mark i (((t + 1 : ℕ) : ℤ) - 2 * ell) :=
    mark_congr (by omega)
  have hb : mark (i + 1) (-(t : ℤ)) = mark i (-((t + 1 : ℕ) : ℤ)) :=
    mark_congr (by omega)
  simp only [returning, ha, hb]

theorem iterate_outbound {ell t : ℕ} (h₀ : 0 < t) (ht : t ≤ ell) :
    (step^[t]) (initial ell) = outbound ell t := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    by_cases hz : t = 0
    · subst t
      exact step_initial ell
    · rw [ih (by omega) (by omega), step_outbound_before (by omega) (by omega)]

theorem iterate_returning {ell t : ℕ} (hell : 0 < ell) (h₀ : ell < t) (ht : t ≤ 2 * ell) :
    (step^[t]) (initial ell) = returning ell t := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    by_cases hz : t = ell
    · subst t
      rw [iterate_outbound hell le_rfl, step_outbound_at hell]
    · rw [ih (by omega) (by omega), step_returning_before (by omega) (by omega)]

/-- The two reflections send the initially right-moving particle back to the observed site. -/
theorem returning_observation {ell : ℕ} (hell : 0 < ell) :
    (((step^[2 * ell]) (initial ell)) 0).a = true := by
  rw [iterate_returning hell (by omega) le_rfl]
  exact mark_of_eq (by omega)


def residualProfile (ell t : ℕ) (i : ℤ) : Cell :=
  if t = 0 then ⟨mark i 1, mark i (-1), false⟩
  else if t = ell then ⟨mark i (1 - ell), false, mark i (-(ell : ℤ))⟩
  else ⟨false, false, false⟩

/-- Exactly the two collision updates carry a nonzero global discrepancy. -/
theorem residual_eq_profile {ell t : ℕ} (hell : 0 < ell) (ht : t < 2 * ell) (i : ℤ) :
    let x := (step^[t]) (initial ell)
    (step x i).xor (stream x i) = residualProfile ell t i := by
  dsimp
  by_cases hz : t = 0
  · subst t
    change (step (initial ell) i).xor (stream (initial ell) i) = residualProfile ell 0 i
    rw [step_initial]
    have ha : mark (i - 1) 0 = mark i 1 := mark_congr (by omega)
    simp [Cell.xor, stream, initial, outbound, residualProfile, ha]
  · by_cases he : t = ell
    · subst t
      rw [iterate_outbound hell le_rfl, step_outbound_at hell]
      have h₁ : mark i ((ell : ℤ) + 1 - 2 * ell) = mark i (1 - ell) :=
        mark_congr (by omega)
      have h₂ : mark (i + 1) (-(ell : ℤ)) = mark i (-((ell + 1 : ℕ) : ℤ)) :=
        mark_congr (by omega)
      by_cases hc : i = 0
      · have hn : i ≠ -(ell : ℤ) := by omega
        simp [returning, Cell.xor, stream, outbound, residualProfile, hz, h₁, h₂,
          mark_of_eq hc, mark_of_ne hn]
      · simp [returning, Cell.xor, stream, outbound, residualProfile, hz, h₁, h₂, mark_of_ne hc]
    · have hfixed :
        collide ∘ ((step^[t]) (initial ell)) = (step^[t]) (initial ell) := by
        by_cases hlt : t < ell
        · rw [iterate_outbound (by omega) (by omega)]
          exact funext (collide_outbound_before (by omega) hlt)
        · rw [iterate_returning hell (by omega) (by omega)]
          exact funext (collide_returning_before (by omega) ht)
      simp [step, hfixed, Cell.xor, residualProfile, hz, he]

def Cell.bits (x : Cell) : Fin 3 → Bool := ![x.a, x.b, x.c]

def Cell.ofBits (v : Fin 3 → Bool) : Cell := ⟨v 0, v 1, v 2⟩

@[simp] theorem Cell.ofBits_bits (x : Cell) : Cell.ofBits x.bits = x := by
  cases x
  rfl

@[simp] theorem Cell.bits_ofBits (v : Fin 3 → Bool) : (Cell.ofBits v).bits = v := by
  funext a
  fin_cases a <;> rfl

theorem Cell.bits_xor (x y : Cell) (a : Fin 3) :
    (x.xor y).bits a = Bool.xor (x.bits a) (y.bits a) := by
  fin_cases a <;> rfl

def lift (f : Config → Config) (x : Cone.Config 3) : Cone.Config 3 :=
  fun i => (f (Cell.ofBits ∘ x) i).bits

def bitStep : Cone.Config 3 → Cone.Config 3 := lift step

def bitStream : Cone.Config 3 → Cone.Config 3 := lift stream

@[simp] theorem lift_bits (f : Config → Config) (x : Config) :
    lift f (Cell.bits ∘ x) = Cell.bits ∘ f x := by
  have h : Cell.ofBits ∘ (Cell.bits ∘ x) = x := funext (fun i => Cell.ofBits_bits (x i))
  unfold lift
  rw [h]
  rfl

theorem bitStep_local : Geometry.Local 1 bitStep := by
  intro x y i h
  simp only [bitStep, lift, step, stream, Function.comp_apply]
  rw [h (i - 1) (by omega) (by omega), h (i + 1) (by omega) (by omega),
    h i (by omega) (by omega)]

theorem bitStream_local : Geometry.Local 1 bitStream := by
  intro x y i h
  simp only [bitStream, lift, stream, Function.comp_apply]
  rw [h (i - 1) (by omega) (by omega), h (i + 1) (by omega) (by omega),
    h i (by omega) (by omega)]

theorem bitStep_iterate (x : Config) (t : ℕ) :
    (bitStep^[t]) (Cell.bits ∘ x) = Cell.bits ∘ (step^[t]) x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact lift_bits _ _

def exampleInput (ell : ℕ) : Layer (coneWidth 3 1 (2 * ell)) 0 :=
  Cone.restrict 1 (2 * ell) 0 (Cell.bits ∘ initial ell)

def exampleResidual (ell : ℕ) : Residual (coneWidth 3 1 (2 * ell)) (2 * ell) :=
  actualResidual (Cone.transition 1 (2 * ell) bitStep)
    (Cone.transition 1 (2 * ell) bitStream) (exampleInput ell)

theorem exampleResidual_at {ell : ℕ} (hell : 0 < ell) (t : Fin (2 * ell))
    (i : ℤ) (hi : Cone.InWindow 1 (2 * ell) (t.val + 1) i) (a : Fin 3) :
    exampleResidual ell ⟨t, Cone.encodeBit 3 1 (2 * ell) (t.val + 1) i hi a⟩ =
      (residualProfile ell t i).bits a := by
  rw [exampleResidual, exampleInput, Cone.actualResidual_eq_restrict bitStep_local bitStream_local,
    bitStep_iterate, bitStep_iterate, bitStream, lift_bits, Function.iterate_succ_apply']
  exact (Cell.bits_xor _ _ a).symm.trans
    (congrArg (fun x : Cell => x.bits a) (residual_eq_profile hell t.isLt i))


abbrev ExampleEvent (ell : ℕ) := Event (coneWidth 3 1 (2 * ell)) (2 * ell)

def eventAt {ell : ℕ} (t : Fin (2 * ell)) (i : ℤ)
    (hi : Cone.InWindow 1 (2 * ell) (t.val + 1) i) (a : Fin 3) : ExampleEvent ell :=
  ⟨t, Cone.encodeBit 3 1 (2 * ell) (t.val + 1) i hi a⟩

private theorem eventAt_eq_iff {ell : ℕ} {t s : Fin (2 * ell)} {i j : ℤ} {a b : Fin 3}
    {hi : Cone.InWindow 1 (2 * ell) (t.val + 1) i}
    {hj : Cone.InWindow 1 (2 * ell) (s.val + 1) j} :
    eventAt t i hi a = eventAt s j hj b ↔ t.val = s.val ∧ i = j ∧ a = b := by
  constructor
  · intro h
    obtain ⟨rfl, hb⟩ := Sigma.mk.inj h
    exact ⟨rfl, Cone.encodeBit_eq_iff.mp (eq_of_heq hb)⟩
  · rintro ⟨ht, rfl, rfl⟩
    obtain rfl := Fin.ext ht
    rfl

def firstA {ell : ℕ} (hell : 0 < ell) : ExampleEvent ell :=
  eventAt ⟨0, by omega⟩ 1 (by simp [Cone.InWindow, Cone.radius]; omega) 0

def firstB {ell : ℕ} (hell : 0 < ell) : ExampleEvent ell :=
  eventAt ⟨0, by omega⟩ (-1) (by simp [Cone.InWindow, Cone.radius]; omega) 1

def secondA {ell : ℕ} (hell : 0 < ell) : ExampleEvent ell :=
  eventAt ⟨ell, by omega⟩ (1 - ell) (by simp [Cone.InWindow, Cone.radius]; omega) 0

theorem secondC_outside {ell : ℕ} (hell : 0 < ell) :
    ¬ Cone.InWindow 1 (2 * ell) (ell + 1) (-(ell : ℤ)) := by
  simp only [Cone.InWindow, Cone.radius, one_mul]
  omega

/-- One of the four global discrepancies is outside the observation cone. -/
theorem exampleResidual_support {ell : ℕ} (hell : 0 < ell) :
    support (exampleResidual ell) = {firstA hell, firstB hell, secondA hell} := by
  ext v
  obtain ⟨t, b⟩ := v
  obtain ⟨i, hi, a, rfl⟩ := Cone.exists_encodeBit b
  rw [mem_support, exampleResidual_at hell]
  change (residualProfile ell t i).bits a = true ↔ eventAt t i hi a ∈ _
  simp only [Finset.mem_insert, Finset.mem_singleton, firstA, firstB, secondA,
    eventAt_eq_iff]
  by_cases hz : t.val = 0
  · fin_cases a <;> simp [residualProfile, hz, (Nat.ne_of_gt hell).symm, Cell.bits, mark]
  · by_cases he : t.val = ell
    · have hn : i ≠ -(ell : ℤ) := by
        intro h
        apply secondC_outside hell
        simpa [h, he] using hi
      fin_cases a <;> simp [residualProfile, he, Nat.ne_of_gt hell, Cell.bits, mark, hn]
    · fin_cases a <;> simp [residualProfile, hz, he, Cell.bits]

theorem exampleResidual_card {ell : ℕ} (hell : 0 < ell) :
    (support (exampleResidual ell)).card = 3 := by
  rw [exampleResidual_support hell, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
  · rfl
  · simp [firstB, secondA, eventAt_eq_iff]
  · simp [firstA, firstB, secondA, eventAt_eq_iff, (Nat.ne_of_gt hell).symm]

end PredictionDepth.SparseCorrections.Collision
