import Mathlib.Data.Nat.Log
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.SplitIfs

/-!
# Fast composition: the algebraic part of the prediction upper bound

A shared straight-line program computes a representation of `F^[T]` by repeated
squaring.  Its number of composition instructions is at most twice the binary
length of `T`.  A square uses the preceding register twice; it does not copy the
program that produced that register.

The resource bounds below are *primitive-operation* bounds.  Interpreting them
as Boolean-circuit bounds additionally requires implementations of initialization,
composition, and observation on bounded finite encodings, with the stated costs.
This file does not postulate that arbitrary semantic functions have cheap circuits.
Nor does algebraic closure alone establish a uniform circuit-family generator.
-/

namespace PredictionDepth.FastComposition

/-- A semantic representation of one-step evolution and function composition. -/
structure Realization (X R : Type*) (F : X → X) where
  identity : R
  seed : R
  compose : R → R → R
  denote : R → X → X
  identity_correct : denote identity = id
  seed_correct : denote seed = F
  compose_correct : ∀ a b, denote (compose a b) = denote a ∘ denote b

/-- A program with one mutable accumulator and a read-only seed register.
` square` reuses the accumulator as both inputs of one composition instruction. -/
inductive Program where
  | identity
  | square (previous : Program)
  | multiplySeed (previous : Program)
  deriving DecidableEq, Repr

namespace Program

/-- The number of composition instructions, with shared registers. -/
def operations : Program → ℕ
  | .identity => 0
  | .square p => operations p + 1
  | .multiplySeed p => operations p + 1

/-- The power of the evolution represented by the program. -/
def exponent : Program → ℕ
  | .identity => 0
  | .square p => exponent p + exponent p
  | .multiplySeed p => exponent p + 1

/-- Execute the register program in any semantic representation. -/
def run {X R : Type*} {F : X → X} (r : Realization X R F) : Program → R
  | .identity => r.identity
  | .square p => r.compose (run r p) (run r p)
  | .multiplySeed p => r.compose r.seed (run r p)

/-- Every generated representation has exactly its claimed iterate semantics. -/
theorem run_correct {X R : Type*} {F : X → X}
    (r : Realization X R F) (p : Program) :
    r.denote (run r p) = F^[exponent p] := by
  induction p with
  | identity => simpa [run, exponent] using r.identity_correct
  | square p ih =>
      simp only [run, exponent, r.compose_correct, ih, Function.iterate_add]
  | multiplySeed p ih =>
      simp only [run, exponent, r.compose_correct, r.seed_correct, ih,
        Function.iterate_succ']

/-- Each accumulator value that occurs during execution, in reverse time order. -/
def states {X R : Type*} {F : X → X} (r : Realization X R F) : Program → List R
  | .identity => [r.identity]
  | .square p => run r (.square p) :: states r p
  | .multiplySeed p => run r (.multiplySeed p) :: states r p

theorem states_length {X R : Type*} {F : X → X}
    (r : Realization X R F) (p : Program) :
    (states r p).length = operations p + 1 := by
  induction p <;> simp_all [states, operations]

end Program

/-- The numerical value of a little-endian binary digit list. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * binaryValue bs + if b then 1 else 0

/-- Compile little-endian bits to a shared repeated-squaring program. -/
def compileBits : List Bool → Program
  | [] => .identity
  | b :: bs =>
      let p := Program.square (compileBits bs)
      if b then .multiplySeed p else p

theorem compileBits_exponent (bs : List Bool) :
    (compileBits bs).exponent = binaryValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [compileBits, binaryValue, Program.exponent, ih] <;> omega

theorem compileBits_operations (bs : List Bool) :
    (compileBits bs).operations ≤ 2 * bs.length := by
  induction bs with
  | nil => simp [compileBits, Program.operations]
  | cons b bs ih =>
      cases b <;> simp [compileBits, Program.operations] <;> omega

/-- Canonical binary digits; zero uses the empty list. -/
def binaryDigits (n : ℕ) : List Bool :=
  if h : n = 0 then [] else decide (n % 2 = 1) :: binaryDigits (n / 2)
termination_by n
decreasing_by omega

theorem binaryDigits_value (n : ℕ) : binaryValue (binaryDigits n) = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      rw [binaryDigits]
      split_ifs with hn
      · simp [hn, binaryValue]
      · simp only [binaryValue]
        rw [ih (n / 2) (by omega)]
        by_cases hodd : n % 2 = 1 <;> simp [hodd] <;> omega

/-- The usual binary input length, with length zero at `T = 0`. -/
def bitLength (n : ℕ) : ℕ := (binaryDigits n).length

/-- Characterization of binary length, including the zero boundary case. -/
theorem bitLength_le_iff (n k : ℕ) : bitLength n ≤ k ↔ n < 2 ^ k := by
  induction k generalizing n with
  | zero =>
      rw [bitLength, binaryDigits]
      split_ifs with hn
      · simp [hn]
      · simp [hn]
  | succ k ih =>
      rw [bitLength, binaryDigits]
      split_ifs with hn
      · simp only [hn, List.length_nil, Nat.zero_le, true_iff]
        exact Nat.two_pow_pos _
      · simp only [List.length_cons, Nat.add_le_add_iff_right]
        change bitLength (n / 2) ≤ k ↔ n < 2 ^ (k + 1)
        rw [ih, pow_succ]
        omega

/-- Exact logarithmic identification: `bitLength T = ceil(log₂(T+1))`. -/
theorem bitLength_eq_clog (n : ℕ) : bitLength n = Nat.clog 2 (n + 1) := by
  apply Nat.le_antisymm
  · rw [bitLength_le_iff]
    have h := Nat.le_pow_clog (by omega : 1 < (2 : ℕ)) (n + 1)
    omega
  · rw [Nat.clog_le_iff_le_pow (by omega : 1 < (2 : ℕ))]
    have h := (bitLength_le_iff n (bitLength n)).mp le_rfl
    omega

/-- An executable repeated-squaring algorithm, uniform at the program level. -/
def compile (n : ℕ) : Program := compileBits (binaryDigits n)

theorem compile_exponent (n : ℕ) : (compile n).exponent = n := by
  simp [compile, compileBits_exponent, binaryDigits_value]

theorem compile_operations (n : ℕ) : (compile n).operations ≤ 2 * bitLength n :=
  compileBits_operations (binaryDigits n)

/-- Theorem A, semantic conclusion: the generated representation predicts exactly. -/
theorem fast_prediction_correct {X R Y : Type*} {F : X → X}
    (r : Realization X R F) (observe : X → Y) (n : ℕ) (x : X) :
    observe (r.denote ((compile n).run r) x) = observe (F^[n] x) := by
  rw [Program.run_correct, compile_exponent]

/-- A concrete closure obligation for an encoding length bound `L`.
This is an assumption about representations, not a consequence of semantics. -/
structure ClosedEncodingBound {X R : Type*} {F : X → X}
    (r : Realization X R F) (encodingLength : R → ℕ) (L : ℕ) : Prop where
  identity_le : encodingLength r.identity ≤ L
  seed_le : encodingLength r.seed ≤ L
  compose_le : ∀ a b, encodingLength a ≤ L → encodingLength b ≤ L →
    encodingLength (r.compose a b) ≤ L

/-- Closure proves all intermediate registers remain within the given bound. -/
theorem all_states_bounded {X R : Type*} {F : X → X}
    (r : Realization X R F) (encodingLength : R → ℕ) (L : ℕ)
    (h : ClosedEncodingBound r encodingLength L) (p : Program) :
    encodingLength (p.run r) ≤ L ∧
      ∀ a ∈ p.states r, encodingLength a ≤ L := by
  induction p with
  | identity => simpa [Program.run, Program.states] using h.identity_le
  | square p ih =>
      have hn : encodingLength ((Program.square p).run r) ≤ L :=
        h.compose_le _ _ ih.1 ih.1
      exact ⟨hn, by simpa only [Program.states, List.mem_cons] using
        (fun a (ha : a = (Program.square p).run r ∨ a ∈ p.states r) =>
          ha.elim (fun he => he ▸ hn) (ih.2 a))⟩
  | multiplySeed p ih =>
      have hn : encodingLength ((Program.multiplySeed p).run r) ≤ L :=
        h.compose_le _ _ h.seed_le ih.1
      exact ⟨hn, by simpa only [Program.states, List.mem_cons] using
        (fun a (ha : a = (Program.multiplySeed p).run r ∨ a ∈ p.states r) =>
          ha.elim (fun he => he ▸ hn) (ih.2 a))⟩

/-- Resource charges for implementations of the primitive operations.
The charges alone do not assert that those implementations exist. -/
structure PrimitiveCosts where
  identityDepth : ℕ
  seedDepth : ℕ
  compositionDepth : ℕ
  observationDepth : ℕ
  identityWork : ℕ
  seedWork : ℕ
  compositionWork : ℕ
  observationWork : ℕ
  deriving Repr

/-- Parallel initialization, followed by serial composition layers and observation. -/
def chargedDepth (c : PrimitiveCosts) (p : Program) : ℕ :=
  max c.identityDepth c.seedDepth + p.operations * c.compositionDepth +
    c.observationDepth

/-- Total work, counting a square as one call with two wires to the same register. -/
def chargedWork (c : PrimitiveCosts) (p : Program) : ℕ :=
  c.identityWork + c.seedWork + p.operations * c.compositionWork + c.observationWork

theorem fast_prediction_depth_bound (c : PrimitiveCosts) (n : ℕ) :
    chargedDepth c (compile n) ≤
      max c.identityDepth c.seedDepth + 2 * bitLength n * c.compositionDepth +
        c.observationDepth := by
  unfold chargedDepth
  exact Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (compile_operations n)) _) _

theorem fast_prediction_work_bound (c : PrimitiveCosts) (n : ℕ) :
    chargedWork c (compile n) ≤
      c.identityWork + c.seedWork + 2 * bitLength n * c.compositionWork +
        c.observationWork := by
  unfold chargedWork
  exact Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (compile_operations n)) _) _

/-- The logarithmic version of Theorem A, with initialization explicitly included. -/
theorem fast_prediction_logarithmic_depth (c : PrimitiveCosts) (n : ℕ) :
    chargedDepth c (compile n) ≤ max c.identityDepth c.seedDepth +
      2 * Nat.clog 2 (n + 1) * c.compositionDepth + c.observationDepth := by
  simpa [bitLength_eq_clog] using fast_prediction_depth_bound c n

/-- Linear endomorphisms give a concrete semantic representation.  This does
not assert matrix multiplication costs or a finite-field Boolean encoding. -/
def linearRealization {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (A : V →ₗ[K] V) : Realization V (V →ₗ[K] V) A where
  identity := LinearMap.id
  seed := A
  compose := LinearMap.comp
  denote := fun B => B
  identity_correct := rfl
  seed_correct := rfl
  compose_correct := fun _ _ => rfl

theorem linear_fast_prediction {K V : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V] (A : V →ₗ[K] V) (n : ℕ) (x : V) :
    ((compile n).run (linearRealization A)) x = (A : V → V)^[n] x := by
  exact fast_prediction_correct (linearRealization A) id n x

end PredictionDepth.FastComposition
