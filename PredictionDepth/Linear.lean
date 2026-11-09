import PredictionDepth.CompiledComposition
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite binary linear evolution

The two-element Boolean ring is represented by one bit: addition is XOR and
multiplication is AND. Matrix multiplication is implemented by parallel dot
products, each a layer of AND gates followed by a balanced XOR reduction.
-/

namespace PredictionDepth.Linear
open FastComposition
open scoped BigOperators Matrix

abbrev F₂ := AsBoolRing Bool

def addGate (a b : Bool) : Bool := ofBoolRing (toBoolRing a + toBoolRing b)
def mulGate (a b : Bool) : Bool := ofBoolRing (toBoolRing a * toBoolRing b)

@[simp] theorem addGate_ring (a b : Bool) :
    toBoolRing (addGate a b) = (toBoolRing a + toBoolRing b : F₂) := rfl
@[simp] theorem mulGate_ring (a b : Bool) :
    toBoolRing (mulGate a b) = (toBoolRing a * toBoolRing b : F₂) := rfl

theorem addGate_eq_xor (a b : Bool) : addGate a b = Bool.xor a b := by
  cases a <;> cases b <;> rfl
theorem mulGate_eq_and (a b : Bool) : mulGate a b = (a && b) := by
  cases a <;> cases b <;> rfl

namespace Circuits

/-- Collect independent scalar outputs; the input wires may be shared. -/
def collect {n : ℕ} : {m : ℕ} → (Fin m → BinaryCircuit n 1) → BinaryCircuit n m
  | 0, _ => .wire (fun i => Fin.elim0 i)
  | m + 1, cs => .parallel (collect (fun i => cs i.castSucc)) (cs (Fin.last m))

theorem collect_eval {n m : ℕ} (cs : Fin m → BinaryCircuit n 1) (x : Bits n)
    (i : Fin m) : (collect cs).eval x i = (cs i).eval x 0 := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change joinBits _ _ (Fin.last m) = _
        simpa only [show Fin.last m = Fin.natAdd m (0 : Fin 1) from rfl] using
          joinBits_right ((collect (fun i => cs i.castSucc)).eval x)
            ((cs (Fin.last m)).eval x) (0 : Fin 1)
      · change joinBits _ _ j.castSucc = _
        rw [show j.castSucc = Fin.castAdd 1 j from rfl, joinBits_left]
        exact ih _ j

theorem collect_depth_le {n m D : ℕ} (cs : Fin m → BinaryCircuit n 1)
    (h : ∀ i, (cs i).depth ≤ D) : (collect cs).depth ≤ D := by
  induction m with
  | zero => simp [collect, BinaryCircuit.depth]
  | succ m ih =>
      simp only [collect, BinaryCircuit.depth]
      exact max_le (ih _ (fun i => h i.castSucc)) (h (Fin.last m))

theorem collect_gateCount_le {n m G : ℕ} (cs : Fin m → BinaryCircuit n 1)
    (h : ∀ i, (cs i).gateCount ≤ G) : (collect cs).gateCount ≤ m * G := by
  induction m with
  | zero => simp [collect, BinaryCircuit.gateCount]
  | succ m ih =>
      simp only [collect, BinaryCircuit.gateCount, Nat.succ_mul]
      exact Nat.add_le_add (ih _ (fun i => h i.castSucc)) (h (Fin.last m))

/-- A balanced XOR tree over a list of independently computed leaves. -/
def sumTree {n k : ℕ} (cs : Fin k → BinaryCircuit n 1) :
    ℕ → List (Fin k) → BinaryCircuit n 1
  | 0, [] => BinaryCircuit.constant (fun _ => false)
  | 0, i :: _ => cs i
  | d + 1, xs => .seq
      (.parallel (sumTree cs d (xs.take (2 ^ d))) (sumTree cs d (xs.drop (2 ^ d))))
      (.gate addGate)

theorem sumTree_eval {n k d : ℕ} (cs : Fin k → BinaryCircuit n 1)
    (xs : List (Fin k)) (hlen : xs.length ≤ 2 ^ d) (x : Bits n) :
    toBoolRing ((sumTree cs d xs).eval x 0) =
      (xs.map (fun i => toBoolRing ((cs i).eval x 0))).sum := by
  induction d generalizing xs with
  | zero =>
      cases xs with
      | nil => rfl
      | cons i xs =>
          have hx : xs = [] := by simpa using hlen
          subst xs
          simp [sumTree]
  | succ d ih =>
      change toBoolRing (addGate
        ((sumTree cs d (xs.take (2 ^ d))).eval x 0)
        ((sumTree cs d (xs.drop (2 ^ d))).eval x 0)) = _
      rw [addGate_ring, ih, ih]
      · rw [← List.sum_append, ← List.map_append, List.take_append_drop]
      · simp only [List.length_drop]
        have hp : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by omega
        omega
      · simp only [List.length_take]
        exact Nat.min_le_left _ _

theorem sumTree_depth_le {n k D : ℕ} (cs : Fin k → BinaryCircuit n 1)
    (h : ∀ i, (cs i).depth ≤ D) (d : ℕ) (xs : List (Fin k)) :
    (sumTree cs d xs).depth ≤ d + D := by
  induction d generalizing xs with
  | zero => cases xs <;> simp [sumTree, BinaryCircuit.constant, BinaryCircuit.depth, h]
  | succ d ih =>
      simp only [sumTree, BinaryCircuit.depth]
      have h₁ := ih (xs.take (2 ^ d))
      have h₂ := ih (xs.drop (2 ^ d))
      omega

theorem sumTree_gateCount_le {n k : ℕ} (cs : Fin k → BinaryCircuit n 1)
    (h : ∀ i, (cs i).gateCount ≤ 1) (d : ℕ) (xs : List (Fin k)) :
    (sumTree cs d xs).gateCount < 2 ^ (d + 1) := by
  induction d generalizing xs with
  | zero =>
      cases xs with
      | nil => change (0 : ℕ) < 2; decide
      | cons i xs =>
          change (cs i).gateCount < 2
          have := h i
          omega
  | succ d ih =>
      simp only [sumTree, BinaryCircuit.gateCount]
      have h₁ := ih (xs.take (2 ^ d))
      have h₂ := ih (xs.drop (2 ^ d))
      rw [pow_succ]
      omega

/-- One multiplication of two selected bits, using one AND gate. -/
def productTerm {m : ℕ} (a b : Fin m) : BinaryCircuit m 1 :=
  .seq (BinaryCircuit.select (fun p : Fin 2 => if p = 0 then a else b))
    (.gate mulGate)

@[simp] theorem productTerm_eval {m : ℕ} (a b : Fin m) (x : Bits m) :
    toBoolRing ((productTerm a b).eval x 0) =
      (toBoolRing (x a) * toBoolRing (x b) : F₂) := by
  rfl

@[simp] theorem productTerm_depth {m : ℕ} (a b : Fin m) :
    (productTerm a b).depth = 1 := rfl
@[simp] theorem productTerm_gateCount {m : ℕ} (a b : Fin m) :
    (productTerm a b).gateCount = 1 := rfl

/-- A binary dot product, including the zero-dimensional case. -/
def dot {m n : ℕ} (a b : Fin n → Fin m) : BinaryCircuit m 1 :=
  sumTree (fun k => productTerm (a k) (b k)) (Nat.clog 2 n) (List.finRange n)

theorem dot_eval {m n : ℕ} (a b : Fin n → Fin m) (x : Bits m) :
    toBoolRing ((dot a b).eval x 0) =
      ∑ k : Fin n, (toBoolRing (x (a k)) * toBoolRing (x (b k)) : F₂) := by
  rw [dot, sumTree_eval]
  · simp only [productTerm_eval]
    simpa only [← List.ofFn_eq_map] using
      (List.sum_ofFn (f := fun k => (toBoolRing (x (a k)) * toBoolRing (x (b k)) : F₂)))
  · simpa using Nat.le_pow_clog (by omega : 1 < (2 : ℕ)) n

theorem dot_depth_le {m n : ℕ} (a b : Fin n → Fin m) :
    (dot a b).depth ≤ Nat.clog 2 n + 1 :=
  sumTree_depth_le _ (fun _ => by simp) _ _

theorem dot_gateCount_le {m n : ℕ} (a b : Fin n → Fin m) :
    (dot a b).gateCount ≤ 4 * n + 1 := by
  have h := sumTree_gateCount_le (fun k => productTerm (a k) (b k))
    (fun _ => by simp) (Nat.clog 2 n) (List.finRange n)
  change (dot a b).gateCount < 2 ^ (Nat.clog 2 n + 1) at h
  by_cases hn : n ≤ 1
  · rw [Nat.clog_of_right_le_one hn] at h
    omega
  · have hp := Nat.pow_pred_clog_lt_self (by omega : 1 < (2 : ℕ)) (by omega : 1 < n)
    simp only [Nat.pred_eq_sub_one] at hp
    have hc := Nat.clog_pos (by omega : 1 < (2 : ℕ)) (by omega : 1 < n)
    have he : Nat.clog 2 n = (Nat.clog 2 n - 1) + 1 := by omega
    rw [he, pow_succ, pow_succ] at h
    omega

end Circuits

abbrev BinaryMatrix (n : ℕ) := Matrix (Fin n) (Fin n) F₂

def index {n : ℕ} (i j : Fin n) : Fin (n * n) := finProdFinEquiv (i, j)

def encode {n : ℕ} (A : BinaryMatrix n) : Bits (n * n) :=
  fun p => ofBoolRing (A (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)

@[simp] theorem encode_index {n : ℕ} (A : BinaryMatrix n) (i j : Fin n) :
    encode A (index i j) = ofBoolRing (A i j) := by simp [encode, index]

def denote {n : ℕ} (A : BinaryMatrix n) (x : Bits n) : Bits n :=
  fun i => ofBoolRing (A.mulVec (fun j => toBoolRing (x j)) i)

/-- Matrix multiplication realizes composition of binary linear evolution. -/
def realization {n : ℕ} (A : BinaryMatrix n) :
    Realization (Bits n) (BinaryMatrix n) (denote A) where
  identity := 1
  seed := A
  compose := (· * ·)
  denote := denote
  identity_correct := by funext x i; simp [denote]
  seed_correct := rfl
  compose_correct := by
    intro B C
    funext x i
    simp only [denote, Function.comp_apply, toBoolRing_ofBoolRing]
    rw [Matrix.mulVec_mulVec]

/-- Iterating the linear evolution agrees with the conventional matrix power. -/
theorem denote_pow {n : ℕ} (A : BinaryMatrix n) (T : ℕ) :
    denote (A ^ T) = (denote A)^[T] := by
  induction T with
  | zero => exact (realization A).identity_correct
  | succ T ih =>
      rw [pow_succ']
      calc
        denote (A * A ^ T) = denote A ∘ denote (A ^ T) :=
          (realization A).compose_correct A (A ^ T)
        _ = (denote A)^[T + 1] := by rw [ih, Function.iterate_succ']

def compositionCircuit (n : ℕ) : BinaryCircuit (n * n + n * n) (n * n) :=
  Circuits.collect (fun p => Circuits.dot
    (fun k => Fin.castAdd (n * n) (index (finProdFinEquiv.symm p).1 k))
    (fun k => Fin.natAdd (n * n) (index k (finProdFinEquiv.symm p).2)))

theorem compositionCircuit_eval (n : ℕ) (A B : BinaryMatrix n) :
    (compositionCircuit n).eval (joinBits (encode A) (encode B)) = encode (A * B) := by
  funext p
  rw [compositionCircuit, Circuits.collect_eval]
  apply (@toBoolRing Bool).injective
  rw [Circuits.dot_eval]
  simp only [joinBits_left, joinBits_right, encode, index, Equiv.symm_apply_apply,
    toBoolRing_ofBoolRing, Matrix.mul_apply]

theorem compositionCircuit_depth_le (n : ℕ) :
    (compositionCircuit n).depth ≤ Nat.clog 2 n + 1 :=
  Circuits.collect_depth_le _ (fun _ => Circuits.dot_depth_le _ _)

theorem compositionCircuit_gateCount_le (n : ℕ) :
    (compositionCircuit n).gateCount ≤ (n * n) * (4 * n + 1) :=
  Circuits.collect_gateCount_le _ (fun _ => Circuits.dot_gateCount_le _ _)

def observationCircuit {n : ℕ} (i : Fin n) : BinaryCircuit (n * n + n) 1 :=
  Circuits.dot (fun k => Fin.castAdd n (index i k)) (fun k => Fin.natAdd (n * n) k)

theorem observationCircuit_eval {n : ℕ} (i : Fin n) (A : BinaryMatrix n) (x : Bits n) :
    (observationCircuit i).eval (joinBits (encode A) x) 0 = denote A x i := by
  apply (@toBoolRing Bool).injective
  rw [observationCircuit, Circuits.dot_eval]
  simp [denote, Matrix.mulVec, dotProduct]

def initializationCircuit {n : ℕ} (A : BinaryMatrix n) :
    BinaryCircuit n (n * n + (n * n + n)) :=
  .parallel (BinaryCircuit.constant (encode A))
    (.parallel (BinaryCircuit.constant (encode (1 : BinaryMatrix n)))
      (BinaryCircuit.select id))

/-- A finite-width witness for Theorem A: matrices always use exactly `n²` bits. -/
def implementation {n : ℕ} (A : BinaryMatrix n) (i : Fin n) :
    Implementation (realization A) (fun x => x i) (n * n) where
  encode := encode
  initialization := initializationCircuit A
  initialization_correct := by intro x; rfl
  composition := compositionCircuit n
  composition_correct := compositionCircuit_eval n
  observation := observationCircuit i
  observation_correct := observationCircuit_eval i

/-- The concrete, shared, bounded-fan-in predictor for a binary linear system. -/
def predictor {n : ℕ} (A : BinaryMatrix n) (i : Fin n) (T : ℕ) : BinaryCircuit n 1 :=
  (implementation A i).predictor T

theorem predictor_correct {n : ℕ} (A : BinaryMatrix n) (i : Fin n) (T : ℕ) (x : Bits n) :
    (predictor A i T).eval x 0 = ((denote A)^[T] x) i :=
  (implementation A i).predictor_correct T x

theorem predictor_depth_le {n : ℕ} (A : BinaryMatrix n) (i : Fin n) (T : ℕ) :
    (predictor A i T).depth ≤
      2 * Nat.clog 2 (T + 1) * (Nat.clog 2 n + 1) + (Nat.clog 2 n + 1) := by
  have h := (implementation A i).predictor_depth_le T
  have hm := compositionCircuit_depth_le n
  have ho := Circuits.dot_depth_le
    (fun k => Fin.castAdd n (index i k)) (fun k => Fin.natAdd (n * n) k)
  change (observationCircuit i).depth ≤ Nat.clog 2 n + 1 at ho
  change (predictor A i T).depth ≤ (initializationCircuit A).depth +
    2 * Nat.clog 2 (T + 1) * (compositionCircuit n).depth + (observationCircuit i).depth at h
  have hinit : (initializationCircuit A).depth = 0 := rfl
  rw [hinit, Nat.zero_add] at h
  exact h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hm) ho)

theorem predictor_gateCount_le {n : ℕ} (A : BinaryMatrix n) (i : Fin n) (T : ℕ) :
    (predictor A i T).gateCount ≤
      2 * Nat.clog 2 (T + 1) * ((n * n) * (4 * n + 1)) + (4 * n + 1) := by
  have h := (implementation A i).predictor_gateCount_le T
  have hm := compositionCircuit_gateCount_le n
  have ho := Circuits.dot_gateCount_le
    (fun k => Fin.castAdd n (index i k)) (fun k => Fin.natAdd (n * n) k)
  change (observationCircuit i).gateCount ≤ 4 * n + 1 at ho
  change (predictor A i T).gateCount ≤ (initializationCircuit A).gateCount +
    2 * Nat.clog 2 (T + 1) * (compositionCircuit n).gateCount +
      (observationCircuit i).gateCount at h
  have hinit : (initializationCircuit A).gateCount = 0 := rfl
  rw [hinit, Nat.zero_add] at h
  exact h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hm) ho)

end PredictionDepth.Linear
