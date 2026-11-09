import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.FinRange

/-!
# Bounded fan-in prediction circuits

Depth is an upper bound: an input or constant may occur at any available depth.
Gates have arbitrary Boolean truth tables of arity `b`, so projections express
unused ports. Wires have no geometric restriction. `LayeredNetwork` below permits
sharing and is unfolded, without a depth increase, into this inductive model.
-/

namespace PredictionDepth

abbrev BooleanInput (n : ℕ) := Fin n → Bool

/-- A variable is essential if changing only that coordinate can change the result. -/
def Essential {n : ℕ} (f : BooleanInput n → Bool) (i : Fin n) : Prop :=
  ∃ x y, (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y

noncomputable def essentialInputs {n : ℕ} (f : BooleanInput n → Bool) : Finset (Fin n) :=
  by classical exact Finset.univ.filter (Essential f)

/-- Finite proof-carrying data for an information-dependency lower bound.
For each claimed variable the witness supplies two explicit assignments which
agree everywhere else and produce different outputs. All data domains are finite. -/
structure DependencyWitness {n : ℕ} (f : BooleanInput n → Bool) where
  coordinates : Finset (Fin n)
  left : Fin n → BooleanInput n
  right : Fin n → BooleanInput n
  agree : ∀ i ∈ coordinates, ∀ j, j ≠ i → left i j = right i j
  distinguish : ∀ i ∈ coordinates, f (left i) ≠ f (right i)

theorem DependencyWitness.sound {n : ℕ} {f : BooleanInput n → Bool}
    (w : DependencyWitness f) : w.coordinates ⊆ essentialInputs f := by
  classical
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ⟨w.left i, w.right i, w.agree i hi, w.distinguish i hi⟩⟩

/-- A circuit of fan-in at most `b` and depth at most `d`. -/
inductive BoundedCircuit (b n : ℕ) : ℕ → Type
  | input {d : ℕ} (i : Fin n) : BoundedCircuit b n d
  | constant {d : ℕ} (v : Bool) : BoundedCircuit b n d
  | gate {d : ℕ} (op : (Fin b → Bool) → Bool)
      (args : Fin b → BoundedCircuit b n d) : BoundedCircuit b n (d + 1)

namespace BoundedCircuit

def eval {b n d : ℕ} : BoundedCircuit b n d → BooleanInput n → Bool
  | .input i, x => x i
  | .constant v, _ => v
  | .gate op args, x => op (fun i => (args i).eval x)

def support {b n d : ℕ} : BoundedCircuit b n d → Finset (Fin n)
  | .input i => {i}
  | .constant _ => ∅
  | .gate _ args => Finset.univ.biUnion (fun i => (args i).support)

def gateCount {b n d : ℕ} : BoundedCircuit b n d → ℕ
  | .input _ => 0
  | .constant _ => 0
  | .gate _ args => 1 + ∑ i, (args i).gateCount

theorem eval_eq_of_agree {b n d : ℕ} (c : BoundedCircuit b n d)
    (x y : BooleanInput n) (h : ∀ i ∈ c.support, x i = y i) : c.eval x = c.eval y := by
  induction c with
  | input i => exact h i (by simp [support])
  | constant v => rfl
  | gate op args ih =>
      apply congrArg op
      funext i
      apply ih i
      intro j hj
      exact h j (by simp only [support, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact ⟨i, hj⟩)

theorem essential_subset_support {b n d : ℕ} (c : BoundedCircuit b n d) :
    essentialInputs c.eval ⊆ c.support := by
  classical
  intro i hi
  by_contra hn
  obtain ⟨x, y, hxy, hne⟩ := (Finset.mem_filter.mp hi).2
  apply hne
  apply c.eval_eq_of_agree x y
  intro j hj
  apply hxy j
  intro heq
  subst j
  exact hn hj

theorem support_card_le {b n d : ℕ} (hb : 1 ≤ b) (c : BoundedCircuit b n d) :
    c.support.card ≤ b ^ d := by
  induction c with
  | @input d i => simpa [support] using (Nat.one_le_pow d b hb)
  | constant v => simp [support]
  | @gate d op args ih =>
      calc
        (Finset.univ.biUnion fun i => (args i).support).card
            ≤ ∑ i : Fin b, (args i).support.card := Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin b, b ^ d := Finset.sum_le_sum (fun i _ => ih i)
        _ = b ^ (d + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Theorem C, in its stronger integer form. It is independent of circuit size. -/
theorem essential_count_le_pow {b n d : ℕ} (hb : 1 ≤ b) (c : BoundedCircuit b n d) :
    (essentialInputs c.eval).card ≤ b ^ d :=
  (Finset.card_le_card c.essential_subset_support).trans (c.support_card_le hb)

theorem essential_depth_lower_bound {b n d : ℕ} (hb : 1 < b)
    (c : BoundedCircuit b n d) : Nat.clog b (essentialInputs c.eval).card ≤ d :=
  (Nat.clog_le_iff_le_pow hb).mpr (c.essential_count_le_pow (by omega))

end BoundedCircuit

/-- A finite layered DAG. Every layer may share arbitrary predecessors; `width`
is unrestricted. The initial layer consists of constants and input wires. -/
structure LayeredNetwork (b n d : ℕ) where
  width : ℕ
  output : Fin width
  initial : Fin width → Sum Bool (Fin n)
  wiring : Fin d → Fin width → Fin b → Fin width
  operation : Fin d → Fin width → (Fin b → Bool) → Bool

namespace LayeredNetwork

def unfoldNode {b n d : ℕ} (N : LayeredNetwork b n d) :
    (t : ℕ) → t ≤ d → Fin N.width → BoundedCircuit b n t
  | 0, _, v => match N.initial v with
      | .inl a => .constant a
      | .inr i => .input i
  | t + 1, h, v => .gate (N.operation ⟨t, by omega⟩ v)
      (fun p => N.unfoldNode t (by omega) (N.wiring ⟨t, by omega⟩ v p))

def unfold {b n d : ℕ} (N : LayeredNetwork b n d) : BoundedCircuit b n d :=
  N.unfoldNode d le_rfl N.output

def run {b n d : ℕ} (N : LayeredNetwork b n d) (x : BooleanInput n) :
    (t : ℕ) → t ≤ d → Fin N.width → Bool
  | 0, _, v => match N.initial v with
      | .inl a => a
      | .inr i => x i
  | t + 1, h, v => N.operation ⟨t, by omega⟩ v
      (fun p => N.run x t (by omega) (N.wiring ⟨t, by omega⟩ v p))

def eval {b n d : ℕ} (N : LayeredNetwork b n d) (x : BooleanInput n) : Bool :=
  N.run x d le_rfl N.output

theorem unfoldNode_eval {b n d : ℕ} (N : LayeredNetwork b n d)
    (x : BooleanInput n) (t : ℕ) (h : t ≤ d) (v : Fin N.width) :
    (N.unfoldNode t h v).eval x = N.run x t h v := by
  induction t generalizing v with
  | zero => simp only [unfoldNode, run]; cases N.initial v <;> rfl
  | succ t ih =>
      simp only [unfoldNode, BoundedCircuit.eval, run]
      congr 1
      funext p
      exact ih (by omega) _

theorem unfold_eval {b n d : ℕ} (N : LayeredNetwork b n d) : N.unfold.eval = N.eval := by
  funext x
  exact N.unfoldNode_eval x d le_rfl N.output

/-- The fan-in bound holds also with arbitrary sharing (unfolding may enlarge size). -/
theorem essential_count_le_pow {b n d : ℕ} (hb : 1 ≤ b) (N : LayeredNetwork b n d) :
    (essentialInputs N.eval).card ≤ b ^ d := by
  rw [← N.unfold_eval]
  exact N.unfold.essential_count_le_pow hb

theorem essential_depth_lower_bound {b n d : ℕ} (hb : 1 < b)
    (N : LayeredNetwork b n d) : Nat.clog b (essentialInputs N.eval).card ≤ d :=
  (Nat.clog_le_iff_le_pow hb).mpr (N.essential_count_le_pow (by omega))

end LayeredNetwork

/-- Theorem C from explicit finite dependency data, for arbitrary shared wiring. -/
theorem DependencyWitness.network_depth_bound {b n d : ℕ} {f : BooleanInput n → Bool}
    (w : DependencyWitness f) (hb : 1 < b) (N : LayeredNetwork b n d)
    (hN : N.eval = f) : Nat.clog b w.coordinates.card ≤ d := by
  apply (Nat.clog_le_iff_le_pow hb).mpr
  calc
    w.coordinates.card ≤ (essentialInputs f).card := Finset.card_le_card w.sound
    _ = (essentialInputs N.eval).card := by rw [hN]
    _ ≤ b ^ d := N.essential_count_le_pow (by omega)

theorem DependencyWitness.circuit_depth_bound {b n d : ℕ} {f : BooleanInput n → Bool}
    (w : DependencyWitness f) (hb : 1 < b) (c : BoundedCircuit b n d)
    (hc : c.eval = f) : Nat.clog b w.coordinates.card ≤ d := by
  apply (Nat.clog_le_iff_le_pow hb).mpr
  calc
    w.coordinates.card ≤ (essentialInputs f).card := Finset.card_le_card w.sound
    _ = (essentialInputs c.eval).card := by rw [hc]
    _ ≤ b ^ d := c.essential_count_le_pow (by omega)

def boolOr (n : ℕ) (x : BooleanInput n) : Bool := decide (∃ i, x i = true)

theorem boolOr_essential {n : ℕ} (i : Fin n) : Essential (boolOr n) i := by
  refine ⟨fun _ => false, fun j => decide (j = i), ?_, ?_⟩
  · intro j hj; simp [hj]
  · simp [boolOr]

/-- OR has a finite witness naming every input: all false versus one true bit. -/
def boolOr_dependencyWitness (n : ℕ) : DependencyWitness (boolOr n) where
  coordinates := Finset.univ
  left := fun _ _ => false
  right := fun i j => decide (j = i)
  agree := by intro i _ j hji; simp [hji]
  distinguish := by intro i _; simp [boolOr]

theorem boolOr_essential_count (n : ℕ) : (essentialInputs (boolOr n)).card = n := by
  classical
  have h : essentialInputs (boolOr n) = Finset.univ := by
    ext i
    simp [essentialInputs, boolOr_essential]
  simp [h]

theorem boolOr_depth_lower_bound {n d : ℕ} (c : BoundedCircuit 2 n d)
    (hc : c.eval = boolOr n) : Nat.clog 2 n ≤ d := by
  have h := c.essential_depth_lower_bound (by omega)
  simpa [hc, boolOr_essential_count] using h

namespace BoundedCircuit

/-- A balanced binary OR tree, padded with false leaves. -/
def orTree {n : ℕ} : (d : ℕ) → List (Fin n) → BoundedCircuit 2 n d
  | 0, [] => .constant false
  | 0, i :: _ => .input i
  | d + 1, xs => .gate (fun v => v 0 || v 1)
      (fun i => if i = 0 then orTree d (xs.take (2 ^ d)) else orTree d (xs.drop (2 ^ d)))

theorem orTree_eval {n d : ℕ} (xs : List (Fin n)) (hlen : xs.length ≤ 2 ^ d)
    (x : BooleanInput n) : (orTree d xs).eval x = xs.any x := by
  induction d generalizing xs with
  | zero =>
      cases xs with
      | nil => rfl
      | cons i xs =>
          have hx : xs = [] := by simpa using hlen
          subst xs
          simp [orTree, eval]
  | succ d ih =>
      simp only [orTree, eval, Fin.isValue, ↓reduceIte, Fin.reduceEq]
      rw [ih, ih]
      · rw [← List.any_append, List.take_append_drop]
      · simp only [List.length_drop]
        have hp : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by omega
        omega
      · simp only [List.length_take]
        exact Nat.min_le_left _ _

/-- The padded tree has exactly one gate for each non-leaf node. -/
theorem orTree_gateCount {n : ℕ} (d : ℕ) (xs : List (Fin n)) :
    (orTree d xs).gateCount = 2 ^ d - 1 := by
  induction d generalizing xs with
  | zero => cases xs <;> simp [orTree, gateCount]
  | succ d ih =>
      simp only [orTree, gateCount, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
        Fin.reduceEq, ih, pow_succ]
      have hp : 0 < 2 ^ d := Nat.pow_pos (by omega)
      omega

end BoundedCircuit

/-- A total explicit optimal-depth OR circuit, including the empty input. -/
def orCircuit (n : ℕ) : BoundedCircuit 2 n (Nat.clog 2 n) :=
  BoundedCircuit.orTree (Nat.clog 2 n) (List.finRange n)

theorem orCircuit_eval (n : ℕ) : (orCircuit n).eval = boolOr n := by
  funext x
  rw [orCircuit, BoundedCircuit.orTree_eval]
  · apply Bool.eq_iff_iff.mpr
    simp [boolOr, List.any_eq_true]
  · simpa using Nat.le_pow_clog (by omega : 1 < (2 : ℕ)) n

theorem orCircuit_gateCount (n : ℕ) :
    (orCircuit n).gateCount = 2 ^ Nat.clog 2 n - 1 :=
  BoundedCircuit.orTree_gateCount _ _

/-- Explicit linear-size bound. Empty and singleton inputs need no gate. -/
theorem orCircuit_linear_size (n : ℕ) : (orCircuit n).gateCount ≤ 2 * n := by
  rw [orCircuit_gateCount]
  by_cases hn : n ≤ 1
  · simp [Nat.clog_of_right_le_one hn]
  · have hp := Nat.pow_pred_clog_lt_self (by omega : 1 < (2 : ℕ)) (by omega : 1 < n)
    simp only [Nat.pred_eq_sub_one] at hp
    have hc := Nat.clog_pos (by omega : 1 < (2 : ℕ)) (by omega : 1 < n)
    have he : Nat.clog 2 n = (Nat.clog 2 n - 1) + 1 := by omega
    rw [he, pow_succ]
    omega

/-- The exact optimum is the ceiling logarithm, not just an asymptotic estimate. -/
theorem boolOr_exact_depth (n : ℕ) :
    IsLeast {d | ∃ c : BoundedCircuit 2 n d, c.eval = boolOr n} (Nat.clog 2 n) := by
  constructor
  · exact ⟨orCircuit n, orCircuit_eval n⟩
  · rintro d ⟨c, hc⟩
    exact boolOr_depth_lower_bound c hc

/-- The same optimal lower bound allows unrestricted sharing in a layered DAG. -/
theorem boolOr_network_depth_lower_bound {n d : ℕ} (N : LayeredNetwork 2 n d)
    (hN : N.eval = boolOr n) : Nat.clog 2 n ≤ d := by
  have h := N.essential_depth_lower_bound (by omega)
  simpa [hN, boolOr_essential_count] using h

end PredictionDepth
