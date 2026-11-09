import CslibFrontier.Computability.Circuit.Pi
import Cslib.Computability.Circuit.Boolean.Basic
import PredictionDepth.Complexity.BalancedReduction
import PredictionDepth.Complexity.Reachability

/-! Regular De Morgan circuits for Boolean matrix powering. -/

namespace PredictionDepth.StandardComplexity.StandardPower
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open ParallelReachability RegularReduction

abbrev width (N : ℕ) : ℕ := 2 ^ N.size
abbrev layerWidth (N : ℕ) : ℕ := (N * N) * width N

def slot {N P : ℕ} (entry : Fin (N * N)) (j : Fin P) : Fin ((N * N) * P) :=
  finProdFinEquiv (entry, j)

def expanded {N P : ℕ} (M : Fin (N * N) → Fin P → Bool) :
    Fin ((N * N) * P) → Bool :=
  fun q => M (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

@[simp] theorem expanded_slot {N P : ℕ} (M : Fin (N * N) → Fin P → Bool)
    (i : Fin (N * N)) (j : Fin P) : expanded M (slot i j) = M i j := by
  simp [expanded, slot]

def productVector {N P : ℕ} (R : Relation N) (entry : Fin (N * N)) : Fin P → Bool :=
  padTo (fun k => R (finProdFinEquiv.symm entry).1 k && R k (finProdFinEquiv.symm entry).2)

def productEntry {N P : ℕ} (entry : Fin (N * N)) (j : Fin P) :
    Circuit signature (N * N) 1 :=
  if h : j.val < N then
    Circuit.oneGate .and ![index (finProdFinEquiv.symm entry).1 ⟨j.val, h⟩,
      index ⟨j.val, h⟩ (finProdFinEquiv.symm entry).2]
  else Circuit.oneGate (.const false) Fin.elim0

def products (N P : ℕ) : Circuit signature (N * N) ((N * N) * P) :=
  Circuit.pi fun q => productEntry (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

theorem productEntry_eval {N P : ℕ} (R : Relation N) (entry : Fin (N * N)) (j : Fin P) :
    (productEntry entry j).eval interpretation (encode R) 0 = productVector R entry j := by
  unfold productEntry productVector padTo
  split_ifs <;> simp [Circuit.eval_oneGate, interpretation]

theorem products_eval {N P : ℕ} (R : Relation N) :
    (products N P).eval interpretation (encode R) = expanded (productVector (P := P) R) := by
  funext q
  simp only [products, Circuit.eval_pi, expanded, productEntry_eval]

@[simp] theorem productEntry_size {N P : ℕ} (entry : Fin (N * N)) (j : Fin P) :
    (productEntry entry j).size = 1 := by unfold productEntry; split <;> simp

@[simp] theorem productEntry_depth {N P : ℕ} (entry : Fin (N * N)) (j : Fin P) :
    (productEntry entry j).depth = 1 := by unfold productEntry; split <;> simp

@[simp] theorem products_size (N P : ℕ) : (products N P).size = (N * N) * P := by
  simp [products]

theorem products_depth_le (N P : ℕ) : (products N P).depth ≤ 1 :=
  Circuit.depth_pi_le _ (fun _ => by simp)

def mergeEntry {N P : ℕ} (entry : Fin (N * N)) (j : Fin P) :
    Circuit signature ((N * N) * P) 1 :=
  if h : 2 * j.val + 1 < P then
    Circuit.oneGate .or ![slot entry ⟨2 * j.val, by omega⟩, slot entry ⟨2 * j.val + 1, h⟩]
  else Circuit.oneGate (.const false) Fin.elim0

def merge (N P : ℕ) : Circuit signature ((N * N) * P) ((N * N) * P) :=
  Circuit.pi fun q => mergeEntry (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

theorem mergeEntry_eval {N P : ℕ} (M : Fin (N * N) → Fin P → Bool)
    (entry : Fin (N * N)) (j : Fin P) :
    (mergeEntry entry j).eval interpretation (expanded M) 0 = mergeVector (M entry) j := by
  unfold mergeEntry mergeVector
  split_ifs <;> simp [Circuit.eval_oneGate, interpretation]

theorem merge_eval {N P : ℕ} (M : Fin (N * N) → Fin P → Bool) :
    (merge N P).eval interpretation (expanded M) = expanded (fun i => mergeVector (M i)) := by
  funext q
  simp only [merge, Circuit.eval_pi, expanded, mergeEntry_eval]

@[simp] theorem mergeEntry_size {N P : ℕ} (entry : Fin (N * N)) (j : Fin P) :
    (mergeEntry entry j).size = 1 := by unfold mergeEntry; split <;> simp

@[simp] theorem mergeEntry_depth {N P : ℕ} (entry : Fin (N * N)) (j : Fin P) :
    (mergeEntry entry j).depth = 1 := by unfold mergeEntry; split <;> simp

@[simp] theorem merge_size (N P : ℕ) : (merge N P).size = (N * N) * P := by
  simp [merge]

theorem merge_depth_le (N P : ℕ) : (merge N P).depth ≤ 1 :=
  Circuit.depth_pi_le _ (fun _ => by simp)

def mergeRounds (N P : ℕ) : ℕ → Circuit signature ((N * N) * P) ((N * N) * P)
  | 0 => Circuit.wiring signature id
  | d + 1 => (merge N P).comp (mergeRounds N P d)

theorem mergeRounds_eval {N P : ℕ} (M : Fin (N * N) → Fin P → Bool) (d : ℕ) :
    (mergeRounds N P d).eval interpretation (expanded M) =
      expanded (fun i => reduceVector d (M i)) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [mergeRounds, Circuit.eval_comp, ih, merge_eval, reduceVector]

@[simp] theorem mergeRounds_size (N P d : ℕ) :
    (mergeRounds N P d).size = d * ((N * N) * P) := by
  induction d with
  | zero => simp [mergeRounds]
  | succ d ih => simp [mergeRounds, ih, Nat.succ_mul, Nat.add_comm]

theorem mergeRounds_depth_le (N P d : ℕ) : (mergeRounds N P d).depth ≤ d := by
  induction d with
  | zero => simp [mergeRounds]
  | succ d ih =>
      exact (Circuit.depth_comp_le _ _).trans
        (by have hm := merge_depth_le N P; omega)

def selectRoots (N : ℕ) : Circuit signature (layerWidth N) (N * N) :=
  Circuit.wiring signature (fun i => slot i ⟨0, Nat.two_pow_pos _⟩)

def square (N : ℕ) : Circuit signature (N * N) (N * N) :=
  (selectRoots N).comp ((mergeRounds N (width N) N.size).comp (products N (width N)))

theorem square_eval {N : ℕ} (R : Relation N) :
    (square N).eval interpretation (encode R) = encode (compose R R) := by
  funext entry
  by_cases hN : N = 0
  · subst N
    exact Fin.elim0 entry
  have hd : 0 < N.size := by simpa using Nat.size_pos.mpr (Nat.pos_of_ne_zero hN)
  simp only [square, Circuit.eval_comp, products_eval, mergeRounds_eval,
    selectRoots, Circuit.eval_wiring, Function.comp_apply, expanded_slot]
  apply Bool.eq_iff_iff.mpr
  unfold productVector
  rw [reduceVector_padded_root_true_iff hd (Nat.lt_size_self N).le]
  simp only [encode, compose_true, Bool.and_eq_true]

@[simp] theorem square_size (N : ℕ) :
    (square N).size = (N.size + 1) * layerWidth N := by
  simp [square, selectRoots, layerWidth, Nat.add_mul, Nat.add_comm]

theorem square_depth_le (N : ℕ) : (square N).depth ≤ N.size + 1 := by
  apply (Circuit.depth_comp_le _ _).trans
  simp only [selectRoots, Circuit.depth_wiring, Nat.zero_add]
  exact (Circuit.depth_comp_le _ _).trans
    (Nat.add_le_add (mergeRounds_depth_le N (width N) N.size) (products_depth_le N (width N)))

def power (N : ℕ) : ℕ → Circuit signature (N * N) (N * N)
  | 0 => Circuit.wiring signature id
  | d + 1 => (square N).comp (power N d)

theorem power_eval {N : ℕ} (R : Relation N) (d : ℕ) :
    (power N d).eval interpretation (encode R) = encode (squares R d) := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [power, Circuit.eval_comp, ih, square_eval, squares]

@[simp] theorem power_size (N d : ℕ) :
    (power N d).size = d * ((N.size + 1) * layerWidth N) := by
  induction d with
  | zero => simp [power]
  | succ d ih => simp [power, ih, Nat.succ_mul, Nat.add_comm]

theorem power_depth_le (N d : ℕ) : (power N d).depth ≤ d * (N.size + 1) := by
  induction d with
  | zero => simp [power]
  | succ d ih =>
      apply (Circuit.depth_comp_le _ _).trans
      simpa only [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (square_depth_le N) ih

/-- Select reachable accepting vertices, padded to the same regular width as
the squaring blocks. Repetition across entry blocks keeps one uniform layout. -/
def acceptingEntry {N : ℕ} (start : Fin N) (accept : Fin N → Bool)
    (j : Fin (width N)) : Circuit signature (N * N) 1 :=
  if h : j.val < N then
    if accept ⟨j.val, h⟩ then
      Circuit.oneGate .and (fun _ => index start ⟨j.val, h⟩)
    else Circuit.oneGate (.const false) Fin.elim0
  else Circuit.oneGate (.const false) Fin.elim0

def acceptingLeaves {N : ℕ} (start : Fin N) (accept : Fin N → Bool) :
    Circuit signature (N * N) (layerWidth N) :=
  Circuit.pi fun q => acceptingEntry start accept (finProdFinEquiv.symm q).2

theorem acceptingEntry_eval {N : ℕ} (start : Fin N) (accept : Fin N → Bool)
    (R : Relation N) (j : Fin (width N)) :
    (acceptingEntry start accept j).eval interpretation (encode R) 0 =
      padTo (fun k => accept k && R start k) j := by
  unfold acceptingEntry padTo
  split_ifs <;> simp_all [Circuit.eval_oneGate, interpretation]

theorem acceptingLeaves_eval {N : ℕ} (start : Fin N) (accept : Fin N → Bool)
    (R : Relation N) :
    (acceptingLeaves start accept).eval interpretation (encode R) =
      expanded (fun _ : Fin (N * N) => padTo (P := width N) (fun k => accept k && R start k)) := by
  funext q
  simp only [acceptingLeaves, Circuit.eval_pi, expanded, acceptingEntry_eval]

@[simp] theorem acceptingEntry_size {N : ℕ} (start : Fin N) (accept : Fin N → Bool)
    (j : Fin (width N)) : (acceptingEntry start accept j).size = 1 := by
  unfold acceptingEntry
  split_ifs <;> simp

theorem acceptingEntry_depth {N : ℕ} (start : Fin N) (accept : Fin N → Bool)
    (j : Fin (width N)) : (acceptingEntry start accept j).depth = 1 := by
  unfold acceptingEntry
  split_ifs <;> simp

@[simp] theorem acceptingLeaves_size {N : ℕ} (start : Fin N) (accept : Fin N → Bool) :
    (acceptingLeaves start accept).size = layerWidth N := by
  simp [acceptingLeaves, layerWidth]

theorem acceptingLeaves_depth_le {N : ℕ} (start : Fin N) (accept : Fin N → Bool) :
    (acceptingLeaves start accept).depth ≤ 1 :=
  Circuit.depth_pi_le _ (fun _ => (acceptingEntry_depth _ _ _).le)

def rootSelector {N : ℕ} (start : Fin N) : Circuit signature (layerWidth N) 1 :=
  Circuit.wiring signature (fun _ => slot (index start start) ⟨0, Nat.two_pow_pos _⟩)

/-- Actual De Morgan reachability decider. `start` also certifies `N>0`. -/
def decider {N : ℕ} (start : Fin N) (accept : Fin N → Bool) : Circuit signature (N * N) 1 :=
  (rootSelector start).comp
    ((mergeRounds N (width N) N.size).comp
      ((acceptingLeaves start accept).comp (power N N.size)))

theorem decider_eval_true_iff {N : ℕ} (start : Fin N) (accept : Fin N → Bool)
    (R : Relation N) :
    (decider start accept).eval interpretation (encode R) 0 = true ↔
      ∃ j, accept j = true ∧ squares R N.size start j = true := by
  have hd : 0 < N.size := Nat.size_pos.mpr (Nat.zero_lt_of_lt start.isLt)
  simp only [decider, Circuit.eval_comp, power_eval, acceptingLeaves_eval,
    mergeRounds_eval, rootSelector, Circuit.eval_wiring, Function.comp_apply, expanded_slot]
  rw [reduceVector_padded_root_true_iff hd (Nat.lt_size_self N).le]
  simp only [Bool.and_eq_true]

/-- Finite configuration-graph reachability, with all length cases covered. -/
theorem decider_reachability {N : ℕ} (start : Fin N) (accept : Fin N → Bool)
    (R : Relation N) (hr : ∀ i, R i i = true) :
    (decider start accept).eval interpretation (encode R) 0 = true ↔
      ∃ j, accept j = true ∧ Relation.ReflTransGen (fun i j => R i j = true) start j := by
  rw [decider_eval_true_iff]
  apply exists_congr
  intro j
  rw [reachable_iff_squares hr (Nat.lt_size_self N).le]

theorem decider_size {N : ℕ} (start : Fin N) (accept : Fin N → Bool) :
    (decider start accept).size = (N.size + 1) ^ 2 * layerWidth N := by
  simp only [decider, Circuit.size_comp, rootSelector, Circuit.size_wiring,
    mergeRounds_size, acceptingLeaves_size, power_size]
  dsimp only [layerWidth]
  ring

theorem decider_depth_le {N : ℕ} (start : Fin N) (accept : Fin N → Bool) :
    (decider start accept).depth ≤ (N.size + 1) ^ 2 := by
  have h₁ := Circuit.depth_comp_le (acceptingLeaves start accept) (power N N.size)
  have h₂ := Circuit.depth_comp_le (mergeRounds N (width N) N.size)
    ((acceptingLeaves start accept).comp (power N N.size))
  have h₃ := Circuit.depth_comp_le (rootSelector start)
    ((mergeRounds N (width N) N.size).comp
      ((acceptingLeaves start accept).comp (power N N.size)))
  have hp := power_depth_le N N.size
  have hl := acceptingLeaves_depth_le start accept
  have hm := mergeRounds_depth_le N (width N) N.size
  have hz : (rootSelector start).depth = 0 := Circuit.depth_wiring _
  change (decider start accept).depth ≤ _ at h₃
  rw [hz] at h₃
  calc
    (decider start accept).depth ≤
        0 + (N.size + (1 + N.size * (N.size + 1))) :=
      h₃.trans (Nat.add_le_add_left
        (h₂.trans (Nat.add_le_add hm (h₁.trans (Nat.add_le_add hl hp)))) 0)
    _ = (N.size + 1) ^ 2 := by ring

end PredictionDepth.StandardComplexity.StandardPower
