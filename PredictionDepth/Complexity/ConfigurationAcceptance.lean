import PredictionDepth.Complexity.AdjacencyCode
import PredictionDepth.Complexity.Reachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Bounds

/-!
# Configuration acceptance is finite reflexive reachability

This connects the native finite-machine configuration graph to the Boolean
matrix relation used by repeated squaring. Adding diagonal edges changes no
reachability fact; restricting to the proved finite vertex bound loses no
reachable configuration.
-/

namespace PredictionDepth.StandardComplexity.ConfigurationAcceptance
open FastComposition
open Turing.MultiTapeNTM ConfigurationGraph

/-- Adding identity edges does not change reflexive-transitive reachability. -/
theorem reachable_with_diagonal {α : Type*} (R : α → α → Prop) (a b : α) :
    Relation.ReflTransGen (fun x y => x = y ∨ R x y) a b ↔
      Relation.ReflTransGen R a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hstep ih =>
      rcases hstep with heq | hR
      · subst heq; exact ih
      · exact ih.tail hR
  · exact Relation.ReflTransGen.mono (fun _ _ h => Or.inr h) a b

/-- A natural-number graph whose start-reachable vertices all lie below `N`
has exactly the same reachability after restricting its vertices to `Fin N`. -/
theorem reachable_restrict_fin {N start target : ℕ} {R : ℕ → ℕ → Prop}
    (hbound : ∀ v, Relation.ReflTransGen R start v → v < N)
    (hs : start < N) (ht : target < N) :
    Relation.ReflTransGen (fun a b : Fin N => R a.val b.val) ⟨start, hs⟩ ⟨target, ht⟩ ↔
      Relation.ReflTransGen R start target := by
  constructor
  · exact Relation.ReflTransGen.lift Fin.val (fun _ _ h => h) _ _
  · intro h
    induction h with
    | refl => exact .refl
    | @tail a b h hstep ih =>
      have ha := hbound a h
      exact (ih ha).tail hstep

variable {k : ℕ} {State : Type} [Fintype State]

def graphRadix (State : Type) [Fintype State] (c n : ℕ) : ℕ :=
  radix (radixExponent State c) n

def vertexCount (k : ℕ) (State : Type) [Fintype State] (c n : ℕ) : ℕ :=
  vertexBound (k := k) (graphRadix State c n)

theorem vertexCount_pos (c n : ℕ) : 0 < vertexCount k State c n :=
  Nat.pow_pos (Nat.pow_pos (by omega))

/-- Modulo makes the selector total for every machine and length. For any
actual space-bounded run, `source_val` proves that this does not change the ID. -/
noncomputable def source (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) :
    Fin (vertexCount k State c n) :=
  ⟨startID tm (graphRadix State c n) % vertexCount k State c n,
    Nat.mod_lt _ (vertexCount_pos c n)⟩

noncomputable def acceptsVertex (c n : ℕ) (v : Fin (vertexCount k State c n)) : Bool :=
  bad (k := k) (State := State) (graphRadix State c n) n v.val

/-- The finite graph includes identity edges so walks can be padded. -/
noncomputable def graph (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) (x : Bits n) :
    ParallelReachability.Relation (vertexCount k State c n) :=
  fun u v => if u = v then true else
    edgeWithSymbol tm (graphRadix State c n) n u.val v.val
      (List.ofFn x)[queryIndex (k := k) (graphRadix State c n) u.val]?

@[simp] theorem graph_refl (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ)
    (x : Bits n) (u : Fin (vertexCount k State c n)) : graph tm c n x u u = true := by
  simp [graph]

theorem graph_true_iff (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ)
    (x : Bits n) (u v : Fin (vertexCount k State c n)) :
    graph tm c n x u v = true ↔ u = v ∨
      Edge tm (graphRadix State c n) (List.ofFn x) u.val v.val := by
  by_cases h : u = v <;> simp [graph, h, Edge]

theorem reachable_bound (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) (x : Bits n)
    (hs : tm.RunsInSpace (List.ofFn x) (c * (Nat.log2 n + 1))) {v : ℕ}
    (hv : Relation.ReflTransGen (Edge tm (graphRadix State c n) (List.ofFn x))
      (startID tm (graphRadix State c n)) v) : v < vertexCount k State c n := by
  have hs' : tm.RunsInSpace (List.ofFn x) (c * (Nat.log2 (List.ofFn x).length + 1)) := by
    simpa only [List.length_ofFn] using hs
  have h := reachable_lt_pow_of_runsInSpace c hs'
    (by simpa only [List.length_ofFn, graphRadix] using hv)
  simpa only [List.length_ofFn, vertexCount, graphRadix, vertexBound_eq_pow] using h

theorem source_val (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) (x : Bits n)
    (hs : tm.RunsInSpace (List.ofFn x) (c * (Nat.log2 n + 1))) :
    (source tm c n).val = startID tm (graphRadix State c n) :=
  Nat.mod_eq_of_lt (reachable_bound tm c n x hs .refl)

/-- Exact native acceptance, expressed in the finite reflexive Boolean graph. -/
theorem accepts_iff_reachable (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) (x : Bits n)
    (hs : tm.RunsInSpace (List.ofFn x) (c * (Nat.log2 n + 1))) :
    tm.Accepts (List.ofFn x) ↔ ∃ v : Fin (vertexCount k State c n),
      Relation.ReflTransGen (fun a b => graph tm c n x a b = true) (source tm c n) v ∧
        acceptsVertex c n v = true := by
  have hs' : tm.RunsInSpace (List.ofFn x) (c * (Nat.log2 (List.ofFn x).length + 1)) := by
    simpa only [List.length_ofFn] using hs
  have hnative := accepts_iff_reachable_bad_of_runsInSpace c hs'
  simp only [List.length_ofFn] at hnative
  rw [hnative]
  have hsource := source_val tm c n x hs
  have hbound := fun v => @reachable_bound k State _ tm c n x hs v
  have hstart := hbound _ Relation.ReflTransGen.refl
  have hrel : (fun a b : Fin (vertexCount k State c n) => graph tm c n x a b = true) =
      (fun a b => a = b ∨ Edge tm (graphRadix State c n) (List.ofFn x) a.val b.val) := by
    funext a b
    exact propext (graph_true_iff tm c n x a b)
  simp only [hrel, reachable_with_diagonal]
  constructor
  · rintro ⟨v, hv, hbad⟩
    refine ⟨⟨v, hbound v hv⟩, ?_, hbad⟩
    have hfin := (reachable_restrict_fin hbound hstart (hbound v hv)).mpr hv
    have hsource' : source tm c n = ⟨startID tm (graphRadix State c n), hstart⟩ :=
      Fin.ext hsource
    simpa only [hsource'] using hfin
  · rintro ⟨v, hv, hbad⟩
    refine ⟨v.val, ?_, hbad⟩
    have h := Relation.ReflTransGen.lift Fin.val (fun _ _ h => h) _ _ hv
    change Relation.ReflTransGen (Edge tm (graphRadix State c n) (List.ofFn x))
      (source tm c n).val v.val at h
    rw [hsource] at h
    exact h

/-- Once the squaring horizon covers the finite graph, its accepting entries
decide native machine acceptance. This is the semantic core of L/NL ⊆ NC². -/
theorem accepts_iff_squares (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) (x : Bits n)
    (hs : tm.RunsInSpace (List.ofFn x) (c * (Nat.log2 n + 1))) (rounds : ℕ)
    (hrounds : vertexCount k State c n ≤ 2 ^ rounds) :
    tm.Accepts (List.ofFn x) ↔ ∃ v : Fin (vertexCount k State c n),
      ParallelReachability.squares (graph tm c n x) rounds (source tm c n) v = true ∧
        acceptsVertex c n v = true := by
  rw [accepts_iff_reachable tm c n x hs]
  apply exists_congr
  intro v
  rw [ParallelReachability.reachable_iff_squares (graph_refl tm c n x) hrounds]

/-- The generated Cslib adjacency circuit is exactly the encoded finite graph
to which the reachability theorem applies. -/
theorem adjacencyCircuit_eval (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) (x : Bits n) :
    (Adjacency.reflexiveStandardCircuit tm (graphRadix State c n) n
      (vertexCount k State c n)).eval Cslib.Circuits.Boolean.interpretation x =
      ParallelReachability.encode (graph tm c n x) := by
  funext p
  rw [Adjacency.reflexiveStandardCircuit_eval]
  simp only [ParallelReachability.encode, graph, Fin.ext_iff]
  rfl

open Cslib Turing.MultiTapeTM ComputableInSpace

/-- The ambient vertex count is an explicit polynomial in input length. -/
theorem vertexCount_polynomial (c : ℕ) : PolynomiallyBounded (vertexCount k State c) := by
  change PolynomiallyBounded (fun n => vertexCount k State c n)
  simp only [vertexCount, graphRadix, vertexBound_eq_pow]
  fun_prop

/-- The start selector is generated by finite machines within the local budget. -/
theorem source_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (tm : Turing.MultiTapeNTM k Bool State) (c : ℕ) {n : α → ℕ}
    (hn : ComputableInSpace n enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => (source tm c (n a)).val) enc encNat S := by
  have hB := budget_natPow (budget_natAdd hn (budget_const 2 hin)) hin (radixExponent State c)
  exact budget_natMod (startID_budget tm hB hin) (vertexBound_budget (k := k) hB hin)

/-- Accepting-ID flags are likewise actual small-workspace computations. -/
theorem acceptsVertex_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (c : ℕ) {n v : α → ℕ}
    (hn : ComputableInSpace n enc encNat S)
    (hv : ComputableInSpace v enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace
      (fun a => bad (k := k) (State := State) (graphRadix State c (n a)) (n a) (v a))
      enc encBool S := by
  have hB := budget_natPow (budget_natAdd hn (budget_const 2 hin)) hin (radixExponent State c)
  exact bad_budget (k := k) (State := State) hB hn hv hin

end PredictionDepth.StandardComplexity.ConfigurationAcceptance
