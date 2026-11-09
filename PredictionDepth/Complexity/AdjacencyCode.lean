import PredictionDepth.Complexity.Adjacency
import PredictionDepth.Complexity.CircuitWriter
import CslibFrontier.Computability.Circuit.Pi
import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
import CslibFrontier.Computability.Complexity.Problems.CircuitValue.Writer

/-!
# De Morgan code for compact configuration adjacency

Each matrix entry has exactly one gate. All references point to primary inputs;
no gate depends on another entry. This regular format permits direct streaming
generation from the binary source/target indices.
-/

namespace PredictionDepth.StandardComplexity.Adjacency
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeNTM ConfigurationGraph
open Turing.MultiTapeTM ComputableInSpace

/-- One bit's arbitrary truth table uses one De Morgan gate. -/
def unaryCircuit {n : ℕ} (q : Fin n) (lo hi : Bool) : Circuit signature n 1 :=
  if lo then
    if hi then Circuit.oneGate (.const true) Fin.elim0
    else Circuit.oneGate .not (fun _ => q)
  else
    if hi then Circuit.oneGate .and (fun _ => q)
    else Circuit.oneGate (.const false) Fin.elim0

theorem unaryCircuit_eval {n : ℕ} (q : Fin n) (lo hi : Bool) (x : Fin n → Bool) :
    (unaryCircuit q lo hi).eval interpretation x 0 = if x q then hi else lo := by
  cases lo <;> cases hi <;> cases h : x q <;>
    simp [unaryCircuit, Circuit.eval_oneGate, interpretation, h]

@[simp] theorem unaryCircuit_size {n : ℕ} (q : Fin n) (lo hi : Bool) :
    (unaryCircuit q lo hi).size = 1 := by
  cases lo <;> cases hi <;> simp [unaryCircuit]

@[simp] theorem unaryCircuit_depth {n : ℕ} (q : Fin n) (lo hi : Bool) :
    (unaryCircuit q lo hi).depth = 1 := by
  cases lo <;> cases hi <;> simp [unaryCircuit]

def unaryGateCode (q : ℕ) (lo hi : Bool) : Op × List ℕ :=
  if lo then (if hi then (.const true, []) else (.not, [q]))
  else (if hi then (.and, [q, q]) else (.const false, []))

theorem unaryCircuit_code {n : ℕ} (q : Fin n) (lo hi : Bool) :
    (unaryCircuit q lo hi).code = ([unaryGateCode q.val lo hi], [n]) := by
  cases lo <;> cases hi <;> rfl

variable {k : ℕ} {State : Type} [Fintype State]

/-- A single configuration edge, in the same De Morgan basis used by standard NC. -/
noncomputable def standardEntry (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : Circuit signature n 1 :=
  if h : queryIndex (k := k) B u < n then
    unaryCircuit ⟨queryIndex (k := k) B u, h⟩
      (edgeWithSymbol tm B n u v (some false))
      (edgeWithSymbol tm B n u v (some true))
  else Circuit.oneGate (.const (edgeWithSymbol tm B n u v none)) Fin.elim0

noncomputable def entryGateCode (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : Op × List ℕ :=
  if queryIndex (k := k) B u < n then
    unaryGateCode (queryIndex (k := k) B u)
      (edgeWithSymbol tm B n u v (some false))
      (edgeWithSymbol tm B n u v (some true))
  else (.const (edgeWithSymbol tm B n u v none), [])

theorem standardEntry_eval (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) (x : Fin n → Bool) :
    (standardEntry tm B n u v).eval interpretation x 0 =
      edgeWithSymbol tm B n u v (List.ofFn x)[queryIndex (k := k) B u]? := by
  by_cases h : queryIndex (k := k) B u < n
  · simp only [standardEntry, dite_eq_left h, unaryCircuit_eval]
    simp only [List.getElem?_ofFn, dite_eq_left h]
    cases x ⟨queryIndex (k := k) B u, h⟩ <;> rfl
  · simp [standardEntry, h, Circuit.eval_oneGate, interpretation]

@[simp] theorem standardEntry_size (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : (standardEntry tm B n u v).size = 1 := by
  unfold standardEntry
  split <;> simp

@[simp] theorem standardEntry_depth (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : (standardEntry tm B n u v).depth = 1 := by
  unfold standardEntry
  split <;> simp

theorem standardEntry_code (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) :
    (standardEntry tm B n u v).code = ([entryGateCode tm B n u v], [n]) := by
  by_cases h : queryIndex (k := k) B u < n
  · simp only [standardEntry, entryGateCode, dite_eq_left h, ite_eq_left h]
    exact unaryCircuit_code _ _ _
  · simp only [standardEntry, entryGateCode, dite_eq_right h, ite_eq_right h]
    rfl

theorem entryGateCode_inputs (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : ∀ j ∈ (entryGateCode tm B n u v).2, j < n := by
  unfold entryGateCode
  split_ifs with h
  · unfold unaryGateCode
    split <;> split <;> simp_all
  · simp

/-- Canonical parallel adjacency circuit: exactly `N²` gates, each of depth one. -/
noncomputable def standardCircuit (tm : Turing.MultiTapeNTM k Bool State)
    (B n N : ℕ) : Circuit signature n (N * N) :=
  Circuit.pi fun p => standardEntry tm B n (p.val / N) (p.val % N)

theorem standardCircuit_eval (tm : Turing.MultiTapeNTM k Bool State)
    (B n N : ℕ) (x : Fin n → Bool) (p : Fin (N * N)) :
    (standardCircuit tm B n N).eval interpretation x p =
      edgeWithSymbol tm B n (p.val / N) (p.val % N)
        (List.ofFn x)[queryIndex (k := k) B (p.val / N)]? := by
  simp only [standardCircuit, Circuit.eval_pi, standardEntry_eval]

@[simp] theorem standardCircuit_size (tm : Turing.MultiTapeNTM k Bool State)
    (B n N : ℕ) : (standardCircuit tm B n N).size = N * N := by
  simp [standardCircuit]

theorem standardCircuit_depth_le (tm : Turing.MultiTapeNTM k Bool State)
    (B n N : ℕ) : (standardCircuit tm B n N).depth ≤ 1 := by
  exact Circuit.depth_pi_le _ (fun _ => by simp)

theorem pi_inputGate_code {n m : ℕ} (cs : Fin m → Circuit signature n 1)
    (g : Fin m → Op × List ℕ)
    (hc : ∀ i, (cs i).code = ([g i], [n]))
    (hg : ∀ i j, j ∈ (g i).2 → j < n) :
    (Circuit.pi cs).code =
      (List.ofFn g, List.ofFn (fun i : Fin m => n + i.val)) :=
  CircuitWriter.pi_inputGate_code cs g hc hg

/-- Closed-form gate code, including out-of-range entry indices. -/
noncomputable def gateCode (tm : Turing.MultiTapeNTM k Bool State)
    (B n N p : ℕ) : Op × List ℕ := entryGateCode tm B n (p / N) (p % N)

/-- The raw circuit description lists independent entry gates and then their
consecutive output wires. No dependency-sensitive traversal is needed. -/
noncomputable def rawCode (tm : Turing.MultiTapeNTM k Bool State) (B n N : ℕ) :
    List (Op × List ℕ) × List ℕ :=
  ((List.range (N * N)).map (gateCode tm B n N),
    (List.range (N * N)).map (fun p => n + p))

theorem standardCircuit_code (tm : Turing.MultiTapeNTM k Bool State) (B n N : ℕ) :
    (standardCircuit tm B n N).code = rawCode tm B n N := by
  rw [standardCircuit,
    pi_inputGate_code _ _ (fun _ => standardEntry_code _ _ _ _ _)
      (fun _ => entryGateCode_inputs _ _ _ _ _)]
  simp only [rawCode, gateCode, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map, Function.comp_def]

section Generator
variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

theorem unaryGateCode_budget {q : α → ℕ} {lo hi : α → Bool}
    (hq : ComputableInSpace q enc encNat S)
    (hlo : ComputableInSpace lo enc encBool S)
    (hhi : ComputableInSpace hi enc encBool S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => unaryGateCode (q a) (lo a) (hi a)) enc encGate S := by
  have hnil := budget_const (encB := encList encNat) ([] : List ℕ) hin
  exact budget_ite hlo
    (budget_ite hhi (budget_const (encB := encGate) (Op.const true, []) hin)
      (budget_prod (budget_const (encB := encOp) Op.not hin) (budget_cons hq hnil)))
    (budget_ite hhi
      (budget_prod (budget_const (encB := encOp) Op.and hin) (budget_cons hq (budget_cons hq hnil)))
      (budget_const (encB := encGate) (Op.const false, []) hin))

/-- The concrete De Morgan gate code, including its binary wire references, is
computed within the same short-argument workspace budget. -/
theorem entryGateCode_budget (tm : Turing.MultiTapeNTM k Bool State)
    {B n u v : α → ℕ}
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hv : ComputableInSpace v enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => entryGateCode tm (B a) (n a) (u a) (v a))
      enc encGate S := by
  have hq := queryIndex_budget (k := k) hB hu
  have hnone := edgeWithSymbol_budget tm hB hn hu hv (budget_const none hin) hin
  have hfalse := edgeWithSymbol_budget tm hB hn hu hv (budget_const (some false) hin) hin
  have htrue := edgeWithSymbol_budget tm hB hn hu hv (budget_const (some true) hin) hin
  have hconst := budget_finite (encC := encGate) (fun b : Bool => (Op.const b, [])) hnone
  exact (budget_ite (budget_natLt hq hn) (unaryGateCode_budget hq hfalse htrue hin)
    hconst).of_enc_eq fun a => by simp only [entryGateCode, decide_eq_true_eq]

theorem gateCode_budget (tm : Turing.MultiTapeNTM k Bool State)
    {B n N p : α → ℕ}
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hN : ComputableInSpace N enc encNat S)
    (hp : ComputableInSpace p enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => gateCode tm (B a) (n a) (N a) (p a)) enc encGate S :=
  entryGateCode_budget tm hB hn (budget_natDiv hp hN) (budget_natMod hp hN) hin

end Generator

/-- Add identity edges, so every shorter walk can be padded to the squaring horizon. -/
noncomputable def reflexiveEntry (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : Circuit signature n 1 :=
  if u = v then Circuit.oneGate (.const true) Fin.elim0 else standardEntry tm B n u v

noncomputable def reflexiveEntryCode (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : Op × List ℕ :=
  if u = v then (.const true, []) else entryGateCode tm B n u v

theorem reflexiveEntry_eval (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) (x : Fin n → Bool) :
    (reflexiveEntry tm B n u v).eval interpretation x 0 =
      if u = v then true
      else edgeWithSymbol tm B n u v (List.ofFn x)[queryIndex (k := k) B u]? := by
  by_cases h : u = v
  · simp [reflexiveEntry, h, interpretation]
  · simp [reflexiveEntry, h, standardEntry_eval]

@[simp] theorem reflexiveEntry_size (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : (reflexiveEntry tm B n u v).size = 1 := by
  unfold reflexiveEntry
  split <;> simp

@[simp] theorem reflexiveEntry_depth (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : (reflexiveEntry tm B n u v).depth = 1 := by
  unfold reflexiveEntry
  split <;> simp

theorem reflexiveEntry_code (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) :
    (reflexiveEntry tm B n u v).code = ([reflexiveEntryCode tm B n u v], [n]) := by
  by_cases h : u = v
  · simp only [reflexiveEntry, reflexiveEntryCode, ite_eq_left h]
    rfl
  · simp only [reflexiveEntry, reflexiveEntryCode, ite_eq_right h]
    exact standardEntry_code _ _ _ _ _

theorem reflexiveEntryCode_inputs (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : ∀ j ∈ (reflexiveEntryCode tm B n u v).2, j < n := by
  by_cases h : u = v
  · simp [reflexiveEntryCode, h]
  · simpa [reflexiveEntryCode, h] using entryGateCode_inputs tm B n u v

noncomputable def reflexiveStandardCircuit (tm : Turing.MultiTapeNTM k Bool State)
    (B n N : ℕ) : Circuit signature n (N * N) :=
  Circuit.pi fun p => reflexiveEntry tm B n (p.val / N) (p.val % N)

theorem reflexiveStandardCircuit_eval (tm : Turing.MultiTapeNTM k Bool State)
    (B n N : ℕ) (x : Fin n → Bool) (p : Fin (N * N)) :
    (reflexiveStandardCircuit tm B n N).eval interpretation x p =
      if p.val / N = p.val % N then true
      else edgeWithSymbol tm B n (p.val / N) (p.val % N)
        (List.ofFn x)[queryIndex (k := k) B (p.val / N)]? := by
  simp only [reflexiveStandardCircuit, Circuit.eval_pi, reflexiveEntry_eval]

@[simp] theorem reflexiveStandardCircuit_size (tm : Turing.MultiTapeNTM k Bool State)
    (B n N : ℕ) : (reflexiveStandardCircuit tm B n N).size = N * N := by
  simp [reflexiveStandardCircuit]

theorem reflexiveStandardCircuit_depth_le (tm : Turing.MultiTapeNTM k Bool State)
    (B n N : ℕ) : (reflexiveStandardCircuit tm B n N).depth ≤ 1 :=
  Circuit.depth_pi_le _ (fun _ => by simp)

noncomputable def reflexiveGateCode (tm : Turing.MultiTapeNTM k Bool State)
    (B n N p : ℕ) : Op × List ℕ := reflexiveEntryCode tm B n (p / N) (p % N)

noncomputable def reflexiveRawCode (tm : Turing.MultiTapeNTM k Bool State)
    (B n N : ℕ) : List (Op × List ℕ) × List ℕ :=
  ((List.range (N * N)).map (reflexiveGateCode tm B n N),
    (List.range (N * N)).map (fun p => n + p))

theorem reflexiveStandardCircuit_code (tm : Turing.MultiTapeNTM k Bool State) (B n N : ℕ) :
    (reflexiveStandardCircuit tm B n N).code = reflexiveRawCode tm B n N := by
  rw [reflexiveStandardCircuit,
    pi_inputGate_code _ _ (fun _ => reflexiveEntry_code _ _ _ _ _)
      (fun _ => reflexiveEntryCode_inputs _ _ _ _ _)]
  simp only [reflexiveRawCode, reflexiveGateCode, List.ofFn_eq_map,
    ← List.map_coe_finRange_eq_range, List.map_map, Function.comp_def]

theorem reflexiveGateCode_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (tm : Turing.MultiTapeNTM k Bool State) {B n N p : α → ℕ}
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hN : ComputableInSpace N enc encNat S)
    (hp : ComputableInSpace p enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => reflexiveGateCode tm (B a) (n a) (N a) (p a))
      enc encGate S := by
  exact (budget_ite (budget_natEq (budget_natDiv hp hN) (budget_natMod hp hN))
    (budget_const (.const true, []) hin) (gateCode_budget tm hB hn hN hp hin)).of_enc_eq
      fun a => by simp only [reflexiveGateCode, reflexiveEntryCode, gateCode, decide_eq_true_eq]

/-- The entire regular adjacency code is generated in logarithmic space from
unary input length. The two gate values are computed by finite machines, not
stored in an unbounded nonuniform advice table. -/
theorem reflexiveStandardCircuit_uniform (tm : Turing.MultiTapeNTM k Bool State) (D : ℕ) :
    ComputableInLogSpace
      (fun n => (reflexiveStandardCircuit tm (radix D n) n
        (vertexBound (k := k) (radix D n))).code)
      encUnary encCode := by
  let N : ℕ → ℕ := fun n => vertexBound (k := k) (radix D n)
  let G : ℕ → ℕ := fun n => N n * N n
  have hn := CircuitWriter.length_inSpace
  have hin := CircuitWriter.input_budget
  have hB := budget_natPow (budget_natAdd hn (budget_const 2 hin)) hin D
  have hN : ComputableInSpace (fun p : CircuitWriter.Input => N p.1.2.1)
      CircuitWriter.inputEncoding encNat CircuitWriter.budget :=
    vertexBound_budget (k := k) hB hin
  have hG : ComputableInSpace (fun p : CircuitWriter.Input => G p.1.2.1)
      CircuitWriter.inputEncoding encNat CircuitWriter.budget := budget_natMul hN hN
  have hgate := reflexiveGateCode_budget tm hB hn hN CircuitWriter.index_inSpace hin
  have hout := budget_natAdd hn
    (budget_natSub CircuitWriter.index_inSpace (budget_natAdd hG (budget_const 1 hin)))
  have hp : PolynomiallyBounded G := by
    dsimp only [G, N, vertexBound, radix]
    fun_prop
  have h := CircuitWriter.computableInLogSpace_code (G := G) (O := G)
    (gate := fun n => reflexiveGateCode tm (radix D n) n (N n))
    (output := fun n p => n + p) hG hG hgate hout hp hp
  exact h.congr fun n => by
    rw [reflexiveStandardCircuit_code]
    rfl

end PredictionDepth.StandardComplexity.Adjacency
