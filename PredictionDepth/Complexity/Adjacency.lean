import PredictionDepth.Linear
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Routines
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Correctness

/-!
# Constant-depth configuration-graph adjacency circuits

At fixed source and target configuration IDs, the transition relation reads at
most one bit of the original input. All other fields belong to the fixed IDs
and the machine's finite transition table. Therefore one binary gate (with one
unused port) suffices for an adjacency entry, and all entries run in parallel.

The semantic graph and arithmetic metadata are those of cslib-frontier's
guarded compact configuration graph. This module does not replace actual
logspace generation by arbitrary hardwired truth tables: generation of the
query indices and two one-bit gate values is handled separately below.
-/

namespace PredictionDepth.StandardComplexity.Adjacency
open FastComposition
open Turing.MultiTapeNTM
open ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State]

/-- One adjacency entry. The queried input coordinate is fixed by the source ID. -/
noncomputable def entryCircuit (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : BinaryCircuit n 1 :=
  if h : queryIndex (k := k) B u < n then
    .seq (BinaryCircuit.select (fun _ : Fin 2 => ⟨queryIndex (k := k) B u, h⟩))
      (.gate (fun bit _ => edgeWithSymbol tm B n u v (some bit)))
  else BinaryCircuit.constant (fun _ => edgeWithSymbol tm B n u v none)

theorem entryCircuit_eval (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) (x : Bits n) :
    (entryCircuit tm B n u v).eval x 0 =
      edgeWithSymbol tm B n u v (List.ofFn x)[queryIndex (k := k) B u]? := by
  by_cases h : queryIndex (k := k) B u < n
  · simp [entryCircuit, h, BinaryCircuit.eval, BinaryCircuit.select]
  · simp [entryCircuit, h, BinaryCircuit.constant, BinaryCircuit.eval]

theorem entryCircuit_depth_le (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : (entryCircuit tm B n u v).depth ≤ 1 := by
  unfold entryCircuit
  split <;> simp [BinaryCircuit.depth, BinaryCircuit.select, BinaryCircuit.constant]

theorem entryCircuit_gateCount_le (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : (entryCircuit tm B n u v).gateCount ≤ 1 := by
  unfold entryCircuit
  split <;> simp [BinaryCircuit.gateCount, BinaryCircuit.select, BinaryCircuit.constant]

theorem entryCircuit_descriptionSize_le (tm : Turing.MultiTapeNTM k Bool State)
    (B n u v : ℕ) : (entryCircuit tm B n u v).descriptionSize ≤ 5 := by
  unfold entryCircuit
  split <;> simp [BinaryCircuit.descriptionSize, BinaryCircuit.select, BinaryCircuit.constant]

/-- The entire adjacency matrix is emitted in row-major order. -/
noncomputable def circuit (tm : Turing.MultiTapeNTM k Bool State) (B n N : ℕ) :
    BinaryCircuit n (N * N) :=
  Linear.Circuits.collect fun p => entryCircuit tm B n
    (finProdFinEquiv.symm p).1.val (finProdFinEquiv.symm p).2.val

theorem circuit_eval (tm : Turing.MultiTapeNTM k Bool State) (B n N : ℕ)
    (x : Bits n) (u v : Fin N) :
    (circuit tm B n N).eval x (finProdFinEquiv (u, v)) =
      edgeWithSymbol tm B n u v (List.ofFn x)[queryIndex (k := k) B u]? := by
  rw [circuit, Linear.Circuits.collect_eval, entryCircuit_eval]
  simp only [Equiv.symm_apply_apply]

theorem circuit_edge_iff (tm : Turing.MultiTapeNTM k Bool State) (B n N : ℕ)
    (x : Bits n) (u v : Fin N) :
    (circuit tm B n N).eval x (finProdFinEquiv (u, v)) = true ↔
      Edge tm B (List.ofFn x) u v := by
  rw [circuit_eval]
  simp only [Edge, List.length_ofFn]

theorem circuit_depth_le (tm : Turing.MultiTapeNTM k Bool State) (B n N : ℕ) :
    (circuit tm B n N).depth ≤ 1 :=
  Linear.Circuits.collect_depth_le _ (fun _ => entryCircuit_depth_le _ _ _ _ _)

theorem circuit_gateCount_le (tm : Turing.MultiTapeNTM k Bool State) (B n N : ℕ) :
    (circuit tm B n N).gateCount ≤ N * N := by
  simpa [circuit] using Linear.Circuits.collect_gateCount_le
    (fun p : Fin (N * N) => entryCircuit tm B n
      (finProdFinEquiv.symm p).1.val (finProdFinEquiv.symm p).2.val)
    (fun _ => entryCircuit_gateCount_le _ _ _ _ _)

/-- The complete local generator data: one queried coordinate, followed by the
truth-table values for absent, false, and true input symbols. -/
noncomputable def entryData (tm : Turing.MultiTapeNTM k Bool State) (B n u v : ℕ) :
    ℕ × (Bool × (Bool × Bool)) :=
  (queryIndex (k := k) B u,
    edgeWithSymbol tm B n u v none,
    edgeWithSymbol tm B n u v (some false),
    edgeWithSymbol tm B n u v (some true))

open Turing.MultiTapeTM ComputableInSpace

def entryDataEncoding : (ℕ × (Bool × (Bool × Bool))) ↪ List Bool :=
  encPair encNat (encPair encBool (encPair encBool encBool))

/-- The local gate metadata is computed by actual finite-control machines in
space linear in the short binary arguments, using the upstream arithmetic
routines. The original input bits are never included in these arguments. -/
theorem entryData_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (tm : Turing.MultiTapeNTM k Bool State) {B n u v : α → ℕ}
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hv : ComputableInSpace v enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => entryData tm (B a) (n a) (u a) (v a))
      enc entryDataEncoding S := by
  exact budget_prod (queryIndex_budget (k := k) hB hu)
    (budget_prod (edgeWithSymbol_budget tm hB hn hu hv (budget_const none hin) hin)
      (budget_prod (edgeWithSymbol_budget tm hB hn hu hv (budget_const (some false) hin) hin)
        (edgeWithSymbol_budget tm hB hn hu hv (budget_const (some true) hin) hin)))

/-- At the polynomial radix used for a fixed logspace machine, the gate's full
metadata is a linear-space function of binary `(input length, source, target)`.
During row-major enumeration of polynomially many vertices these arguments use
only logarithmically many bits of workspace. -/
theorem entryData_radix_inSpace (tm : Turing.MultiTapeNTM k Bool State) (D : ℕ) :
    ComputableInSpace
      (fun p : ℕ × ℕ × ℕ => entryData tm (radix D p.1) p.1 p.2.1 p.2.2)
      encNat3 entryDataEncoding (fun p => (encNat3 p).length) := by
  have hin : (fun p : ℕ × ℕ × ℕ => (encNat3 p).length) ≼
      (fun p => (encNat3 p).length) := .refl _
  have hn := ComputableInSpace.fst encNat (encPair encNat encNat)
  have hp := ComputableInSpace.snd encNat (encPair encNat encNat)
  have hu := fst' hp
  have hv := snd' hp
  exact entryData_budget tm
    (budget_natPow (budget_natAdd hn (budget_const 2 hin)) hin D) hn hu hv hin

end PredictionDepth.StandardComplexity.Adjacency
