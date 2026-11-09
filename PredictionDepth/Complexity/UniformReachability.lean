import PredictionDepth.Complexity.PowerUniform
import PredictionDepth.Complexity.UniformNC
import PredictionDepth.Complexity.StandardDeciderSerialization
import PredictionDepth.Complexity.CodeLogspace
import PredictionDepth.LogBounds
import CslibFrontier.Computability.Complexity.Classes.LogSpace

/-!
# Configuration reachability by uniform shallow circuits

The circuit construction uses the actual finite native-machine configuration
graph, a constant-depth adjacency stage, and Boolean relation powering.
-/

namespace PredictionDepth.StandardComplexity
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM
open Turing.MultiTapeNTM ConfigurationGraph ConfigurationAcceptance StandardPower

variable {k : ℕ} {State : Type} [Fintype State]

noncomputable def configurationFamily (tm : Turing.MultiTapeNTM k Bool State) (c : ℕ) :
    BooleanCircuitFamily := fun n =>
  (decider (source tm c n) (acceptsVertex (k := k) (State := State) c n)).comp
    (Adjacency.reflexiveStandardCircuit tm (graphRadix State c n) n (vertexCount k State c n))

theorem configurationFamily_correct (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ)
    (x : Fin n → Bool)
    (hs : tm.RunsInSpace (List.ofFn x) (c * (Nat.log2 n + 1))) :
    (configurationFamily tm c n).eval interpretation x 0 = true ↔ tm.Accepts (List.ofFn x) := by
  simp only [configurationFamily, Circuit.eval_comp, adjacencyCircuit_eval,
    decider_eval_true_iff]
  rw [accepts_iff_squares tm c n x hs (vertexCount k State c n).size
    (Nat.lt_size_self _).le]
  simp only [and_comm]

theorem configurationFamily_size (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) :
    (configurationFamily tm c n).size =
      (vertexCount k State c n).size.succ ^ 2 * layerWidth (vertexCount k State c n) +
        vertexCount k State c n * vertexCount k State c n := by
  simp only [configurationFamily, Circuit.size_comp, decider_size,
    Adjacency.reflexiveStandardCircuit_size, Nat.succ_eq_add_one, Nat.add_comm]

theorem configurationFamily_depth_le (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) :
    (configurationFamily tm c n).depth ≤ ((vertexCount k State c n).size + 1) ^ 2 + 1 :=
  (Circuit.depth_comp_le _ _).trans (Nat.add_le_add (decider_depth_le _ _)
    (Adjacency.reflexiveStandardCircuit_depth_le _ _ _ _))

theorem configurationFamily_polynomialSize (tm : Turing.MultiTapeNTM k Bool State) (c : ℕ) :
    PolynomiallyBounded (fun n => (configurationFamily tm c n).size) := by
  have hN := vertexCount_polynomial (k := k) (State := State) c
  have hD := polynomiallyBounded_deciderGateCount hN
  apply (hD.add (hN.mul hN)).mono_of_le
  intro n
  exact (configurationFamily_size tm c n).le

/-- One fixed quadratic polynomial in log input length bounds all depths. -/
theorem configurationFamily_polylogDepth (tm : Turing.MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C : ℕ, ∀ n, (configurationFamily tm c n).depth ≤ C * (Nat.log 2 n + 1) ^ 2 := by
  obtain ⟨A, d, hN⟩ := Cslib.polynomiallyBounded_iff_le.mp
    (vertexCount_polynomial (k := k) (State := State) c)
  let K := Nat.clog 2 (A + 1) + d + 1
  refine ⟨K ^ 2 + 1, ?_⟩
  intro n
  have hs : (vertexCount k State c n).size ≤
      (Nat.clog 2 (A + 1) + d) * (Nat.log 2 n + 1) := by
    rw [RegularReduction.size_eq_clog_succ]
    exact bitLength_of_polynomial_bound (hN n)
  have hbase : 1 ≤ Nat.log 2 n + 1 := by omega
  have hs' : (vertexCount k State c n).size + 1 ≤ K * (Nat.log 2 n + 1) := by
    dsimp only [K]
    rw [Nat.add_mul]
    omega
  have hsq := Nat.pow_le_pow_left hs' 2
  rw [mul_pow] at hsq
  have hunit : 1 ≤ (Nat.log 2 n + 1) ^ 2 := Nat.one_le_pow _ _ hbase
  calc
    (configurationFamily tm c n).depth ≤ ((vertexCount k State c n).size + 1) ^ 2 + 1 :=
      configurationFamily_depth_le tm c n
    _ ≤ K ^ 2 * (Nat.log 2 n + 1) ^ 2 + (Nat.log 2 n + 1) ^ 2 := Nat.add_le_add hsq hunit
    _ = (K ^ 2 + 1) * (Nat.log 2 n + 1) ^ 2 := by ring

/-- The same shallow family has an actual logarithmic-space native generator.
The code equalities connect the streaming writers to the typed circuits. -/
theorem configurationFamily_uniform (tm : Turing.MultiTapeNTM k Bool State) (c : ℕ) :
    LogspaceUniform (configurationFamily tm c) := by
  have hdec : ComputableInLogSpace
      (fun n => (decider (source tm c n) (acceptsVertex (k := k) (State := State) c n)).code)
      encUnary encCode :=
    (graphDeciderCode_logspace tm c).congr_fun (fun n => decider_code_nat (source tm c n)
      (fun v => bad (k := k) (State := State) (graphRadix State c n) n v))
  have hadj := Adjacency.reflexiveStandardCircuit_uniform tm (radixExponent State c)
  have hcomp := CodeLogspace.circuit_comp_logspace ComputableInLogSpace.id hadj hdec
  change ComputableInLogSpace
    (fun n => (⟨n, configurationFamily tm c n⟩ : Σ n, Circuit signature n 1)) encUnary (encCircuit 1)
  exact (ComputableInLogSpace.pair ComputableInLogSpace.id hcomp).congr (fun _ => rfl)

/-- Every native logspace Boolean computation has one genuinely uniform NC²
family. For typed encodings correctness is asserted on valid encoded inputs;
the generated circuit still exists at every length. -/
theorem logspace_bool_circuits {α : Type} {enc : α ↪ List Bool} {f : α → Bool}
    (hf : ComputableInLogSpace f enc encBool) :
    ∃ (F : BooleanCircuitFamily) (C : ℕ), LogspaceUniform F ∧
      PolynomiallyBounded (fun n => (F n).size) ∧
      (∀ n, (F n).depth ≤ C * (Nat.log 2 n + 1) ^ 2) ∧
      ∀ a, evaluateFamily F (enc a) = f a := by
  obtain ⟨t, c, hf⟩ := hf
  obtain ⟨k, State, hfinite, tm, hd⟩ :=
    hf.exists_decidesInSpace (A := {a | f a = true}) (fun _ => Iff.rfl)
  let : Finite State := hfinite
  let : Fintype State := Fintype.ofFinite State
  obtain ⟨C, hC⟩ := configurationFamily_polylogDepth tm c
  refine ⟨configurationFamily tm c, C, configurationFamily_uniform tm c,
    configurationFamily_polynomialSize tm c, hC, ?_⟩
  intro a
  apply Bool.eq_iff_iff.mpr
  have hw : List.ofFn (BitString.ofList (enc a).length (enc a)) = enc a :=
    BitString.ofFn_ofList rfl
  have hs := (hd.1 a).1
  have hc := configurationFamily_correct tm c (enc a).length
    (BitString.ofList (enc a).length (enc a)) (by simpa only [hw] using hs)
  change (configurationFamily tm c (enc a).length).eval interpretation
    (BitString.ofList (enc a).length (enc a)) 0 = true ↔ f a = true
  rw [hc, hw]
  exact (hd.1 a).2.symm

/-- A standard stronger inclusion, proved through the concrete configuration
graph rather than supplied as a complexity-class premise. -/
theorem NL_subset_uniformNC_two : Cslib.Complexity.NL encBits ⊆ UniformNCLevel 2 := by
  rintro A ⟨k, State, hfinite, tm, c, hd⟩
  let : Finite State := hfinite
  let : Fintype State := Fintype.ofFinite State
  obtain ⟨C, hC⟩ := configurationFamily_polylogDepth tm c
  refine ⟨configurationFamily tm c, C, ?_, configurationFamily_polynomialSize tm c,
    hC, configurationFamily_uniform tm c⟩
  intro x
  have hw : List.ofFn (BitString.ofList x.length x) = x := BitString.ofFn_ofList rfl
  have hc := configurationFamily_correct tm c x.length (BitString.ofList x.length x)
    (by simpa only [hw, encBits_apply] using (hd.1 x).1)
  change x ∈ A ↔ (configurationFamily tm c x.length).eval interpretation
    (BitString.ofList x.length x) 0 = true
  rw [hc, hw]
  simpa only [encBits_apply] using (hd.1 x).2

theorem L_subset_uniformNC_two : Cslib.Complexity.L encBits ⊆ UniformNCLevel 2 :=
  Cslib.Complexity.L_subset_NL.trans NL_subset_uniformNC_two

end PredictionDepth.StandardComplexity
