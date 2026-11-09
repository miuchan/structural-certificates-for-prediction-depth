import PredictionDepth.Complexity.GraphUniform
import PredictionDepth.Complexity.UniformReachability

/-! Direct equality between the streamed configuration circuit and its typed semantics. -/

namespace PredictionDepth.StandardComplexity
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM
open Turing.MultiTapeNTM ConfigurationGraph ConfigurationAcceptance StandardPower

variable {k : ℕ} {State : Type} [Fintype State]

theorem configurationFamily_code (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) :
    (configurationFamily tm c n).code = graphRawCode tm c n := by
  have hd : (decider (source tm c n) (acceptsVertex (k := k) (State := State) c n)).code =
      graphDeciderCode tm c n :=
    decider_code_nat (source tm c n)
      (fun v => bad (k := k) (State := State) (graphRadix State c n) n v)
  rw [configurationFamily, ← compCode_code, hd, Adjacency.reflexiveStandardCircuit_code,
    graphRawCode_eq]
  unfold Adjacency.reflexiveRawCode
  have he : RegularCompositionCode.shiftGate n =
      (fun g : Op × List ℕ => (g.1, g.2.map (n + ·))) := by
    funext g
    rfl
  rw [← he]
  exact RegularCompositionCode.compCode_affine n
      (vertexCount k State c n * vertexCount k State c n) n
      ((List.range (vertexCount k State c n * vertexCount k State c n)).map
        (Adjacency.reflexiveGateCode tm (graphRadix State c n) n (vertexCount k State c n)))
      (by simp) (graphDeciderCode tm c n)

/-- A second, direct finite-machine implementation of the family generator:
one streamed gate table, with no stored intermediate matrix or circuit code. -/
theorem configurationFamily_direct_uniform (tm : Turing.MultiTapeNTM k Bool State) (c : ℕ) :
    LogspaceUniform (configurationFamily tm c) := by
  have hcode := (graphRawCode_logspace tm c).congr_fun (configurationFamily_code tm c)
  exact (ComputableInLogSpace.id.pair hcode).congr (fun _ => rfl)

end PredictionDepth.StandardComplexity
