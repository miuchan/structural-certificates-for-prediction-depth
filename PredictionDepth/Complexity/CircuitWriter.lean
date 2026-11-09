import CslibFrontier.Computability.Complexity.Problems.CircuitValue.Writer
import CslibFrontier.Computability.Circuit.Boolean.Encoding
import CslibFrontier.Computability.Circuit.Boolean.CodeComposition

/-!
# Logspace serialization of regular circuit codes

A circuit family whose gate count, individual gate and output-wire indices are
computable in linear workspace in their short binary arguments can be written
in logarithmic space on unary length. The writer emits one small chunk at a
time and never stores the complete circuit.
-/

namespace PredictionDepth.StandardComplexity.CircuitWriter
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity.CircuitValue
open Turing.MultiTapeTM ComputableInSpace

/-- The code of independent one-gate outputs, all of whose references are primary inputs. -/
theorem pi_inputGate_code {n m : ℕ} (cs : Fin m → Circuit signature n 1)
    (g : Fin m → Op × List ℕ)
    (hc : ∀ i, (cs i).code = ([g i], [n]))
    (hg : ∀ i j, j ∈ (g i).2 → j < n) :
    (Circuit.pi cs).code =
      (List.ofFn g, List.ofFn (fun i : Fin m => n + i.val)) := by
  induction m with
  | zero => simp [Circuit.pi, Circuit.code, Circuit.wiring]
  | succ m ih =>
      rw [Circuit.pi, ← appendCode_code,
        ih (fun i => cs i.castSucc) (fun i => g i.castSucc)
          (fun i => hc i.castSucc) (fun i => hg i.castSucc), hc (Fin.last m)]
      have hmap : (g (Fin.last m)).2.map (shiftCodeWire n m) = (g (Fin.last m)).2 := by
        calc
          _ = (g (Fin.last m)).2.map id := by
            apply List.map_congr_left
            intro j hj
            simp only [shiftCodeWire, ite_eq_left (hg (Fin.last m) j hj), id_eq]
          _ = _ := List.map_id _
      rw [List.ofFn_succ_last (f := g),
        List.ofFn_succ_last (f := fun i : Fin (m + 1) => n + i.val)]
      simp only [appendCode, List.length_ofFn, List.map_singleton, hmap,
        shiftCodeWire, Nat.lt_irrefl, ↓reduceIte, Fin.val_castSucc, Fin.val_last]


abbrev Input := (ℕ × ℕ × ℕ) × Bool
abbrev inputEncoding := WriterSpec.encStepIn
def budget (p : Input) : ℕ := wBudget p.1

theorem input_budget : (fun p : Input => (inputEncoding p).length) ≼ budget := by
  refine .of_le_linear 2 0 ?_
  intro p
  simp only [inputEncoding, WriterSpec.encStepIn, length_encPair, encBool_apply,
    List.length_singleton, budget, wBudget]
  omega

theorem length_inSpace :
    ComputableInSpace (fun p : Input => p.1.2.1) inputEncoding encNat budget :=
  fst' (snd' ((ComputableInSpace.fst encNat3 encBool).weaken input_budget))

theorem index_inSpace :
    ComputableInSpace (fun p : Input => p.1.2.2) inputEncoding encNat budget :=
  snd' (snd' ((ComputableInSpace.fst encNat3 encBool).weaken input_budget))

def code (G O : ℕ → ℕ) (gate : ℕ → ℕ → Op × List ℕ) (output : ℕ → ℕ → ℕ)
    (n : ℕ) : List (Op × List ℕ) × List ℕ :=
  ((List.range (G n)).map (gate n), (List.range (O n)).map (output n))

def chunk (G : ℕ → ℕ) (gate : ℕ → ℕ → Op × List ℕ) (output : ℕ → ℕ → ℕ)
    (n i : ℕ) : List Bool :=
  if i < G n then doubled (frame (encGate (gate n i)))
  else if i = G n then [false]
  else frame (encNat (output n (i - (G n + 1))))

def spec (G O : ℕ → ℕ) (gate : ℕ → ℕ → Op × List ℕ) (output : ℕ → ℕ → ℕ) :
    WriterSpec where
  countUnit := []
  countEnd := []
  numChunks n := G n + 1 + O n
  chunk := chunk G gate output
  trailer _ := []
  copyBit _ := []

theorem chunks_eq (G O : ℕ → ℕ) (gate : ℕ → ℕ → Op × List ℕ)
    (output : ℕ → ℕ → ℕ) (n : ℕ) :
    (List.range (G n + 1 + O n)).flatMap (chunk G gate output n) =
      (List.range (G n)).flatMap (fun i => doubled (frame (encGate (gate n i)))) ++
        [false] ++ (List.range (O n)).flatMap (fun i => frame (encNat (output n i))) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map, List.range_succ,
    List.flatMap_append]
  have hleft : (List.range (G n)).flatMap (chunk G gate output n) =
      (List.range (G n)).flatMap (fun i => doubled (frame (encGate (gate n i)))) := by
    apply List.flatMap_congr
    intro i hi
    simp only [List.mem_range] at hi
    simp [chunk, hi]
  have hright : (List.range (O n)).flatMap
      (fun i => chunk G gate output n (G n + 1 + i)) =
      (List.range (O n)).flatMap (fun i => frame (encNat (output n i))) := by
    apply List.flatMap_congr
    intro i _
    simp [chunk, show ¬ G n + 1 + i < G n by omega,
      show G n + 1 + i ≠ G n by omega]
  rw [hleft]
  simp only [List.flatMap_singleton]
  rw [show chunk G gate output n (G n) = [false] by simp [chunk]]
  simpa only [Function.comp_def] using congrArg
    (fun tail => (List.range (G n)).flatMap
      (fun i => doubled (frame (encGate (gate n i)))) ++ [false] ++ tail) hright

theorem spec_output (G O : ℕ → ℕ) (gate : ℕ → ℕ → Op × List ℕ)
    (output : ℕ → ℕ → ℕ) (w : List Bool) :
    encCode (code G O gate output w.length) = (spec G O gate output).output w := by
  have hmap (L : List ℕ) :
      doubled (L.flatMap (fun i => frame (encGate (gate w.length i)))) =
        L.flatMap (fun i => doubled (frame (encGate (gate w.length i)))) := by
    induction L with
    | nil => rfl
    | cons i L ih => simp only [List.flatMap_cons, doubled_append, ih]
  have hl {α : Type} (enc : α ↪ List Bool) (L : List ℕ) (f : ℕ → α) :
      encList enc (L.map f) = L.flatMap (fun i => frame (enc (f i))) := by
    change (L.map f).flatMap (frame ∘ enc) = _
    rw [List.flatMap_map]
    rfl
  change frame (encList encGate ((List.range (G w.length)).map (gate w.length))) ++
    encList encNat ((List.range (O w.length)).map (output w.length)) = _
  rw [hl, hl, frame_eq_doubled, hmap, ← chunks_eq]
  simp [spec, WriterSpec.output, ← List.flatMap_def]

variable {G O : ℕ → ℕ} {gate : ℕ → ℕ → Op × List ℕ} {output : ℕ → ℕ → ℕ}

/-- Kernel-checked streaming construction from local numerical routines.
`houtput` concerns the residual output index used after all gates are emitted. -/
theorem computableInLogSpace_code
    (hG : ComputableInSpace (fun p : Input => G p.1.2.1) inputEncoding encNat budget)
    (hO : ComputableInSpace (fun p : Input => O p.1.2.1) inputEncoding encNat budget)
    (hgate : ComputableInSpace (fun p : Input => gate p.1.2.1 p.1.2.2)
      inputEncoding encGate budget)
    (houtput : ComputableInSpace
      (fun p : Input => output p.1.2.1 (p.1.2.2 - (G p.1.2.1 + 1)))
      inputEncoding encNat budget)
    (hpolyG : PolynomiallyBounded G) (hpolyO : PolynomiallyBounded O) :
    ComputableInLogSpace (code G O gate output) encUnary encCode := by
  have hchunks : ComputableInSpace
      (fun p : Input => chunk G gate output p.1.2.1 p.1.2.2)
      inputEncoding encBits budget := by
    have hg := budget_comp_linear doubled_inSpace
      (budget_comp_linear (ComputableInSpace.frame encGate) hgate)
    have ho := budget_comp_linear (ComputableInSpace.frame encNat) houtput
    exact (budget_ite (budget_natLt index_inSpace hG) hg
      (budget_ite (budget_natEq index_inSpace hG) (budget_const [false] input_budget)
        ho)).of_enc_eq fun p => by simp only [chunk, decide_eq_true_eq]
  have hcount := budget_natAdd (budget_natAdd hG (budget_const 1 input_budget)) hO
  have hpoly : PolynomiallyBounded (fun n => G n + 1 + O n) := by fun_prop
  have hwriter := (spec G O gate output).computableInLogSpace (spec_output G O gate output)
    hcount hchunks (budget_const [] input_budget) hpoly
  have h := hwriter.comp (computableInLogSpace_frame encUnary)
  exact h.congr fun n => by simp only [Function.comp_apply, encUnary_apply, List.length_replicate]

end PredictionDepth.StandardComplexity.CircuitWriter
