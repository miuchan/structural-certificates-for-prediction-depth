import PredictionDepth.Complexity.CircuitWriter
import PredictionDepth.Complexity.CodeLogspace

/-!
# Consecutive output normalization

One binary AND copy per output gives an arbitrary circuit a consecutive final
output block. The transformation is semantic identity, adds one to depth, and
has an actual logspace code generator.
-/

namespace PredictionDepth.StandardComplexity.OutputNormalization
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInSpace

def copyBank (m : ℕ) : Circuit signature m m :=
  Circuit.pi (fun i => Circuit.oneGate .and (fun _ => i))

@[simp] theorem copyBank_eval (m : ℕ) (x : Fin m → Bool) :
    (copyBank m).eval interpretation x = x := by
  funext i
  simp [copyBank, Circuit.eval_pi, Circuit.eval_oneGate, interpretation]

@[simp] theorem copyBank_size (m : ℕ) : (copyBank m).size = m := by
  simp [copyBank]

theorem copyBank_depth_le (m : ℕ) : (copyBank m).depth ≤ 1 :=
  Circuit.depth_pi_le _ (fun _ => (Circuit.depth_oneGate _ _).le)

theorem copyBank_code (m : ℕ) :
    (copyBank m).code =
      ((List.range m).map (fun i => (.and, [i, i])), (List.range m).map (m + ·)) := by
  rw [copyBank, CircuitWriter.pi_inputGate_code
    _ (fun i : Fin m => (.and, [i.val, i.val]))]
  · simp only [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map,
      Function.comp_def]
  · intro i
    rfl
  · intro i j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hj
    rw [hj]
    exact i.isLt

def normalizeOutputs {n m : ℕ} (c : Circuit signature n m) : Circuit signature n m :=
  (copyBank m).comp c

@[simp] theorem normalizeOutputs_eval {n m : ℕ} (c : Circuit signature n m)
    (x : Fin n → Bool) : (normalizeOutputs c).eval interpretation x = c.eval interpretation x := by
  rw [normalizeOutputs, Circuit.eval_comp, copyBank_eval]

@[simp] theorem normalizeOutputs_size {n m : ℕ} (c : Circuit signature n m) :
    (normalizeOutputs c).size = c.size + m := by
  simp [normalizeOutputs]

theorem normalizeOutputs_depth_le {n m : ℕ} (c : Circuit signature n m) :
    (normalizeOutputs c).depth ≤ c.depth + 1 :=
  (Circuit.depth_comp_le _ _).trans (by have h := copyBank_depth_le m; omega)

theorem normalizeOutputs_code {n m : ℕ} (c : Circuit signature n m) :
    (normalizeOutputs c).code =
      (c.code.1 ++ c.code.2.map (fun i => (.and, [i, i])),
       (List.range m).map (fun i => n + c.size + i)) := by
  have hin (i : Fin m) : compCodeWire n c.code i.val = (c.outputs i).toNat := by
    simp [compCodeWire, Circuit.code, List.getD_eq_getElem?_getD]
  have hout (i : Fin m) : compCodeWire n c.code (m + i.val) = n + c.size + i.val := by
    have hm : c.code.2.length = m := by simp [Circuit.code]
    rw [compCodeWire, hm, ite_eq_right (show ¬ m + i.val < m by omega),
      Circuit.length_code_fst, Nat.add_sub_cancel_left]
  rw [normalizeOutputs, ← compCode_code]
  have hc : (copyBank m).code =
      (List.ofFn (fun i : Fin m => (.and, [i.val, i.val])),
       List.ofFn (fun i : Fin m => m + i.val)) := by
    simpa only [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map,
      Function.comp_def] using copyBank_code m
  rw [hc]
  simp only [compCode, List.map_ofFn, Function.comp_def, List.map_cons, List.map_nil, hin, hout]
  apply Prod.ext
  · apply congrArg (List.append _)
    simp only [Circuit.code, List.map_ofFn, Function.comp_def]
  · simp only [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map,
      Function.comp_def]

/-- The output block is consecutive and occurs after all original gates. -/
theorem normalizeOutputs_consecutive {n m : ℕ} (c : Circuit signature n m) :
    m ≤ (normalizeOutputs c).code.1.length ∧
      (normalizeOutputs c).code.2 =
        (List.range m).map (fun i => n + (normalizeOutputs c).code.1.length - m + i) := by
  rw [Circuit.length_code_fst, normalizeOutputs_size]
  constructor
  · omega
  · rw [normalizeOutputs_code]
    apply List.map_congr_left
    intro i _
    omega

theorem copyBank_code_logspace :
    ComputableInLogSpace (fun m => (copyBank m).code) encUnary encCode := by
  have hn := CircuitWriter.length_inSpace
  have hi := CircuitWriter.index_inSpace
  have hin := CircuitWriter.input_budget
  have hgate := budget_prod (budget_const (encB := encOp) Op.and hin)
    (budget_cons hi (budget_cons hi (budget_const (encB := encList encNat) [] hin)))
  have ho := budget_natAdd hn (budget_natSub hi (budget_natAdd hn (budget_const 1 hin)))
  have h := CircuitWriter.computableInLogSpace_code
    (G := id) (O := id) (gate := fun _ i => (.and, [i, i])) (output := fun m i => m + i)
    hn hn hgate ho (by fun_prop) (by fun_prop)
  exact h.congr_fun (fun m => by simpa only [CircuitWriter.code, id_eq] using copyBank_code m)

/-- The normalization is a standard logspace transformation on families of
typed circuits, charging the complete original and appended descriptions. -/
theorem normalizeOutputs_logspace {α : Type} {enc : α ↪ List Bool} {n m : α → ℕ}
    {c : ∀ a, Circuit signature (n a) (m a)}
    (hn : ComputableInLogSpace n enc encUnary) (hm : ComputableInLogSpace m enc encUnary)
    (hc : ComputableInLogSpace (fun a => (c a).code) enc encCode) :
    ComputableInLogSpace (fun a => (normalizeOutputs (c a)).code) enc encCode :=
  CodeLogspace.circuit_comp_logspace hn hc (copyBank_code_logspace.comp hm)

end PredictionDepth.StandardComplexity.OutputNormalization
