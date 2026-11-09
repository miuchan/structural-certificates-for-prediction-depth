import PredictionDepth.Complexity.PowerUniform

/-! A native logspace writer for adjacency followed by matrix powering. -/

namespace PredictionDepth.StandardComplexity
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInSpace
open Turing.MultiTapeNTM ConfigurationGraph ConfigurationAcceptance
open StandardPower

/-- Relocate one De Morgan gate using at most two argument lookups. -/
def shiftGate (offset : ℕ) (g : Op × List ℕ) : Op × List ℕ :=
  if g.1 = .const false ∨ g.1 = .const true then (g.1, [])
  else if g.1 = .not then (g.1, [offset + g.2.headD 0])
  else (g.1, [offset + g.2.headD 0, offset + g.2.tail.headD 0])

theorem shiftGate_eq_map (offset : ℕ) (g : Op × List ℕ)
    (hg : g.2.length = signature.Arity g.1) :
    shiftGate offset g = (g.1, g.2.map (offset + ·)) := by
  rcases g with ⟨op, args⟩
  cases op with
  | const b =>
      have : args = [] := List.length_eq_zero_iff.mp hg
      subst args
      cases b <;> simp [shiftGate]
  | not =>
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hg
      simp [shiftGate]
  | and =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hg
      simp [shiftGate]
  | or =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hg
      simp [shiftGate]

theorem shiftGate_budget {α : Type} {enc : α ↪ List Bool} {B : α → ℕ}
    {offset : α → ℕ} {gate : α → Op × List ℕ}
    (ho : ComputableInSpace offset enc encNat B)
    (hg : ComputableInSpace gate enc encGate B)
    (hin : (fun a => (enc a).length) ≼ B) :
    ComputableInSpace (fun a => shiftGate (offset a) (gate a)) enc encGate B := by
  have hop := fst' hg
  have hargs := snd' hg
  have h₀ := budget_natAdd ho (budget_headD 0 hargs)
  have h₁ := budget_natAdd ho (budget_headD 0 (budget_tail hargs))
  have hnil : ComputableInSpace (fun _ : α => ([] : List ℕ)) enc (encList encNat) B :=
    budget_const [] hin
  have hconst := budget_finite (encC := encBool)
    (fun op : Op => decide (op = .const false ∨ op = .const true)) hop
  have hnot := budget_finite (encC := encBool) (fun op : Op => decide (op = .not)) hop
  exact (budget_ite hconst (budget_prod hop hnil)
    (budget_ite hnot (budget_prod hop (budget_cons h₀ hnil))
      (budget_prod hop (budget_cons h₀ (budget_cons h₁ hnil))))).of_enc_eq
        (fun a => by simp only [shiftGate, decide_eq_true_eq])

theorem powerGate_arity (N q : ℕ) :
    (powerGate N q).2.length = signature.Arity (powerGate N q).1 := by
  unfold powerGate productGateCode mergeGateCode
  dsimp only
  split_ifs <;> rfl

theorem deciderGate_arity (N start : ℕ) (accept : ℕ → Bool) (q : ℕ) :
    (deciderGate N start accept q).2.length = signature.Arity (deciderGate N start accept q).1 := by
  unfold deciderGate
  dsimp only
  split_ifs
  · exact powerGate_arity N q
  · unfold acceptingGateCode
    dsimp only
    split_ifs <;> rfl
  · unfold mergeGateCode
    dsimp only
    split_ifs <;> rfl

variable {k : ℕ} {State : Type} [Fintype State]

noncomputable def graphGateCount (c n : ℕ) : ℕ :=
  let N := vertexCount k State c n
  N * N + (stageCount N) ^ 2 * layerWidth N

noncomputable def graphGate (tm : Turing.MultiTapeNTM k Bool State) (c n q : ℕ) : Op × List ℕ :=
  let N := vertexCount k State c n
  if q < N * N then Adjacency.reflexiveGateCode tm (graphRadix State c n) n N q
  else shiftGate n (deciderGate N (source tm c n).val
    (fun v => bad (k := k) (State := State) (graphRadix State c n) n v) (q - N * N))

noncomputable def graphOutput (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) : ℕ :=
  n + deciderOutput (vertexCount k State c n) (source tm c n).val

noncomputable def graphRawCode (tm : Turing.MultiTapeNTM k Bool State) (c : ℕ)
    (n : ℕ) : List (Op × List ℕ) × List ℕ :=
  CircuitWriter.code (graphGateCount (k := k) (State := State) c) (fun _ => 1)
    (graphGate tm c) (fun n _ => graphOutput tm c n) n

private theorem map_range_split {β : Type*} (m t : ℕ) (f g : ℕ → β) :
    (List.range (m + t)).map (fun q => if q < m then f q else g (q - m)) =
      (List.range m).map f ++ (List.range t).map g := by
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro q hq
    simp only [List.mem_range] at hq
    simp only [ite_eq_left hq]
  · apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply, ite_eq_right (show ¬ m + q < m by omega), Nat.add_sub_cancel_left]

set_option maxHeartbeats 800000 in
/-- The single streamed table is precisely adjacency followed by the shifted
decider table. All original matrix-input wires become adjacency-output wires. -/
theorem graphRawCode_eq (tm : Turing.MultiTapeNTM k Bool State) (c n : ℕ) :
    graphRawCode tm c n =
      ((Adjacency.reflexiveRawCode tm (graphRadix State c n) n (vertexCount k State c n)).1 ++
        (graphDeciderCode tm c n).1.map (fun g => (g.1, g.2.map (n + ·))),
       (graphDeciderCode tm c n).2.map (n + ·)) := by
  unfold graphRawCode CircuitWriter.code graphGateCount graphGate graphOutput graphDeciderCode
    deciderCode Adjacency.reflexiveRawCode
  dsimp only
  rw [map_range_split (vertexCount k State c n * vertexCount k State c n)
    ((stageCount (vertexCount k State c n)) ^ 2 * layerWidth (vertexCount k State c n))
    (Adjacency.reflexiveGateCode tm (graphRadix State c n) n (vertexCount k State c n))
    (fun q => shiftGate n (deciderGate (vertexCount k State c n) (source tm c n).val
      (fun v => bad (k := k) (State := State) (graphRadix State c n) n v) q))]
  apply Prod.ext
  · apply congrArg (List.append _)
    rw [List.map_map]
    apply List.map_congr_left
    intro q _
    exact shiftGate_eq_map n _ (deciderGate_arity _ _ _ _)
  · simp

set_option maxHeartbeats 800000 in
theorem graphRawCode_logspace (tm : Turing.MultiTapeNTM k Bool State) (c : ℕ) :
    ComputableInLogSpace (graphRawCode tm c) encUnary encCode := by
  have hn := CircuitWriter.length_inSpace
  have hin := CircuitWriter.input_budget
  have hB := budget_natPow (budget_natAdd hn (budget_const 2 hin)) hin (radixExponent State c)
  have hN := vertexBound_budget (k := k) hB hin
  change ComputableInSpace (fun p : CircuitWriter.Input => vertexCount k State c p.1.2.1)
    CircuitWriter.inputEncoding encNat CircuitWriter.budget at hN
  have hs := source_budget tm c hn hin
  have hm := budget_natMul hN hN
  have hq := budget_natSub CircuitWriter.index_inSpace hm
  have hleaf := budget_natMod
    (budget_natMod hq (layerWidth_budget hN hin)) (width_budget hN hin)
  have ha := acceptsVertex_budget (k := k) (State := State) c hn hleaf hin
  have hdec := deciderGate_budget hN hs hq ha hin
  have hgate := budget_ite (budget_natLt CircuitWriter.index_inSpace hm)
    (Adjacency.reflexiveGateCode_budget tm hB hn hN CircuitWriter.index_inSpace hin)
    (shiftGate_budget hn hdec hin)
  have hg : ComputableInSpace
      (fun p : CircuitWriter.Input => graphGate tm c p.1.2.1 p.1.2.2)
      CircuitWriter.inputEncoding encGate CircuitWriter.budget :=
    hgate.of_enc_eq (fun p => by simp only [graphGate, graphRadix, radix, decide_eq_true_eq])
  have hc := budget_natAdd hm (deciderGateCount_budget hN hin)
  have ho := budget_natAdd hn (deciderOutput_budget hN hs hin)
  have hpN := vertexCount_polynomial (k := k) (State := State) c
  have hpD := polynomiallyBounded_deciderGateCount hpN
  have hp : PolynomiallyBounded (graphGateCount (k := k) (State := State) c) := by
    exact (hpN.mul hpN).add hpD
  exact CircuitWriter.computableInLogSpace_code hc (budget_const 1 hin) hg ho hp (by fun_prop)

end PredictionDepth.StandardComplexity
