import PredictionDepth.Complexity.LogspaceBatch.Machine

/-! All batch-controller transitions have native linear-space implementations. -/

namespace PredictionDepth.StandardComplexity.LogspaceBatch

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal
open Turing.VirtualWord ComputableInSpace

section Routines
variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

theorem count_budget {n : α → ℕ} (hn : ComputableInSpace n enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) (C d : ℕ) :
    ComputableInSpace (fun a => count C d (n a)) enc encNat S :=
  budget_natMul (budget_const C hin) (budget_natPow (budget_natSucc hn) hin d)

theorem symbol_budget {n j q : α → ℕ} {b : α → Option Bool}
    (hn : ComputableInSpace n enc encNat S)
    (hj : ComputableInSpace j enc encNat S)
    (hq : ComputableInSpace q enc encNat S)
    (hb : ComputableInSpace b enc (encOption encBool) S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => symbol (n a) (j a) (q a) (b a)) enc (encOption encBool) S := by
  have htwo := budget_const (encB := encNat) 2 hin
  have htwon := budget_natMul htwo hn
  exact (budget_ite (budget_natLt hq htwon)
    (budget_ite (budget_natEq (budget_natMod hq htwo) (budget_const 0 hin))
      (budget_const (some true) hin) hb)
    (budget_ite (budget_natEq hq htwon) (budget_const (some false) hin)
      (budget_ite (budget_natLt hq (budget_natAdd (budget_natSucc htwon) hj))
        (budget_const (some true) hin) (budget_const none hin)))).of_enc_eq fun a => by
    simp only [symbol, decide_eq_true_eq]

end Routines

theorem components (D : Desc) (C d : ℕ) :
    ComputableInSpace (machine D C d).query encState encNat (fun s => (encState s).length) ∧
    ComputableInSpace (machine D C d).next (QueryMachine.encStateRead encState) encState
      (fun p => (QueryMachine.encStateRead encState p).length) ∧
    ComputableInSpace (machine D C d).emit (QueryMachine.encStateRead encState) encBits
      (fun p => (QueryMachine.encStateRead encState p).length) ∧
    ComputableInSpace (machine D C d).halted encState encBool (fun s => (encState s).length) ∧
    ComputableInSpace (machine D C d).finish encState encBits (fun s => (encState s).length) := by
  obtain ⟨hqM, hnM, heM, hhM, _⟩ := Native.components_inSpace D
  let encRest := encPair encNat (encPair encNat eCfg)
  have phase := ComputableInSpace.fst encBool encRest
  have rest := ComputableInSpace.snd encBool encRest
  have number := rest.fst'
  have index := rest.snd'.fst'
  have cfg := rest.snd'.snd'
  have qpos := budget_comp_linear hqM cfg
  have query := budget_ite phase (budget_natDiv qpos (budget_const 2 (.refl _))) number
  have ended := budget_finite (encC := encBool) Bool.not
    (budget_natLt index (count_budget number (.refl _) C d))
  have halted := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod phase ended)
  have st := ComputableInSpace.fst encState (encOption encBool)
  have bit := ComputableInSpace.snd encState (encOption encBool)
  have ph := st.fst'
  have ns := st.snd'.fst'
  have ix := st.snd'.snd'.fst'
  have qs := st.snd'.snd'.snd'
  have qread := budget_comp_linear hqM qs
  have vb := symbol_budget ns ix qread bit (.refl _)
  have args := budget_prod qs vb
  have qnext := budget_comp_linear hnM args
  have qhalt := budget_comp_linear hhM qs
  have hresume := budget_prod (budget_const (encB := encBool) true (.refl _))
    (budget_prod ns (budget_prod (budget_natSucc ix) (budget_const (encB := eCfg) (init D) (.refl _))))
  have hadvance := budget_prod (budget_const (encB := encBool) true (.refl _))
    (budget_prod ns (budget_prod ix qnext))
  have hscan := budget_prod (budget_const (encB := encBool) false (.refl _))
    (budget_prod (budget_natSucc ns)
      (budget_prod (budget_const (encB := encNat) 0 (.refl _)) (budget_const (encB := eCfg) (init D) (.refl _))))
  have hstart := budget_prod (budget_const (encB := encBool) true (.refl _))
    (budget_prod ns (budget_prod (budget_const (encB := encNat) 0 (.refl _)) (budget_const (encB := eCfg) (init D) (.refl _))))
  have nxt := budget_ite ph (budget_ite qhalt hresume hadvance)
    (budget_ite (budget_optionIsSome bit) hscan hstart)
  have canEmit := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && !p.2)
    (budget_prod ph qhalt)
  have em := budget_ite canEmit (budget_comp_linear heM args) (budget_const (encB := encBits) [] (.refl _))
  refine ⟨query.of_enc_eq (fun _ => rfl), nxt.of_enc_eq (fun _ => rfl),
    em.of_enc_eq (fun _ => rfl), halted.of_enc_eq ?_, budget_const (encB := encBits) [] (.refl _)⟩
  intro s
  by_cases h : s.2.2.1 < count C d s.2.1
  · simp [machine, h, Nat.not_le_of_lt h]
  · simp [machine, h, Nat.le_of_not_gt h]

end PredictionDepth.StandardComplexity.LogspaceBatch
