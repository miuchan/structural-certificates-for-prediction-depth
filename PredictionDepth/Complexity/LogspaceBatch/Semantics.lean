import PredictionDepth.Complexity.LogspaceBatch.Machine

/-! The batch controller emits exactly the concatenation of its separate runs. -/

namespace PredictionDepth.StandardComplexity.LogspaceBatch

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Turing.VirtualWord

theorem item_runFrom (D : Desc) (C d : ℕ) (w : List Bool) (j T : ℕ)
    (hj : j < count C d w.length)
    (hpre : ∀ t < T, (Native.machine D).halted
      ((Native.machine D).run (frame w ++ List.replicate j true) t) = false)
    (t : ℕ) (ht : t ≤ T) :
    (machine D C d).runFrom w (itemState w.length j (init D)) t =
      itemState w.length j ((Native.machine D).run (frame w ++ List.replicate j true) t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.runFrom_succ, ih (by omega)]
    rw [item_step D C d w j _ hj (hpre t (by omega)), QueryMachine.run_succ]

theorem scan_trace (D : Desc) (C d : ℕ) (w : List Bool) (Inv : State → Prop)
    (hscan : ∀ i ≤ w.length, Inv (scanState D i))
    (hstart : Inv (itemState w.length 0 (init D))) :
    Nonempty (Trace (machine D C d) w Inv (scanState D 0) (itemState w.length 0 (init D)) []) := by
  have hpref : ∀ i, i ≤ w.length →
      Nonempty (Trace (machine D C d) w Inv (scanState D 0) (scanState D i) []) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨Trace.refl _ (hscan 0 (Nat.zero_le _))⟩
    | succ i ih =>
      intro hi
      obtain ⟨hprev⟩ := ih (by omega)
      have hn := scan_step D C d w i (by omega)
      let hs := Trace.single (M := machine D C d) (w := w) (scanState D i)
        (hscan i (by omega)) (by simp [machine, scanState])
        (hn.symm ▸ hscan (i + 1) hi)
      have hout : (machine D C d).emit
          (scanState D i, (machine D C d).read w (scanState D i)) = [] := by
        simp [machine, scanState]
      exact ⟨(hprev.trans (hs.congr hn hout)).congr rfl (by simp)⟩
  obtain ⟨hprev⟩ := hpref w.length le_rfl
  have hn := scan_end D C d w
  let hs := Trace.single (M := machine D C d) (w := w) (scanState D w.length)
    (hscan _ le_rfl) (by simp [machine, scanState]) (hn.symm ▸ hstart)
  have hout : (machine D C d).emit
      (scanState D w.length, (machine D C d).read w (scanState D w.length)) = [] := by
    simp [machine, scanState]
  exact ⟨(hprev.trans (hs.congr hn hout)).congr rfl (by simp)⟩

theorem item_trace (D : Desc) (C d : ℕ) (w : List Bool) (j T : ℕ) (Inv : State → Prop)
    (hj : j < count C d w.length)
    (hpre : ∀ t < T, (Native.machine D).halted
      ((Native.machine D).run (frame w ++ List.replicate j true) t) = false)
    (hhalt : (Native.machine D).halted
      ((Native.machine D).run (frame w ++ List.replicate j true) T) = true)
    (hstates : ∀ t ≤ T, Inv (itemState w.length j
      ((Native.machine D).run (frame w ++ List.replicate j true) t)))
    (hreset : Inv (itemState w.length (j + 1) (init D))) :
    Nonempty (Trace (machine D C d) w Inv
      (itemState w.length j (init D)) (itemState w.length (j + 1) (init D))
      ((Native.machine D).output (frame w ++ List.replicate j true) T)) := by
  let q := (Native.machine D).run (frame w ++ List.replicate j true) T
  have hrun := item_runFrom D C d w j T hj hpre
  let ht : Trace (machine D C d) w Inv
      (itemState w.length j (init D)) (itemState w.length j q)
      ((Native.machine D).output (frame w ++ List.replicate j true) T) :=
    { time := T
      reaches := hrun T le_rfl
      live := by
        intro i hi
        rw [hrun i hi.le]
        exact item_live D C d w.length j _ hj
      bounded := by
        intro i hi
        rw [hrun i hi]
        exact hstates i hi
      emits := by
        rw [QueryMachine.output_eq_of_not_halted _ _ hpre]
        change _ = ((List.range T).map (fun i => (Native.machine D).emit
          ((Native.machine D).run (frame w ++ List.replicate j true) i,
           (Native.machine D).read (frame w ++ List.replicate j true)
             ((Native.machine D).run (frame w ++ List.replicate j true) i)))).flatten ++ []
        rw [List.append_nil, ← List.flatMap_def]
        apply List.flatMap_congr
        intro i hi
        have hi' := List.mem_range.mp hi
        rw [hrun i hi'.le, item_emit D C d w j _ (hpre i hi')] }
  change (Native.machine D).halted q = true at hhalt
  have hn := item_return D C d w j q hj hhalt
  let hr := Trace.single (M := machine D C d) (w := w)
    (itemState w.length j q) (hstates T le_rfl)
    (item_live D C d w.length j q hj) (hn.symm ▸ hreset)
  have hout : (machine D C d).emit
      (itemState w.length j q, (machine D C d).read w (itemState w.length j q)) = [] := by
    simp only [machine, itemState, hhalt, Bool.not_true, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte]
  exact ⟨(ht.trans (hr.congr hn hout)).congr rfl (List.append_nil _)⟩

theorem complete_trace (D : Desc) (C d : ℕ) (w : List Bool) (Inv : State → Prop)
    (g : ℕ → List Bool)
    (hscan : ∀ i ≤ w.length, Inv (scanState D i))
    (hstates : ∀ j ≤ count C d w.length, ∀ t,
      Inv (itemState w.length j ((Native.machine D).run (frame w ++ List.replicate j true) t)))
    (hchunks : ∀ j < count C d w.length, ∃ T,
      (∀ t < T, (Native.machine D).halted
        ((Native.machine D).run (frame w ++ List.replicate j true) t) = false) ∧
      (Native.machine D).halted
        ((Native.machine D).run (frame w ++ List.replicate j true) T) = true ∧
      (Native.machine D).output (frame w ++ List.replicate j true) T = g j) :
    Nonempty (Trace (machine D C d) w Inv (machine D C d).init
      (itemState w.length (count C d w.length) (init D))
      ((List.range (count C d w.length)).flatMap g)) := by
  have hprefix : ∀ j, j ≤ count C d w.length →
      Nonempty (Trace (machine D C d) w Inv
        (itemState w.length 0 (init D)) (itemState w.length j (init D))
        ((List.range j).flatMap g)) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨Trace.refl _ (hstates 0 (Nat.zero_le _) 0)⟩
    | succ j ih =>
      intro hj
      obtain ⟨hprev⟩ := ih (by omega)
      obtain ⟨T, hpre, hhalt, hout⟩ := hchunks j (by omega)
      obtain ⟨hthis⟩ := item_trace D C d w j T Inv (by omega) hpre hhalt
        (fun t _ => hstates j (by omega) t) (hstates (j + 1) hj 0)
      refine ⟨(hprev.trans (hthis.congr rfl hout)).congr rfl ?_⟩
      simp [List.range_succ]
  obtain ⟨hs⟩ := scan_trace D C d w Inv hscan (hstates 0 (Nat.zero_le _) 0)
  obtain ⟨hr⟩ := hprefix _ le_rfl
  exact ⟨(hs.trans hr).congr rfl (List.nil_append _)⟩

end PredictionDepth.StandardComplexity.LogspaceBatch
