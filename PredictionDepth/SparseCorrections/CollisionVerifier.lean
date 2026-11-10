import PredictionDepth.SparseCorrections.Collision
import PredictionDepth.SparseCorrections.ConeLayout
import PredictionDepth.SparseCorrections.Compiler

/-! Local circuit checks for the reversible collision rule. -/

namespace PredictionDepth.SparseCorrections.Collision

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity Turing.MultiTapeTM
open Cone (stateCount eventCount stateIndex eventIndex offset radius)

private def mux : Gates 3 1 :=
  let selector : Formula signature 3 := .input 0
  ((selector.and (.input 2)).or (selector.not.and (.input 1))).toCircuit

@[simp] private theorem mux_eval (x : Fin 3 → Bool) :
    mux.eval interpretation x 0 = if x 0 then x 2 else x 1 := by
  simp [mux]
  cases x 0 <;> simp

private def inputTrackIndex (a : ℕ) (k : Fin 3) : ℕ :=
  if k.val = 0 then (a + 2) % 3 else if k.val = 1 then a else (a + 1) % 3

private def inputTrack (a k : Fin 3) : Fin 3 :=
  ⟨inputTrackIndex a.val k, by
    unfold inputTrackIndex
    split_ifs <;> first | exact Nat.mod_lt _ (by decide) | exact a.isLt⟩

private def siteShift (a : Fin 3) : ℕ := 2 * a.val % 3

private theorem siteShift_le (a : Fin 3) : siteShift a ≤ 2 := by
  have := Nat.mod_lt (2 * a.val) (by decide : 0 < 3)
  unfold siteShift
  omega

private theorem radius_step (t : Fin T) : radius 1 T t.val = radius 1 T (t.val + 1) + 1 := by
  simp only [radius, one_mul]
  omega

private def sourceSite (t : Fin T) (j : Fin (2 * radius 1 T (t.val + 1) + 1))
    (a : Fin 3) : Fin (2 * radius 1 T t.val + 1) :=
  ⟨j.val + siteShift a, by
    have := j.isLt
    have := siteShift_le a
    rw [radius_step t]
    omega⟩

private def eventParts (t : Fin T) (i : Fin (coneWidth 3 1 T (t.val + 1))) :
    Fin (2 * radius 1 T (t.val + 1) + 1) × Fin 3 :=
  finProdFinEquiv.symm i

private def checkInputs (t : Fin T) (i : Fin (coneWidth 3 1 T (t.val + 1))) (k : Fin 3) :
    Fin (stateCount 3 1 T) :=
  let p := eventParts t i
  stateIndex 3 1 T ⟨t.castSucc, finProdFinEquiv (sourceSite t p.1 p.2, inputTrack p.2 k)⟩

def check (T : ℕ) (i : Fin (eventCount 3 1 T)) : Gates (stateCount 3 1 T) 1 :=
  let v := (eventIndex 3 1 T).symm i
  equalCheck mux (checkInputs v.1 v.2) (stateIndex 3 1 T ⟨v.1.succ, v.2⟩)

theorem check_depth (T : ℕ) (i : Fin (eventCount 3 1 T)) : (check T i).depth ≤ 7 :=
  (equalCheck_depth _ _ _).trans (by decide +kernel)

theorem check_size (T : ℕ) (i : Fin (eventCount 3 1 T)) : (check T i).size = 10 := by
  unfold check
  rw [equalCheck_size]
  decide +kernel

private theorem decode_read (t : Fin (T + 1)) (i : Fin (coneWidth 3 1 T t.val))
    (y : Fin (stateCount 3 1 T) → Bool) :
    decodeTrajectory (stateIndex 3 1 T).symm y t i = y (stateIndex 3 1 T ⟨t, i⟩) := rfl

private theorem extend_source (t : Fin T) (j : Fin (2 * radius 1 T (t.val + 1) + 1))
    (a : Fin 3) (u : Layer (coneWidth 3 1 T) t.val) :
    Cone.extend 1 T t.val u (Cone.site 1 T t.val (sourceSite t j a)) =
      fun k => u (finProdFinEquiv (sourceSite t j a, k)) := by
  funext k
  rw [Cone.extend, dite_eq_left (Cone.site_in_window _ _ _ _), Cone.encodeBit, Cone.siteIndex_site]

private theorem sourceSite_position (t : Fin T) (j : Fin (2 * radius 1 T (t.val + 1) + 1))
    (a : Fin 3) :
    Cone.site 1 T t.val (sourceSite t j a) =
      Cone.site 1 T (t.val + 1) j + ((siteShift a : ℤ) - 1) := by
  unfold Cone.site sourceSite
  push_cast
  rw [radius_step t]
  push_cast
  ring

private theorem streamed_track (x : Cone.Config 3) (i : ℤ) (a : Fin 3) :
    bitStep x i a = (collide (Cell.ofBits (x (i + ((siteShift a : ℤ) - 1))))).bits a := by
  fin_cases a
  · simp [bitStep, lift, step, stream, siteShift, Cell.bits, Int.sub_eq_add_neg]
  · rfl
  · simp [bitStep, lift, step, stream, siteShift, Cell.bits]

private theorem collide_mux : ∀ (x : Fin 3 → Bool) (a : Fin 3),
    (collide (Cell.ofBits x)).bits a =
      mux.eval interpretation (x ∘ inputTrack a) 0 := by decide +kernel

private theorem transition_mux (t : Fin T) (j : Fin (2 * radius 1 T (t.val + 1) + 1))
    (a : Fin 3) (u : Layer (coneWidth 3 1 T) t.val) :
    let i : Fin (coneWidth 3 1 T (t.val + 1)) := finProdFinEquiv (j, a)
    let x := fun k : Fin 3 => u (finProdFinEquiv (sourceSite t j a, inputTrack a k))
    Cone.transition 1 T bitStep t.val u i = mux.eval interpretation x 0 := by
  dsimp only
  change Cone.restrict 1 T (t.val + 1) (bitStep (Cone.extend 1 T t.val u))
    (finProdFinEquiv (j, a)) = _
  simp only [Cone.restrict, Equiv.symm_apply_apply]
  rw [streamed_track, ← sourceSite_position, extend_source, collide_mux]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem check_correct (T : ℕ) (y : Fin (stateCount 3 1 T) → Bool) (i : Fin (eventCount 3 1 T)) :
    (check T i).eval interpretation y 0 = true ↔
      let v := (eventIndex 3 1 T).symm i
      let z := decodeTrajectory (stateIndex 3 1 T).symm y
      z v.1.succ v.2 = Cone.transition 1 T bitStep v.1 (z v.1.castSucc) v.2 := by
  unfold check
  rw [equalCheck_true_iff]
  dsimp only
  let v := (eventIndex 3 1 T).symm i
  let p := eventParts v.1 v.2
  let z := decodeTrajectory (stateIndex 3 1 T).symm y
  change y (stateIndex 3 1 T ⟨v.1.succ, v.2⟩) =
    mux.eval interpretation (y ∘ checkInputs v.1 v.2) 0 ↔
    z v.1.succ v.2 = Cone.transition 1 T bitStep v.1 (z v.1.castSucc) v.2
  have h := transition_mux v.1 p.1 p.2 (z v.1.castSucc)
  dsimp only at h
  have hb : finProdFinEquiv (p.1, p.2) = v.2 := finProdFinEquiv.apply_symm_apply v.2
  have h' := (congrArg (Cone.transition 1 T bitStep v.1 (z v.1.castSucc)) hb.symm).trans h
  rw [← decode_read v.1.succ v.2 y, h']
  rfl

private abbrev wireEncoding := encPair encUnary encUnary

private def updateTime (p : ℕ × ℕ) : ℕ := Cone.layerOf 3 1 (p.1 - 1) p.2

private def outputBit (p : ℕ × ℕ) : ℕ := p.2 - offset 3 1 (p.1 - 1) (updateTime p)

private def inputAddress (p : ℕ × ℕ) (k : Fin 3) : ℕ :=
  let b := outputBit p
  let a := b % 3
  offset 3 1 p.1 (updateTime p) + (b / 3 + 2 * a % 3) * 3 + inputTrackIndex a k

private def outputAddress (p : ℕ × ℕ) : ℕ := offset 3 1 p.1 (updateTime p + 1) + outputBit p

private theorem decode_time_bit (t : Fin T) (i : Fin (coneWidth 3 1 T (t.val + 1))) :
    let p := (T, (eventIndex 3 1 T ⟨t, i⟩).val)
    updateTime p = t.val ∧ outputBit p = i.val := by
  dsimp only
  have ht := Cone.layerOf_eventIndex 3 1 T (by decide) t i
  refine ⟨ht, ?_⟩
  rw [outputBit, updateTime, ht, Cone.eventIndex_val]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem inputAddress_val (t : Fin T) (i : Fin (coneWidth 3 1 T (t.val + 1))) (k : Fin 3) :
    inputAddress (T, (eventIndex 3 1 T ⟨t, i⟩).val) k = (checkInputs t i k).val := by
  have h := decode_time_bit t i
  unfold inputAddress checkInputs
  rw [Cone.stateIndex_val]
  simp only [h.1, h.2, Fin.val_castSucc]
  have hs : (eventParts t i).1.val = i.val / 3 := rfl
  have ha : (eventParts t i).2.val = i.val % 3 := rfl
  simp [finProdFinEquiv, sourceSite, siteShift, inputTrack, hs, ha,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm]

private theorem outputAddress_val (t : Fin T) (i : Fin (coneWidth 3 1 T (t.val + 1))) :
    outputAddress (T, (eventIndex 3 1 T ⟨t, i⟩).val) = (stateIndex 3 1 T ⟨t.succ, i⟩).val := by
  have h := decode_time_bit t i
  simp [outputAddress, h.1, h.2, Cone.stateIndex_val]

set_option maxHeartbeats 700000 in
private theorem updateTime_logspace :
    ComputableInLogSpace updateTime wireEncoding encUnary := by
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have h := (Cone.layerOf_logspace 3 1).comp
    ((hT.unarySub (ComputableInLogSpace.const 1)).pair hi)
  exact h.congr_fun (fun _ => rfl)

private theorem outputBit_logspace :
    ComputableInLogSpace outputBit wireEncoding encUnary := by
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have ho := (Cone.offset_logspace 3 1).comp
    ((hT.unarySub (ComputableInLogSpace.const 1)).pair updateTime_logspace)
  exact hi.unarySub ho

private theorem inputAddress_logspace (k : Fin 3) :
    ComputableInLogSpace (fun p => inputAddress p k) wireEncoding encUnary := by
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have hb := outputBit_logspace
  have h3 := ComputableInLogSpace.const (encIn := wireEncoding) (encMid := encUnary) 3
  have ha := hb.unaryMod h3
  have hs := (ha.unaryMulConst 2).unaryMod h3
  have harg : ComputableInLogSpace (fun p => inputTrackIndex (outputBit p % 3) k)
      wireEncoding encUnary := by
    fin_cases k
    · exact (ha.unaryAdd (ComputableInLogSpace.const 2)).unaryMod h3
    · exact ha
    · exact (ha.unaryAdd (ComputableInLogSpace.const 1)).unaryMod h3
  have ho := (Cone.offset_logspace 3 1).comp (hT.pair updateTime_logspace)
  exact ((ho.unaryAdd (((hb.unaryDiv h3).unaryAdd hs).unaryMulConst 3)).unaryAdd harg).congr_fun
    (fun _ => by simp [inputAddress, Nat.mul_comm])

private theorem outputAddress_logspace :
    ComputableInLogSpace outputAddress wireEncoding encUnary := by
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have ho := (Cone.offset_logspace 3 1).comp
    (hT.pair (updateTime_logspace.unaryAdd (ComputableInLogSpace.const 1)))
  exact ho.unaryAdd outputBit_logspace

private theorem stateCount_pos (T : ℕ) : 0 < stateCount 3 1 T := by
  rw [Cone.stateCount_eq]
  positivity

private def totalInput (p : ℕ × ℕ) (k : Fin 3) : Fin (stateCount 3 1 p.1) :=
  ⟨inputAddress p k % stateCount 3 1 p.1, Nat.mod_lt _ (stateCount_pos _)⟩

private def totalOutput (p : ℕ × ℕ) : Fin (stateCount 3 1 p.1) :=
  ⟨outputAddress p % stateCount 3 1 p.1, Nat.mod_lt _ (stateCount_pos _)⟩

theorem check_code_logspace :
    ComputableInLogSpace (fun p : ℕ × ℕ =>
      if h : p.2 < eventCount 3 1 p.1 then (check p.1 ⟨p.2, h⟩).code else ([], []))
      wireEncoding encCode := by
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have hi := ComputableInLogSpace.snd encUnary encUnary
  have hV := (Cone.stateCount_logspace 3 1).comp hT
  have hc := equalCheck_code_logspace mux (inputs := totalInput) (out := totalOutput) hV
    (fun k => ((inputAddress_logspace k).unaryMod hV).unaryToBinary)
    (outputAddress_logspace.unaryMod hV)
  refine ((hi.unaryLt ((Cone.eventCount_logspace 3 1).comp hT)).ite hc
    (ComputableInLogSpace.const ([], []))).congr_fun ?_
  intro ⟨T, j⟩
  simp only [Function.comp_apply, decide_eq_true_eq]
  split_ifs with h
  · unfold check
    let v := (eventIndex 3 1 T).symm ⟨j, h⟩
    have hj : (eventIndex 3 1 T ⟨v.1, v.2⟩).val = j := by simp [v, Sigma.eta]
    have ha : totalInput (T, j) = checkInputs v.1 v.2 := by
      funext k
      apply Fin.ext
      simp only [totalInput, ← hj, inputAddress_val, Nat.mod_eq_of_lt (checkInputs v.1 v.2 k).isLt]
    have ho : totalOutput (T, j) = stateIndex 3 1 T ⟨v.1.succ, v.2⟩ := by
      apply Fin.ext
      simp only [totalOutput, ← hj, outputAddress_val,
        Nat.mod_eq_of_lt (stateIndex 3 1 T ⟨v.1.succ, v.2⟩).isLt]
    rw [ha, ho]
  · rfl

end PredictionDepth.SparseCorrections.Collision
