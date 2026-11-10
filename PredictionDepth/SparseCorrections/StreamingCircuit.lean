import PredictionDepth.SparseCorrections.ConeLayout
import PredictionDepth.SparseCorrections.Streaming
import PredictionDepth.SparseCorrections.Response

/-!
# Circuits for the full forced streaming response

Every row reads at most one source per layer. Chronological cone offsets
translate the source coordinates to circuit wires. Layers beyond the row's
time supply false leaves to the same balanced parity reducer.
-/

namespace PredictionDepth.SparseCorrections.Streaming

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity Turing.MultiTapeTM
open FrozenPascal (wireBit constBit xorGate reduceBank)
open Linear (F₂)
open scoped BigOperators

abbrev M (T : ℕ) := Cone.eventCount 3 1 T
abbrev V (T : ℕ) := Cone.stateCount 3 1 T
abbrev N (T : ℕ) := M T + Width T 0

/-- From each earlier layer to the next, the cone's left endpoint advances by one. -/
def slotDrift (a : ℕ) : ℕ := if a = 0 then 0 else if a = 1 then 2 else 1

def localSource (t j s : ℕ) : ℕ :=
  j % 3 + 3 * (j / 3 + (t - s) * slotDrift (j % 3))

def sourceIndex (T t j s : ℕ) : ℕ :=
  (if s = 0 then M T else Cone.offset 3 1 (T - 1) (s - 1)) + localSource t j s

def term (T t j s : ℕ) : Gates (N T) 1 :=
  LinearResponse.term (N T) (decide (s ≤ t)) (sourceIndex T t j s)

def row (T t j : ℕ) : Gates (N T) 1 :=
  reduceBank BooleanReduction.xorReduce (fun s : Fin (T + 1) => term T t j s.val)

def circuit (T : ℕ) : Gates (N T) (V T) :=
  Circuit.pi fun k =>
    let p := (Cone.stateIndex 3 1 T).symm k
    row T p.1.val p.2.val

private theorem encoded_source {T t s : ℕ} (hst : s ≤ t) (ht : t ≤ T)
    (i : ℤ) (hi : Cone.InWindow 1 T t i) (a : Fin 3) :
    localSource t (Cone.encodeBit 3 1 T t i hi a).val s =
      (Cone.encodeBit 3 1 T s (source t s i a) (source_in_window hst ht hi a) a).val := by
  have ha := a.isLt
  have he {r : ℕ} {p : ℤ} (hp : Cone.InWindow 1 T r p) :
      (Cone.encodeBit 3 1 T r p hp a).val = a.val + 3 * (p + (T - r : ℕ)).toNat := by
    change a.val + 3 * (p + (1 * (T - r) : ℕ)).toNat = _
    rw [one_mul]
  rw [he hi, he (source_in_window hst ht hi a)]
  have hmod : (a.val + 3 * (i + (T - t : ℕ)).toNat) % 3 = a.val := by omega
  have hdiv : (a.val + 3 * (i + (T - t : ℕ)).toNat) / 3 = (i + (T - t : ℕ)).toNat := by omega
  rw [localSource, hmod, hdiv]
  simp only [Cone.InWindow, Cone.radius, one_mul] at hi
  fin_cases a <;> simp [slotDrift, source, drift] <;> omega

private theorem initialIndex_eq {T t : ℕ} (ht : t ≤ T) (i : ℤ)
    (hi : Cone.InWindow 1 T t i) (a : Fin 3) :
    sourceIndex T t (Cone.encodeBit 3 1 T t i hi a).val 0 =
      (Fin.natAdd (M T) (initWire ht hi a)).val := by
  rw [sourceIndex, ite_eq_left rfl, encoded_source (Nat.zero_le t) ht i hi a]
  rfl

private theorem eventIndex_eq {T t : ℕ} (ht : t ≤ T) (i : ℤ)
    (hi : Cone.InWindow 1 T t i) (a : Fin 3) (s : Fin t) :
    sourceIndex T t (Cone.encodeBit 3 1 T t i hi a).val (s.val + 1) =
      (Fin.castAdd (Width T 0) (Cone.eventIndex 3 1 T (eventWire ht hi a s))).val := by
  rw [sourceIndex, ite_eq_right (Nat.succ_ne_zero _), encoded_source (Nat.succ_le_of_lt s.isLt) ht i hi a]
  simp only [Fin.val_castAdd, eventWire, Cone.eventIndex_val, Nat.add_sub_cancel]

private theorem term_true_eval {T t j s : ℕ} (hst : s ≤ t) (k : Fin (N T))
    (hk : sourceIndex T t j s = k.val) (x : Fin (N T) → Bool) :
    (term T t j s).eval interpretation x 0 = x k := by
  simp [term, LinearResponse.term, hst, hk, k.isLt, Fin.eta]

private theorem term_false_eval {T t j s : ℕ} (hst : t < s) (x : Fin (N T) → Bool) :
    (term T t j s).eval interpretation x 0 = false := by
  unfold term LinearResponse.term
  simp [Nat.not_le_of_gt hst]

private theorem fold_xor_to_sum (xs : List Bool) :
    toBoolRing (xs.foldr (· ^^ ·) false) = (xs.map (toBoolRing : Bool → F₂)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [← Linear.addGate_eq_xor x _, Linear.addGate_ring, ih]

theorem row_correct {T t : ℕ} (ht : t ≤ T) (i : ℤ)
    (hi : Cone.InWindow 1 T t i) (a : Fin 3) (u : Layer (Width T) 0)
    (e : Fin (M T) → Bool) :
    (row T t (Cone.encodeBit 3 1 T t i hi a).val).eval interpretation (Fin.append e u) 0 =
      forcedLayer (Cone.transition 1 T Collision.bitStream) u (e ∘ Cone.eventIndex 3 1 T) t ht
        (Cone.encodeBit 3 1 T t i hi a) := by
  let j := (Cone.encodeBit 3 1 T t i hi a).val
  let f (s : ℕ) : F₂ := toBoolRing ((term T t j s).eval interpretation (Fin.append e u) 0)
  apply toBoolRing.injective
  rw [row, reduceBank, Circuit.eval_comp, BooleanReduction.xorReduce_eval,
    fold_xor_to_sum, List.map_ofFn, List.sum_ofFn, forcedLayer_eq_characteristic]
  simp only [Circuit.eval_pi]
  change (∑ s : Fin (T + 1), f s) = _
  have hsum : (∑ s : Fin (T + 1), f s) = ∑ s : Fin (t + 1), f s := by
    rw [Fin.sum_univ_eq_sum_range f, Fin.sum_univ_eq_sum_range f]
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ ht))
    intro s hs hns
    have hs' : t < s := by simpa using hns
    simp only [f, term_false_eval hs']
    rfl
  rw [hsum, Fin.sum_univ_succ]
  simp only [Fin.val_zero]
  have h₀ : f 0 = toBoolRing (u (initWire ht hi a)) := by
    simp only [f, term_true_eval (Nat.zero_le t) _ (initialIndex_eq ht i hi a), Fin.append_right, j]
  rw [h₀]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  simp only [f, Fin.val_succ, term_true_eval (Nat.succ_le_of_lt s.isLt) _
    (eventIndex_eq ht i hi a s), Fin.append_left, Function.comp_apply, j]

theorem circuit_correct (T : ℕ) (u : Layer (Width T) 0) (e : Fin (M T) → Bool)
    (t : Fin (T + 1)) (b : Fin (Width T t.val)) :
    (circuit T).eval interpretation (Fin.append e u) (Cone.stateIndex 3 1 T ⟨t, b⟩) =
      forcedTrajectory (w := Width T) (T := T) (Cone.transition 1 T Collision.bitStream)
        u (e ∘ Cone.eventIndex 3 1 T) t b := by
  obtain ⟨i, hi, a, rfl⟩ := Cone.exists_encodeBit (q := 3) (R := 1) (T := T) (t := t.val) b
  rw [circuit, Circuit.eval_pi]
  let p : (t : Fin (T + 1)) × Fin (Width T t.val) :=
    ⟨t, Cone.encodeBit 3 1 T t.val i hi a⟩
  let evalRow (r : (t : Fin (T + 1)) × Fin (Width T t.val)) :=
    (row T r.1.val r.2.val).eval interpretation (Fin.append e u) 0
  change evalRow ((Cone.stateIndex 3 1 T).symm (Cone.stateIndex 3 1 T p)) = _
  rw [(Cone.stateIndex 3 1 T).symm_apply_apply p]
  exact row_correct (T := T) (t := t.val) (by omega : t.val ≤ T) i hi a u e

theorem circuit_depth (T : ℕ) :
    (circuit T).depth ≤ 3 + Nat.clog 2 (T + 1) * (xorGate.depth + 1) := by
  apply Circuit.depth_pi_le
  intro k
  have hrow := FrozenPascal.reduceBank_depth BooleanReduction.xorReduce
    (fun s : Fin (T + 1) => term T ((Cone.stateIndex 3 1 T).symm k).1.val
      ((Cone.stateIndex 3 1 T).symm k).2.val s.val) (D := 1) (fun s => by
        unfold term LinearResponse.term
        split_ifs <;> simp)
  exact hrow.trans (by
    have h := BooleanReduction.reduce_depth xorGate false (T + 1)
    unfold BooleanReduction.xorReduce
    omega)

theorem circuit_size (T : ℕ) :
    (circuit T).size ≤ V T * (2 * (T + 2) * (xorGate.size + 3) + (T + 1)) := by
  rw [circuit, Circuit.size_pi]
  calc
    _ ≤ ∑ _ : Fin (V T), (2 * (T + 2) * (xorGate.size + 3) + (T + 1)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [row, reduceBank, Circuit.size_comp, Circuit.size_pi]
      have hterm : (∑ s : Fin (T + 1), (term T ((Cone.stateIndex 3 1 T).symm k).1.val
          ((Cone.stateIndex 3 1 T).symm k).2.val s.val).size) ≤ T + 1 := by
        calc
          _ ≤ ∑ _ : Fin (T + 1), 1 := by
            apply Finset.sum_le_sum
            intro s _
            unfold term LinearResponse.term
            split_ifs <;> simp
          _ = _ := by simp
      simpa [BooleanReduction.xorReduce, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.add_le_add hterm (BooleanReduction.reduce_size xorGate false (T + 1))
    _ = _ := by simp [Nat.mul_comm]


private abbrev encTimeIndex := encPair encUnary encUnary
private abbrev encRow := encPair encTimeIndex encUnary

private theorem width_logspace : ComputableInLogSpace N encUnary encUnary :=
  (Cone.eventCount_logspace 3 1).unaryAdd (inputWidth_logspace 3 1)

private theorem sourceIndex_logspace :
    ComputableInLogSpace (fun p : ((ℕ × ℕ) × ℕ) × ℕ =>
      sourceIndex p.1.1.1 p.1.1.2 p.1.2 p.2) (encPair encRow encUnary) encUnary := by
  have hp := ComputableInLogSpace.fst encRow encUnary
  have hs := ComputableInLogSpace.snd encRow encUnary
  have hq := (ComputableInLogSpace.fst encTimeIndex encUnary).comp hp
  have hj := (ComputableInLogSpace.snd encTimeIndex encUnary).comp hp
  have hT := (ComputableInLogSpace.fst encUnary encUnary).comp hq
  have ht := (ComputableInLogSpace.snd encUnary encUnary).comp hq
  have ha := hj.unaryMod (ComputableInLogSpace.const 3)
  have hslot : ComputableInLogSpace (fun p : ((ℕ × ℕ) × ℕ) × ℕ => slotDrift (p.1.2 % 3))
      (encPair encRow encUnary) encUnary := by
    refine ((ha.unaryEq (ComputableInLogSpace.const 0)).ite (ComputableInLogSpace.const 0)
      ((ha.unaryEq (ComputableInLogSpace.const 1)).ite (ComputableInLogSpace.const 2)
        (ComputableInLogSpace.const 1))).congr_fun ?_
    intro p
    simp [slotDrift]
  have hlocal := ha.unaryAdd (((hj.unaryDiv (ComputableInLogSpace.const 3)).unaryAdd
    ((ht.unarySub hs).unaryMul hslot)).unaryMulConst 3)
  have hoff := (Cone.offset_logspace 3 1).comp
    ((hT.unarySub (ComputableInLogSpace.const 1)).pair
      (hs.unarySub (ComputableInLogSpace.const 1)))
  have hbase := (hs.unaryEq (ComputableInLogSpace.const 0)).ite
    ((Cone.eventCount_logspace 3 1).comp hT) hoff
  exact (hbase.unaryAdd hlocal).congr_fun (fun _ => by simp [sourceIndex, localSource, Nat.mul_comm])

private theorem term_code_logspace :
    ComputableInLogSpace (fun p : ((ℕ × ℕ) × ℕ) × ℕ => (term p.1.1.1 p.1.1.2 p.1.2 p.2).code)
      (encPair encRow encUnary) encCode := by
  have hp := ComputableInLogSpace.fst encRow encUnary
  have hs := ComputableInLogSpace.snd encRow encUnary
  have hq := (ComputableInLogSpace.fst encTimeIndex encUnary).comp hp
  have hT := (ComputableInLogSpace.fst encUnary encUnary).comp hq
  have ht := (ComputableInLogSpace.snd encUnary encUnary).comp hq
  have hn := width_logspace.comp hT
  have hi := sourceIndex_logspace
  have hwire : ComputableInLogSpace
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => (([], [sourceIndex p.1.1.1 p.1.1.2 p.1.2 p.2]) :
        CodeLogspace.RawCode)) (encPair encRow encUnary) encCode :=
    (ComputableInLogSpace.const []).pair (ComputableInLogSpace.listSingleton.comp hi.unaryToBinary)
  refine (((hi.unaryLt hn).bool_and (hs.unaryLe ht)).ite hwire
    (FrozenPascal.Code.constant hn false)).congr_fun ?_
  intro p
  change (term p.1.1.1 p.1.1.2 p.1.2 p.2).code =
    if decide (sourceIndex p.1.1.1 p.1.1.2 p.1.2 p.2 < N p.1.1.1) && decide (p.2 ≤ p.1.1.2)
      then ([], [sourceIndex p.1.1.1 p.1.1.2 p.1.2 p.2]) else (constBit (N p.1.1.1) false).code
  by_cases h : sourceIndex p.1.1.1 p.1.1.2 p.1.2 p.2 < N p.1.1.1
  · by_cases hst : p.2 ≤ p.1.1.2
    · simp only [term, LinearResponse.term, h, hst, dite_true, decide_true, Bool.true_and, ↓reduceIte]
      rfl
    · simp [term, LinearResponse.term, h, hst]
  · simp [term, LinearResponse.term, h]

private theorem row_code_logspace :
    ComputableInLogSpace (fun p : (ℕ × ℕ) × ℕ => (row p.1.1 p.1.2 p.2).code) encRow encCode := by
  have hp := (ComputableInLogSpace.fst encUnary encUnary).comp
    (ComputableInLogSpace.fst encTimeIndex encUnary)
  have hn := width_logspace.comp hp
  have hm := hp.unaryAdd (ComputableInLogSpace.const 1)
  have hxor : ComputableInLogSpace (fun k => (BooleanReduction.xorReduce k).code) encUnary encCode := by
    unfold BooleanReduction.xorReduce
    exact BooleanReduction.reduce_code_logspace xorGate false
  exact FrozenPascal.Code.reduceBank hxor hn hm term_code_logspace


theorem circuit_code_logspace :
    ComputableInLogSpace (fun T => (circuit T).code) encUnary encCode := by
  let work (T k : ℕ) : Gates (N T) 1 :=
    let t := Cone.layerOf 3 1 T k
    row T t (k - Cone.offset 3 1 T t)
  have hp := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  have ht := Cone.layerOf_logspace 3 1
  have ho := (Cone.offset_logspace 3 1).comp (hp.pair ht)
  have hraw := row_code_logspace.comp ((hp.pair ht).pair (hj.unarySub ho))
  have hw : ComputableInLogSpace (fun p : ℕ × ℕ => (work p.1 p.2).code)
      (encPair encUnary encUnary) encCode :=
    hraw.congr_fun (fun _ => rfl)
  refine (FrozenPascal.Code.bank (c := work) width_logspace (Cone.stateCount_logspace 3 1)
    hw).congr_fun ?_
  intro T
  apply congrArg (fun cs : Fin (V T) → Gates (N T) 1 => (Circuit.pi cs).code)
  funext k
  obtain ⟨⟨t, b⟩, rfl⟩ := (Cone.stateIndex 3 1 T).surjective k
  dsimp only [work]
  rw [Cone.layerOf_stateIndex 3 1 T (by decide), Equiv.symm_apply_apply,
    Cone.stateIndex_val, Nat.add_sub_cancel_left]

end PredictionDepth.SparseCorrections.Streaming
