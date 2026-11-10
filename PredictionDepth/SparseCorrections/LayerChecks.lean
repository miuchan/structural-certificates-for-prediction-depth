import PredictionDepth.SparseCorrections.ConeLayout
import PredictionDepth.SparseCorrections.Reduction
import PredictionDepth.FrozenPascal.UniformReducers

/-! Layer failure flags on the consecutive update blocks of a dense cone. -/

namespace PredictionDepth.SparseCorrections.LayerChecks

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity CodeLogspace CodeLogspaceFamilies Turing.MultiTapeTM
open FrozenPascal (notGate andGate)
open BooleanReduction

def eventBlock (q R T : ℕ) (j : Fin (Cone.eventCount q R T)) : Fin T :=
  ((Cone.eventIndex q R T).symm j).1

@[simp] theorem eventBlock_eventIndex (t : Fin T) (j : Fin (coneWidth q R T (t.val + 1))) :
    eventBlock q R T (Cone.eventIndex q R T ⟨t, j⟩) = t := by
  simp [eventBlock]

private def layerWire (t : Fin T) (j : Fin (coneWidth q R T (t.val + 1))) :
    Fin (Cone.eventCount q R T) :=
  Cone.eventIndex q R T ⟨t, j⟩

private def row (q R : ℕ) (t : Fin T) : Gates (Cone.eventCount q R T) 1 :=
  notGate.comp ((andReduce (coneWidth q R T (t.val + 1))).comp (Circuit.wiring signature
    (layerWire t)))

/-- A layer fails if at least one of its local checks fails. The layer
circuits read disjoint intervals of the chronological event layout. -/
def failFlags (q R T : ℕ) : Gates (Cone.eventCount q R T) T :=
  Circuit.pi (row q R)

theorem failFlags_true_iff (q R T : ℕ) (p : Fin (Cone.eventCount q R T) → Bool) (t : Fin T) :
    (failFlags q R T).eval interpretation p t = true ↔
      ∃ j, eventBlock q R T j = t ∧ p j = false := by
  simp only [failFlags, Circuit.eval_pi, row, Circuit.eval_comp, Circuit.eval_wiring,
    notGate, Circuit.eval_oneGate, interpretation, id_eq]
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  change (¬ ((andReduce _).eval interpretation _ 0 = true)) ↔ _
  rw [andReduce_true_iff, not_forall]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨layerWire t i, eventBlock_eventIndex t i,
      Bool.eq_false_iff.mpr hi⟩
  · rintro ⟨j, hj, hp⟩
    obtain ⟨⟨s, i⟩, rfl⟩ := (Cone.eventIndex q R T).surjective j
    rw [eventBlock_eventIndex] at hj
    subst s
    exact ⟨i, Bool.eq_false_iff.mp hp⟩

private theorem sum_layerWidths (q R T : ℕ) :
    (∑ t : Fin T, coneWidth q R T (t.val + 1)) = Cone.eventCount q R T := by
  simpa only [Event, Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_congr (Cone.eventIndex q R T)

theorem failFlags_size (q R T : ℕ) :
    (failFlags q R T).size ≤ 8 * Cone.eventCount q R T + 9 * T := by
  rw [failFlags, Circuit.size_pi]
  calc
    _ ≤ ∑ t : Fin T, (8 * coneWidth q R T (t.val + 1) + 9) := by
      apply Finset.sum_le_sum
      intro t _
      have h := reduce_size andGate true (coneWidth q R T (t.val + 1))
      simp only [row, notGate, Circuit.size_comp, Circuit.size_wiring, Circuit.size_oneGate,
        andReduce]
      simp only [FrozenPascal.andGate_size] at h
      omega
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_layerWidths]; simp [Nat.mul_comm]

theorem failFlags_depth (q R T : ℕ) :
    (failFlags q R T).depth ≤ 2 * Nat.clog 2 (Cone.eventCount q R T) + 3 := by
  apply Circuit.depth_pi_le
  intro t
  have hw : coneWidth q R T (t.val + 1) ≤ Cone.eventCount q R T := by
    rw [← sum_layerWidths]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (coneWidth q R T (j.val + 1)))
      (Finset.mem_univ t)
  have hl := Nat.clog_mono_right 2 hw
  have hr : (andReduce (coneWidth q R T (t.val + 1))).depth ≤
      2 + 2 * Nat.clog 2 (coneWidth q R T (t.val + 1)) := by
    simpa [andReduce, Nat.mul_comm] using reduce_depth andGate true (coneWidth q R T (t.val + 1))
  have hcomp := Circuit.depth_comp_le (andReduce (coneWidth q R T (t.val + 1)))
    (Circuit.wiring signature (layerWire (q := q) (R := R) t))
  simp only [Circuit.depth_wiring, Nat.add_zero] at hcomp
  apply (Circuit.depth_comp_le _ _).trans
  simp only [notGate, Circuit.depth_oneGate]
  omega

private abbrev pairEncoding := encPair encUnary encUnary

/-- The natural-number form of the block address for a serialized event. -/
def blockAddress (q R : ℕ) (p : ℕ × ℕ) : ℕ :=
  Cone.layerOf q R (p.1 - 1) p.2

theorem blockAddress_eq (q R T : ℕ) (j : Fin (Cone.eventCount q R T)) :
    blockAddress q R (T, j.val) = (eventBlock q R T j).val := by
  obtain ⟨⟨t, i⟩, rfl⟩ := (Cone.eventIndex q R T).surjective j
  have hq : 0 < q := by
    by_contra h
    have hzero : q = 0 := Nat.eq_zero_of_not_pos h
    subst q
    have := (Cone.eventIndex 0 R T ⟨t, i⟩).isLt
    simp [Cone.eventCount_eq] at this
  simp only [blockAddress, eventBlock_eventIndex]
  exact Cone.layerOf_eventIndex q R T hq t i

theorem blockAddress_logspace (q R : ℕ) :
    ComputableInLogSpace (blockAddress q R) pairEncoding encUnary := by
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  have h := (Cone.layerOf_logspace q R).comp
    ((hT.unarySub (ComputableInLogSpace.const 1)).pair hj)
  exact h.congr_fun fun _ => rfl

private def width (q R : ℕ) (p : ℕ × ℕ) : ℕ := coneWidth q R p.1 (p.2 + 1)

private theorem width_logspace (q R : ℕ) :
    ComputableInLogSpace (width q R) pairEncoding encUnary := by
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have ht := ComputableInLogSpace.snd encUnary encUnary
  have hs := hT.unarySub (ht.unaryAdd (ComputableInLogSpace.const 1))
  exact (((hs.unaryMulConst (2 * R)).unaryAdd (ComputableInLogSpace.const 1)).unaryMulConst q).congr_fun
    (fun _ => by simp [width, coneWidth, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm])

private def start (q R : ℕ) (p : ℕ × ℕ) : ℕ := Cone.offset q R (p.1 - 1) p.2

private theorem start_logspace (q R : ℕ) :
    ComputableInLogSpace (start q R) pairEncoding encUnary :=
  (Cone.offset_logspace q R).comp
    (((ComputableInLogSpace.fst encUnary encUnary).unarySub (ComputableInLogSpace.const 1)).pair
      (ComputableInLogSpace.snd encUnary encUnary))

private def rawWiring (q R : ℕ) (p : ℕ × ℕ) : RawCode :=
  ([], (List.range (width q R p)).map (start q R p + ·))

private theorem rawWiring_logspace (q R : ℕ) :
    ComputableInLogSpace (rawWiring q R) pairEncoding encCode := by
  have hp := ComputableInLogSpace.fst pairEncoding encUnary
  have hj := ComputableInLogSpace.snd pairEncoding encUnary
  exact (ComputableInLogSpace.const []).pair
    (map_range (width_logspace q R) (((start_logspace q R).comp hp).unaryAdd hj).unaryToBinary)

theorem failFlags_code_logspace (q R : ℕ) :
    ComputableInLogSpace (fun T => (failFlags q R T).code) encUnary encCode := by
  have hM := Cone.eventCount_logspace q R
  apply circuit_pi_of_indexed_logspace hM ComputableInLogSpace.id
  have hT := ComputableInLogSpace.fst encUnary encUnary
  have ht := ComputableInLogSpace.snd encUnary encUnary
  have hred : ComputableInLogSpace (fun p => (andReduce (width q R p)).code) pairEncoding encCode :=
    ((reduce_code_logspace andGate true).comp (width_logspace q R)).congr_fun fun _ => rfl
  have hr := compCode_logspace (hM.comp hT) hred (rawWiring_logspace q R) (fun p => by
    let c := andReduce (width q R p)
    change BoundedReferences ((rawWiring q R p).2.length + c.code.1.length) c.code
    rw [Circuit.length_code_fst]
    simpa [rawWiring] using circuit_boundedReferences c)
  have hnot := compCode_logspace (hM.comp hT) (ComputableInLogSpace.const notGate.code) hr
    (fun p => by
      change BoundedReferences (((andReduce (width q R p)).code.2.map _).length +
        notGate.code.1.length) notGate.code
      simp only [List.length_map, Circuit.code, List.length_ofFn]
      exact circuit_boundedReferences notGate)
  refine ((ht.unaryLt hT).ite hnot (ComputableInLogSpace.const ([], []))).congr_fun ?_
  rintro ⟨T, t⟩
  simp only [Function.comp_apply, decide_eq_true_eq]
  split_ifs with ht
  · have hw : (Circuit.wiring signature (layerWire (q := q) (R := R) ⟨t, ht⟩)).code =
        rawWiring q R (T, t) :=
      Circuit.code_wiring_eq_map (fun i => Cone.eventIndex_val q R T ⟨t, ht⟩ i)
    rw [row, ← compCode_code, ← compCode_code, hw]
    rfl
  · rfl

end PredictionDepth.SparseCorrections.LayerChecks
