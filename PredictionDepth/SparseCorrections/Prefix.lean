import PredictionDepth.SparseCorrections.Reduction
import PredictionDepth.Complexity.CircuitWriter

/-!
# Exclusive parallel prefix OR

Pair adjacent leaves, recurse on their summaries, then expand the prefix
of each pair to the two original leaves. The original inputs are retained
as wires. The construction shares pair summaries and uses linear size.
-/

namespace PredictionDepth.SparseCorrections.Prefix

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FrozenPascal (Gates wireBit constBit)

private def left (j : Fin m) : Fin (m * 2) := ⟨2 * j.val, by have := j.isLt; omega⟩
private def right (j : Fin m) : Fin (m * 2) := ⟨2 * j.val + 1, by have := j.isLt; omega⟩
private def pair (i : Fin (m * 2)) : Fin m := ⟨i.val / 2, by have := i.isLt; omega⟩

private def summarize (m : ℕ) : Gates (m * 2) m :=
  Circuit.pi fun j => Circuit.oneGate .or (fun i => if i = 0 then left j else right j)

@[simp] private theorem summarize_eval (x : Fin (m * 2) → Bool) (j : Fin m) :
    (summarize m).eval interpretation x j = (x (left j) || x (right j)) := by
  simp [summarize, interpretation]

private def expandEntry (i : Fin (m * 2)) : Gates (m + m * 2) 1 :=
  if i.val % 2 = 0 then Circuit.oneGate .and (fun _ => (pair i).castAdd _)
  else Circuit.oneGate .or (fun j =>
    if j = 0 then (pair i).castAdd _ else Fin.natAdd m (left (pair i)))

private def expand (m : ℕ) : Gates (m + m * 2) (m * 2) :=
  Circuit.pi expandEntry

private theorem expand_eval (p : Fin m → Bool) (x : Fin (m * 2) → Bool) (i : Fin (m * 2)) :
    (expand m).eval interpretation (Fin.append p x) i =
      (p (pair i) || (decide (i.val % 2 ≠ 0) && x (left (pair i)))) := by
  rw [expand, Circuit.eval_pi]
  by_cases h : i.val % 2 = 0 <;> simp [expandEntry, h, interpretation]

private def scanPow : (d : ℕ) → Gates (2 ^ d) (2 ^ d)
  | 0 => constBit 1 false
  | d + 1 => (expand (2 ^ d)).comp
      (((scanPow d).comp (summarize (2 ^ d))).append (Circuit.id signature (2 ^ d * 2)))

set_option backward.isDefEq.respectTransparency false in
private theorem scanPow_true_iff (d : ℕ) (x : Fin (2 ^ d) → Bool) (i : Fin (2 ^ d)) :
    (scanPow d).eval interpretation x i = true ↔ ∃ j : Fin (2 ^ d), j < i ∧ x j = true := by
  induction d with
  | zero =>
    rw [Fin.eq_zero i]
    simp [scanPow]
  | succ d ih =>
    rw [scanPow, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_comp,
      Circuit.id, Circuit.eval_wiring, Function.comp_id, expand_eval, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
    simp only [summarize_eval, Bool.or_eq_true]
    have hi := i.isLt
    constructor
    · rintro (⟨j, hji, hj | hj⟩ | ⟨ho, hj⟩)
      · exact ⟨left j, by
          change j.val < i.val / 2 at hji
          change 2 * j.val < i.val
          omega, hj⟩
      · exact ⟨right j, by
          change j.val < i.val / 2 at hji
          change 2 * j.val + 1 < i.val
          omega, hj⟩
      · exact ⟨left (pair i), by
          change 2 * (i.val / 2) < i.val
          omega, hj⟩
    · rintro ⟨j, hji, hj⟩
      have hjlt := j.isLt
      change j.val < i.val at hji
      by_cases hpair : j.val / 2 < i.val / 2
      · left
        refine ⟨pair j, hpair, ?_⟩
        by_cases hrem : j.val % 2 = 0
        · left
          have he : left (pair j) = j := Fin.ext (by change 2 * (j.val / 2) = j.val; omega)
          rwa [he]
        · right
          have he : right (pair j) = j := Fin.ext (by change 2 * (j.val / 2) + 1 = j.val; omega)
          rwa [he]
      · right
        have he : left (pair i) = j := Fin.ext (by change 2 * (i.val / 2) = j.val; omega)
        exact ⟨by omega, he ▸ hj⟩

private theorem summarize_depth (m : ℕ) : (summarize m).depth ≤ 1 := by
  apply Circuit.depth_pi_le
  intro j
  simp

private theorem expand_depth (m : ℕ) : (expand m).depth ≤ 1 := by
  apply Circuit.depth_pi_le
  intro j
  unfold expandEntry
  split_ifs <;> simp

private theorem summarize_size (m : ℕ) : (summarize m).size = m := by
  simp [summarize, Circuit.size_pi]

private theorem expand_size (m : ℕ) : (expand m).size ≤ m * 2 := by
  rw [expand, Circuit.size_pi]
  calc
    _ ≤ ∑ _ : Fin (m * 2), 1 := by
      apply Finset.sum_le_sum
      intro j _
      unfold expandEntry
      split_ifs <;> simp
    _ = _ := by simp

set_option backward.isDefEq.respectTransparency false in
private theorem scanPow_depth (d : ℕ) : (scanPow d).depth ≤ 2 * d + 1 := by
  induction d with
  | zero => simp [scanPow]
  | succ d ih =>
    rw [scanPow]
    have hmid := (Circuit.depth_comp_le (scanPow d) (summarize (2 ^ d))).trans
      (Nat.add_le_add ih (summarize_depth _))
    have ha := (Circuit.depth_append_le ((scanPow d).comp (summarize (2 ^ d)))
      (Circuit.id signature (2 ^ d * 2))).trans
      (max_le hmid (by simp [Circuit.id]))
    exact (Circuit.depth_comp_le (expand (2 ^ d))
      (((scanPow d).comp (summarize (2 ^ d))).append (Circuit.id signature (2 ^ d * 2)))).trans
        (by have := expand_depth (2 ^ d); omega)

set_option backward.isDefEq.respectTransparency false in
private theorem scanPow_size (d : ℕ) : (scanPow d).size ≤ 3 * 2 ^ d - 2 := by
  induction d with
  | zero => simp [scanPow]
  | succ d ih =>
    rw [scanPow, Circuit.size_comp, Circuit.size_append, Circuit.size_comp,
      summarize_size, Circuit.id, Circuit.size_wiring, Nat.add_zero]
    change _ ≤ 3 * (2 ^ d * 2) - 2
    have h := expand_size (2 ^ d)
    have hp := Nat.two_pow_pos d
    omega

private def pad (m : ℕ) : Gates m (2 ^ BlockSummary.paddingDepth m) :=
  Circuit.pi fun i => if h : i.val < m then wireBit ⟨i.val, h⟩ else constBit m false

private theorem pad_depth (m : ℕ) : (pad m).depth ≤ 1 := by
  apply Circuit.depth_pi_le
  intro j
  split_ifs <;> simp

private theorem pad_size (m : ℕ) : (pad m).size ≤ BlockSummary.paddedCount m := by
  rw [pad, Circuit.size_pi]
  calc
    _ ≤ ∑ _ : Fin (BlockSummary.paddedCount m), 1 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> simp
    _ = _ := by simp

def scan (m : ℕ) : Gates m m :=
  (Circuit.wiring signature (Fin.castLE (show m ≤ 2 ^ BlockSummary.paddingDepth m
    from BlockSummary.le_paddedCount m))).comp
    ((scanPow (BlockSummary.paddingDepth m)).comp (pad m))

theorem scan_true_iff (x : Fin m → Bool) (i : Fin m) :
    (scan m).eval interpretation x i = true ↔ ∃ j : Fin m, j < i ∧ x j = true := by
  rw [scan, Circuit.eval_comp, Circuit.eval_wiring, Function.comp_apply, Circuit.eval_comp,
    scanPow_true_iff]
  constructor
  · rintro ⟨j, hji, hj⟩
    have hb : j.val < m := (show j.val < i.val from hji).trans i.isLt
    refine ⟨⟨j.val, hb⟩, hji, ?_⟩
    simpa only [pad, Circuit.eval_pi, dite_eq_left hb, FrozenPascal.wireBit_eval] using hj
  · rintro ⟨j, hji, hj⟩
    let j' : Fin (2 ^ BlockSummary.paddingDepth m) := j.castLE (BlockSummary.le_paddedCount m)
    refine ⟨j', hji, ?_⟩
    have hb : j'.val < m := j.isLt
    simp only [pad, Circuit.eval_pi, dite_eq_left hb, FrozenPascal.wireBit_eval]
    exact hj

theorem scan_depth (m : ℕ) : (scan m).depth ≤ 2 * Nat.clog 2 m + 2 := by
  unfold scan
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [Circuit.depth_wiring, zero_add]
  refine (Circuit.depth_comp_le _ _).trans ?_
  have h₁ := scanPow_depth (BlockSummary.paddingDepth m)
  have h₂ := pad_depth m
  calc
    _ ≤ (2 * BlockSummary.paddingDepth m + 1) + 1 := Nat.add_le_add h₁ h₂
    _ = _ := by rw [BlockSummary.paddingDepth_eq_clog]

theorem scan_size (m : ℕ) : (scan m).size ≤ 8 * (m + 1) := by
  simp only [scan, Circuit.size_comp, Circuit.size_wiring, Nat.add_zero]
  have h₁ := scanPow_size (BlockSummary.paddingDepth m)
  have h₂ := pad_size m
  have h₃ := BlockSummary.paddedCount_le m
  change _ ≤ 3 * BlockSummary.paddedCount m - 2 at h₁
  omega

/-! ## Exact serialized layout

The upsweep gates are ordered from leaves to root. The downsweep gates
follow in reverse layer order. One AND copy for each even output makes each
downsweep layer occupy consecutive wires, including its copied prefixes.
-/

open StandardComplexity Turing.MultiTapeTM CodeLogspace CodeLogspaceFamilies

private def upGate (base i : ℕ) : Op × List ℕ :=
  (.or, [base + 2 * i, base + 2 * i + 1])

private def downGate (base pref i : ℕ) : Op × List ℕ :=
  let p := pref + i / 2
  if i % 2 = 0 then (.and, [p, p]) else (.or, [p, base + 2 * (i / 2)])

private theorem summarize_code (m : ℕ) :
    (summarize m).code =
      ((List.range m).map (upGate 0), (List.range m).map (fun i => m * 2 + i)) := by
  rw [summarize, CircuitWriter.pi_inputGate_code _ (fun i => upGate 0 i.val)]
  · simp only [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map, Function.comp_def]
  · intro i
    simp [Circuit.oneGate, Circuit.code, Program.code, Line.code, List.ofFn_succ,
      upGate, left, right]
  · intro i j hj
    have hi := i.isLt
    simp [upGate] at hj
    omega

private theorem expand_code (m : ℕ) :
    (expand m).code =
      ((List.range (m * 2)).map (downGate m 0),
        (List.range (m * 2)).map (fun i => m + m * 2 + i)) := by
  rw [expand, CircuitWriter.pi_inputGate_code _ (fun i => downGate m 0 i.val)]
  · simp only [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map, Function.comp_def]
  · intro i
    unfold expandEntry
    by_cases hi : i.val % 2 = 0
    · rw [ite_eq_left hi]
      simp [hi, downGate, Circuit.oneGate, Circuit.code, Program.code,
        Line.code, List.ofFn_succ, pair]
    · rw [ite_eq_right hi]
      simp [hi, downGate, Circuit.oneGate, Circuit.code, Program.code,
        Line.code, List.ofFn_succ, pair, left]
  · intro i j hj
    have hi := i.isLt
    by_cases h : i.val % 2 = 0 <;> simp [downGate, h] at hj <;> omega

/-- The active width of a level is the smallest power of two at least its
index-dependent counter. This uses the existing padded-count transducer. -/
private def gateCode (P g : ℕ) : Op × List ℕ :=
  if g < P - 1 then
    let w := BlockSummary.paddedCount (P - g)
    upGate (if w = P then 0 else 2 * (P - w)) (g - (P - w))
  else if g = P - 1 then (.const false, [])
  else
    let w := BlockSummary.paddedCount ((g - P + 2) / 2 + 1)
    downGate (if w = P then 0 else 2 * (P - w))
      (2 * P + w / 2 - 2) (g - (P + w - 2))

private def powCode (P : ℕ) : RawCode :=
  ((List.range (3 * P - 2)).map (gateCode P),
    (List.range P).map (fun j => 3 * P - 2 + j))

private theorem padded_le_pow {d n : ℕ} (h : n ≤ 2 ^ d) :
    BlockSummary.paddedCount n ≤ 2 ^ d := by
  unfold BlockSummary.paddedCount
  rw [BlockSummary.paddingDepth_eq_clog]
  exact Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow h)

private theorem padded_eq_pow {d n : ℕ} (hl : 2 ^ d < n) (hr : n ≤ 2 ^ (d + 1)) :
    BlockSummary.paddedCount n = 2 ^ (d + 1) := by
  unfold BlockSummary.paddedCount
  rw [BlockSummary.paddingDepth_eq_clog]
  congr 1
  apply Nat.le_antisymm (Nat.clog_le_of_le_pow hr)
  have hpow := Nat.le_pow_clog (by decide : 1 < 2) n
  by_contra! h
  exact (not_lt_of_ge (hpow.trans (Nat.pow_le_pow_right (by decide) (by omega)))) hl

private theorem gateCode_first (d j : ℕ) (hj : j < 2 ^ d) :
    gateCode (2 ^ d * 2) j = upGate 0 j := by
  have hw : BlockSummary.paddedCount (2 ^ d * 2 - j) = 2 ^ d * 2 := by
    rw [← pow_succ]
    exact padded_eq_pow (by rw [pow_succ]; omega) (Nat.sub_le ..)
  rw [gateCode, ite_eq_left (by omega), hw]
  simp

private theorem gateCode_shift (d j : ℕ) (hj : j < 3 * 2 ^ d - 2) :
    gateCode (2 ^ d * 2) (2 ^ d + j) =
      ((gateCode (2 ^ d) j).1, (gateCode (2 ^ d) j).2.map (fun i => 2 ^ d * 2 + i)) := by
  let m := 2 ^ d
  have hm : 0 < m := Nat.two_pow_pos d
  change j < 3 * m - 2 at hj
  change gateCode (m * 2) (m + j) =
    ((gateCode m j).1, (gateCode m j).2.map (fun i => m * 2 + i))
  by_cases hup : j < m - 1
  · have hup' : m + j < m * 2 - 1 := by omega
    have hx : m * 2 - (m + j) = m - j := by omega
    rw [gateCode, ite_eq_left hup', hx, gateCode, ite_eq_left hup]
    let w := BlockSummary.paddedCount (m - j)
    have hw : w ≤ m := padded_le_pow (Nat.sub_le ..)
    change upGate (if w = m * 2 then 0 else 2 * (m * 2 - w)) (m + j - (m * 2 - w)) =
      ((upGate (if w = m then 0 else 2 * (m - w)) (j - (m - w))).1,
        (upGate (if w = m then 0 else 2 * (m - w)) (j - (m - w))).2.map (fun i => m * 2 + i))
    rw [ite_eq_right (by omega : w ≠ m * 2), show m + j - (m * 2 - w) = j - (m - w) by omega]
    have hb : 2 * (m * 2 - w) = m * 2 + (if w = m then 0 else 2 * (m - w)) := by
      split <;> omega
    rw [hb]
    simp [upGate, Nat.add_assoc]
  · have hup' : ¬ m + j < m * 2 - 1 := by omega
    rw [gateCode, ite_eq_right hup', gateCode, ite_eq_right hup]
    by_cases he : j = m - 1
    · rw [ite_eq_left he, ite_eq_left (by omega : m + j = m * 2 - 1)]
      rfl
    · have hx : m + j - m * 2 + 2 = j - m + 2 := by omega
      rw [ite_eq_right he, ite_eq_right (by omega : m + j ≠ m * 2 - 1), hx]
      let w := BlockSummary.paddedCount ((j - m + 2) / 2 + 1)
      have hw : w ≤ m := padded_le_pow (by change (j - m + 2) / 2 + 1 ≤ m; omega)
      change downGate (if w = m * 2 then 0 else 2 * (m * 2 - w))
          (2 * (m * 2) + w / 2 - 2) (m + j - (m * 2 + w - 2)) =
        ((downGate (if w = m then 0 else 2 * (m - w)) (2 * m + w / 2 - 2) (j - (m + w - 2))).1,
          (downGate (if w = m then 0 else 2 * (m - w)) (2 * m + w / 2 - 2) (j - (m + w - 2))).2.map
            (fun i => m * 2 + i))
      rw [ite_eq_right (by omega : w ≠ m * 2),
        show m + j - (m * 2 + w - 2) = j - (m + w - 2) by omega]
      have hb : 2 * (m * 2 - w) = m * 2 + (if w = m then 0 else 2 * (m - w)) := by
        split <;> omega
      rw [hb, show 2 * (m * 2) + w / 2 - 2 = m * 2 + (2 * m + w / 2 - 2) by omega]
      unfold downGate
      split <;> simp [Nat.add_assoc]

private theorem gateCode_last (d j : ℕ) (hj : j < 2 ^ d * 2) :
    gateCode (2 ^ d * 2) (2 ^ d + (3 * 2 ^ d - 2) + j) =
      downGate 0 (2 ^ d * 2 + (3 * 2 ^ d - 2)) j := by
  let m := 2 ^ d
  have hm : 0 < m := Nat.two_pow_pos d
  change j < m * 2 at hj
  change gateCode (m * 2) (m + (3 * m - 2) + j) = downGate 0 (m * 2 + (3 * m - 2)) j
  rw [gateCode, ite_eq_right (by omega), ite_eq_right (by omega)]
  have hx : m + (3 * m - 2) + j - m * 2 + 2 = m * 2 + j := by omega
  rw [hx]
  have hw : BlockSummary.paddedCount ((m * 2 + j) / 2 + 1) = m * 2 := by
    change BlockSummary.paddedCount ((2 ^ d * 2 + j) / 2 + 1) = _
    rw [← pow_succ]
    exact padded_eq_pow (by omega) (by rw [pow_succ]; omega)
  rw [hw]
  dsimp only
  rw [ite_eq_left rfl]
  congr 1 <;> omega

private def beforeExpand (m : ℕ) : RawCode :=
  ((List.range m).map (upGate 0) ++ (List.range (3 * m - 2)).map (fun j =>
      ((gateCode m j).1, (gateCode m j).2.map (fun i => m * 2 + i))),
    (List.range m).map (fun i => m * 2 + (3 * m - 2) + i) ++ List.range (m * 2))

set_option backward.isDefEq.respectTransparency false in
private theorem beforeExpand_code (d : ℕ) (ih : (scanPow d).code = powCode (2 ^ d)) :
    (((scanPow d).comp (summarize (2 ^ d))).append (Circuit.id signature (2 ^ d * 2))).code =
      beforeExpand (2 ^ d) := by
  rw [← appendCode_code, ← compCode_code, summarize_code, ih, Circuit.id, Circuit.code_wiring_id]
  let m := 2 ^ d
  let summary : RawCode :=
    ((List.range m).map (upGate 0), (List.range m).map (fun i => m * 2 + i))
  have hw (i : ℕ) : compCodeWire (m * 2) summary i = m * 2 + i := by
    by_cases hi : i < m
    · simp [summary, compCodeWire, List.getD_eq_getElem?_getD, hi]
    · simp only [summary, compCodeWire, List.length_map, List.length_range, ite_eq_right hi]
      omega
  change appendCode (m * 2) (compCode (m * 2) (powCode m) summary) ([], List.range (m * 2)) = _
  have hshift (l : ℕ) : (List.range (m * 2)).map (shiftCodeWire (m * 2) l) = List.range (m * 2) := by
    calc
      _ = (List.range (m * 2)).map id := by
        apply List.map_congr_left
        intro i hi
        simp [shiftCodeWire, List.mem_range.mp hi]
      _ = _ := List.map_id _
  rw [appendCode, compCode, funext hw]
  simp [summary, powCode, beforeExpand, hshift, List.map_map, Function.comp_def, Nat.add_assoc]
  exact ⟨rfl, rfl⟩

private theorem beforeExpand_prefixWire {m i : ℕ} (hi : i < m) :
    compCodeWire (m * 2) (beforeExpand m) i = m * 2 + (3 * m - 2) + i := by
  simp [compCodeWire, beforeExpand, List.getD_eq_getElem?_getD, hi,
    show i < m + m * 2 by omega]

private theorem beforeExpand_inputWire {m i : ℕ} (hi : i < m * 2) :
    compCodeWire (m * 2) (beforeExpand m) (m + i) = i := by
  simp [compCodeWire, beforeExpand, List.getD_eq_getElem?_getD,
    show m + i < m + m * 2 by omega]

private theorem beforeExpand_gateWire (m i : ℕ) :
    compCodeWire (m * 2) (beforeExpand m) (m + m * 2 + i) =
      3 * (m * 2) - 2 + i := by
  simp only [compCodeWire, beforeExpand, List.length_append, List.length_map, List.length_range,
    ite_eq_right (by omega : ¬m + m * 2 + i < m + m * 2)]
  omega

private theorem beforeExpand_downGate {m i : ℕ} (hi : i < m * 2) :
    ((downGate m 0 i).1, (downGate m 0 i).2.map (compCodeWire (m * 2) (beforeExpand m))) =
      downGate 0 (m * 2 + (3 * m - 2)) i := by
  have hp : i / 2 < m := by omega
  have hq : 2 * (i / 2) < m * 2 := by omega
  by_cases he : i % 2 = 0 <;>
    simp [downGate, he, beforeExpand_prefixWire hp, beforeExpand_inputWire hq]

set_option backward.isDefEq.respectTransparency false in
private theorem scanPow_code (d : ℕ) : (scanPow d).code = powCode (2 ^ d) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [scanPow, ← compCode_code, expand_code, beforeExpand_code d ih, pow_succ]
    let m := 2 ^ d
    have hm : 0 < m := Nat.two_pow_pos d
    change compCode (m * 2)
      ((List.range (m * 2)).map (downGate m 0),
        (List.range (m * 2)).map (fun i => m + m * 2 + i))
      (beforeExpand m) = powCode (m * 2)
    apply Prod.ext
    · simp only [compCode, beforeExpand, powCode, List.map_map, Function.comp_def, List.append_assoc]
      rw [show 3 * (m * 2) - 2 = m + (3 * m - 2) + m * 2 by omega, List.range_add,
        List.range_add, List.map_append, List.map_append, List.map_map, List.map_map]
      simp only [Function.comp_def]
      have hs : (List.range m).map (gateCode (m * 2)) = (List.range m).map (upGate 0) := by
        apply List.map_congr_left
        intro j hj
        exact gateCode_first d j (List.mem_range.mp hj)
      have hc : (List.range (3 * m - 2)).map (fun j => gateCode (m * 2) (m + j)) =
          (List.range (3 * m - 2)).map (fun j =>
            ((gateCode m j).1, (gateCode m j).2.map (fun i => m * 2 + i))) := by
        apply List.map_congr_left
        intro j hj
        exact gateCode_shift d j (List.mem_range.mp hj)
      rw [hs, hc, List.append_assoc]
      congr 1
      congr 1
      apply List.map_congr_left
      intro j hj
      exact (beforeExpand_downGate (List.mem_range.mp hj)).trans
        (gateCode_last d j (List.mem_range.mp hj)).symm
    · simp [compCode, powCode, List.map_map, Function.comp_def, beforeExpand_gateWire]

private abbrev encPairUnary := encPair encUnary encUnary

private theorem twoRefs_logspace {f g : ℕ × ℕ → ℕ}
    (hf : ComputableInLogSpace f encPairUnary encUnary)
    (hg : ComputableInLogSpace g encPairUnary encUnary) (op : Op) :
    ComputableInLogSpace (fun a => (op, [f a, g a])) encPairUnary encGate :=
  (ComputableInLogSpace.const (encMid := encOp) op).pair
    (hf.unaryToBinary.listCons (ComputableInLogSpace.listSingleton.comp hg.unaryToBinary))

private theorem levelBase_logspace {w P : ℕ × ℕ → ℕ}
    (hw : ComputableInLogSpace w encPairUnary encUnary)
    (hP : ComputableInLogSpace P encPairUnary encUnary) :
    ComputableInLogSpace (fun a => if w a = P a then 0 else 2 * (P a - w a))
      encPairUnary encUnary := by
  exact ((hw.unaryEq hP).ite (ComputableInLogSpace.const 0)
    ((hP.unarySub hw).unaryMulConst 2)).congr_fun
      (fun a => by simp [Nat.mul_comm])

set_option maxHeartbeats 1000000 in
private theorem gateCode_logspace :
    ComputableInLogSpace (fun a : ℕ × ℕ => gateCode a.1 a.2) encPairUnary encGate := by
  let c (n : ℕ) : ComputableInLogSpace (fun _ : ℕ × ℕ => n) encPairUnary encUnary :=
    ComputableInLogSpace.const n
  have hp := ComputableInLogSpace.fst encUnary encUnary
  have hg := ComputableInLogSpace.snd encUnary encUnary
  have huw := BlockSummary.paddedCount_logspace.comp (hp.unarySub hg)
  have hui := hg.unarySub (hp.unarySub huw)
  have hua := (levelBase_logspace huw hp).unaryAdd (hui.unaryMulConst 2)
  have hu := twoRefs_logspace hua (hua.unaryAdd (c 1)) .or
  have hdw := BlockSummary.paddedCount_logspace.comp
    (((hg.unarySub hp).unaryAdd (c 2)).unaryDiv (c 2) |>.unaryAdd (c 1))
  have hdi := hg.unarySub ((hp.unaryAdd hdw).unarySub (c 2))
  have hq := hdi.unaryDiv (c 2)
  have hdp := (((hp.unaryMulConst 2).unaryAdd (hdw.unaryDiv (c 2))).unarySub (c 2)).unaryAdd hq
  have hda := (levelBase_logspace hdw hp).unaryAdd (hq.unaryMulConst 2)
  have hd := ((hdi.unaryMod (c 2)).unaryEq (c 0)).ite
    (twoRefs_logspace hdp hdp .and) (twoRefs_logspace hdp hda .or)
  have ht := hp.unarySub (c 1)
  exact ((hg.unaryLt ht).ite hu
    ((hg.unaryEq ht).ite (ComputableInLogSpace.const (Op.const false, [])) hd)).congr_fun
      (fun a => by simp [gateCode, upGate, downGate, Nat.mul_comm])

private theorem powCode_logspace : ComputableInLogSpace powCode encUnary encCode := by
  have hid : ComputableInLogSpace (fun n : ℕ => n) encUnary encUnary := ComputableInLogSpace.id
  have hg : ComputableInLogSpace (fun n : ℕ => 3 * n - 2) encUnary encUnary :=
    ((hid.unaryMulConst 3).unarySub (ComputableInLogSpace.const 2)).congr_fun
      (fun n => by simp [Nat.mul_comm])
  have hp := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  exact (map_range hg gateCode_logspace).pair
    (map_range hid (((hg.comp hp).unaryAdd hj).unaryToBinary))

private theorem pad_code_logspace :
    ComputableInLogSpace (fun m => (pad m).code) encUnary encCode := by
  have hp := BlockSummary.paddedCount_logspace
  have hx := ComputableInLogSpace.fst encUnary encUnary
  have hj := ComputableInLogSpace.snd encUnary encUnary
  have hwire : ComputableInLogSpace (fun p : ℕ × ℕ => (([], [p.2]) : RawCode))
      encPairUnary encCode :=
    (ComputableInLogSpace.const []).pair (ComputableInLogSpace.listSingleton.comp hj.unaryToBinary)
  have hconst : ComputableInLogSpace (fun p : ℕ × ℕ => (constBit p.1 false).code)
      encPairUnary encCode :=
    ((ComputableInLogSpace.const [(Op.const false, [])]).pair
      (ComputableInLogSpace.listSingleton.comp hx.unaryToBinary)).congr_fun (fun _ => rfl)
  unfold pad
  apply circuit_pi_of_indexed_logspace ComputableInLogSpace.id hp
  exact ((hj.unaryLt (hp.comp hx)).ite ((hj.unaryLt hx).ite hwire hconst)
    (ComputableInLogSpace.const ([], []))).congr_fun (fun p => by
      simp only [Function.comp_apply, decide_eq_true_eq]
      split_ifs <;> rfl)

/-- The actual linear-size prefix circuit is generated by a logspace transducer. -/
theorem scan_code_logspace :
    ComputableInLogSpace (fun m => (scan m).code) encUnary encCode := by
  have hid : ComputableInLogSpace (fun m : ℕ => m) encUnary encUnary := ComputableInLogSpace.id
  have hp := BlockSummary.paddedCount_logspace
  have hpow : ComputableInLogSpace
      (fun m => (scanPow (BlockSummary.paddingDepth m)).code) encUnary encCode :=
    (powCode_logspace.comp hp).congr_fun (fun m => scanPow_code (BlockSummary.paddingDepth m))
  have hcut : ComputableInLogSpace (fun m => (Circuit.wiring signature
      (Fin.castLE (show m ≤ 2 ^ BlockSummary.paddingDepth m from BlockSummary.le_paddedCount m))).code)
      encUnary encCode := by
    refine ((ComputableInLogSpace.const ([] : List (Op × List ℕ))).pair
      (map_range hid (ComputableInLogSpace.snd encUnary encUnary).unaryToBinary)).congr_fun ?_
    intro m
    exact Circuit.code_wiring_eq_map (fun _ => rfl)
  exact circuit_comp_logspace hid (circuit_comp_logspace hid pad_code_logspace hpow) hcut

end PredictionDepth.SparseCorrections.Prefix
