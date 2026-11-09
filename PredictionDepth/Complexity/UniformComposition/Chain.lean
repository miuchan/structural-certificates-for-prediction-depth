import PredictionDepth.Complexity.CodeLogspaceFamilies
import PredictionDepth.Complexity.RegularCompositionCode

/-!
# Streaming a sequential chain with consecutive outputs

Every intermediate output is an actual last gate, so its global wire number
is determined by a prior gate count. These counts are obtained by streaming
the earlier templates. The complete growing prior circuit is never stored.
-/

namespace PredictionDepth.StandardComplexity.UniformComposition

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM CodeLogspace CodeLogspaceFamilies RegularCompositionCode

/-- Outputs are the last `W` gates, in order. The gate-count inequality rules
out underflow even when there are no primary inputs. -/
def Consecutive (n W : ℕ) (c : RawCode) : Prop :=
  W ≤ c.1.length ∧ c.2 = (List.range W).map (fun j => n + c.1.length - W + j)

def sequentialCodes (n : ℕ) (initial : RawCode) (codes : List RawCode) : RawCode :=
  codes.foldl (fun prior code => compCode n code prior) initial

theorem sequentialCodes_snoc (n : ℕ) (initial : RawCode) (codes : List RawCode) (c : RawCode) :
    sequentialCodes n initial (codes ++ [c]) = compCode n c (sequentialCodes n initial codes) := by
  simp [sequentialCodes]

theorem sequentialCodes_length (n : ℕ) (initial : RawCode) (codes : List RawCode) :
    (sequentialCodes n initial codes).1.length = initial.1.length + (codes.flatMap Prod.fst).length := by
  induction codes using List.reverseRecOn with
  | nil => rfl
  | append_singleton codes c ih =>
    simp [sequentialCodes_snoc, compCode, ih, Nat.add_assoc]

theorem compCode_consecutive (n W : ℕ) (prior later : RawCode)
    (hp : Consecutive n W prior) :
    compCode n later prior =
      (prior.1 ++ later.1.map (shiftGate (n + prior.1.length - W)),
        later.2.map (fun j => n + prior.1.length - W + j)) := by
  rcases prior with ⟨gs, outs⟩
  obtain ⟨hlen, hout⟩ := hp
  change W ≤ gs.length at hlen
  change outs = _ at hout
  simp only [hout]
  exact compCode_affine n W (n + gs.length - W) gs (by omega) later

theorem Consecutive.comp {n W : ℕ} {prior later : RawCode}
    (hp : Consecutive n W prior) (hc : Consecutive W W later) :
    Consecutive n W (compCode n later prior) := by
  rw [compCode_consecutive n W prior later hp]
  constructor
  · simpa only [List.length_append, List.length_map] using hp.1.trans (Nat.le_add_right _ _)
  · simp only [hc.2, List.map_map, Function.comp_def, List.length_append, List.length_map]
    apply List.map_congr_left
    intro j _
    have := hp.1
    omega

theorem sequentialCodes_consecutive (n W : ℕ) (initial : RawCode) (codes : List RawCode)
    (hi : Consecutive n W initial) (hc : ∀ c ∈ codes, Consecutive W W c) :
    Consecutive n W (sequentialCodes n initial codes) := by
  induction codes using List.reverseRecOn with
  | nil => exact hi
  | append_singleton codes c ih =>
    rw [sequentialCodes_snoc]
    apply Consecutive.comp (ih (fun q hq => hc q (List.mem_append_left _ hq)))
    exact hc c (by simp)

def prefixBase (n W : ℕ) (initial : RawCode) (codes : List RawCode) (j : ℕ) : ℕ :=
  n + initial.1.length + ((codes.take j).flatMap Prod.fst).length - W

def directChainCodes (n W : ℕ) (initial : RawCode) (codes : List RawCode) : RawCode :=
  (initial.1 ++ (List.range codes.length).flatMap (fun j =>
      (codes.getD j ([], [])).1.map (shiftGate (prefixBase n W initial codes j))),
    (List.range W).map (fun j => n + initial.1.length + (codes.flatMap Prod.fst).length - W + j))

theorem directChainCodes_gates_snoc (n W : ℕ) (initial : RawCode)
    (codes : List RawCode) (c : RawCode) :
    (directChainCodes n W initial (codes ++ [c])).1 =
      (directChainCodes n W initial codes).1 ++
        c.1.map (shiftGate (n + initial.1.length + (codes.flatMap Prod.fst).length - W)) := by
  have hpre (j : ℕ) (hj : j < codes.length) :
      prefixBase n W initial (codes ++ [c]) j = prefixBase n W initial codes j := by
    rw [prefixBase, prefixBase, List.take_append_of_le_length hj.le]
  have hget (j : ℕ) (hj : j < codes.length) :
      (codes ++ [c]).getD j ([], []) = codes.getD j ([], []) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hj]
  have hlast : (codes ++ [c]).getD codes.length ([], []) = c := by
    simp [List.getD_eq_getElem?_getD]
  simp only [directChainCodes, List.length_append, List.length_singleton, List.range_succ,
    List.flatMap_append, List.flatMap_singleton, hlast, prefixBase, List.take_left,
    List.append_assoc]
  congr 1
  congr 1
  apply List.flatMap_congr
  intro j hj
  rw [hget j (List.mem_range.mp hj), List.take_append_of_le_length (List.mem_range.mp hj).le]

theorem directChainCodes_eq (n W : ℕ) (initial : RawCode) (codes : List RawCode)
    (hi : Consecutive n W initial) (hc : ∀ c ∈ codes, Consecutive W W c) :
    directChainCodes n W initial codes = sequentialCodes n initial codes := by
  induction codes using List.reverseRecOn with
  | nil =>
    apply Prod.ext
    · simp [directChainCodes, sequentialCodes]
    · simpa [directChainCodes, sequentialCodes] using hi.2.symm
  | append_singleton codes c ih =>
    have hcs : ∀ q ∈ codes, Consecutive W W q := fun q hq => hc q (List.mem_append_left _ hq)
    have hlast := hc c (by simp)
    have hprev := sequentialCodes_consecutive n W initial codes hi hcs
    have hind := ih hcs
    rw [sequentialCodes_snoc, compCode_consecutive n W _ c hprev]
    apply Prod.ext
    · rw [directChainCodes_gates_snoc, hind, sequentialCodes_length]
      simp only [Nat.add_assoc]
    · simp only [directChainCodes, hlast.2, List.map_map, Function.comp_def,
        List.flatMap_append, List.flatMap_singleton, List.length_append, sequentialCodes_length]
      apply List.map_congr_left
      intro j _
      have := hi.1
      omega

section Generator
variable {α : Type} {enc : α ↪ List Bool}
  {n W : α → ℕ} {initial : α → RawCode} {codes : α → List RawCode}

/-- Native stream generation for the affine chain normal form. Each template
reference is bounded by its input width and its own gate count. -/
theorem directChainCodes_logspace
    (hn : ComputableInLogSpace n enc encUnary) (hW : ComputableInLogSpace W enc encUnary)
    (hi : ComputableInLogSpace initial enc encCode)
    (hc : ComputableInLogSpace codes enc (encList encCode))
    (hbound : ∀ a c, c ∈ codes a → BoundedReferences (W a + c.1.length) c) :
    ComputableInLogSpace (fun a => directChainCodes (n a) (W a) (initial a) (codes a))
      enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hj := ComputableInLogSpace.snd enc encUnary
  have hblock := getD ([], []) (hc.comp hp) hj
  have hpre := CodeLogspaceFamilies.take ([], []) (hc.comp hp) hj
  have hpreGates := flatMapWithInput ([], []) hpre
    (ComputableInLogSpace.snd (encPair enc encUnary) encCode).fst'
  have hpreLen := ComputableInLogSpace.listLength.comp hpreGates
  have hinitLen := ComputableInLogSpace.listLength.comp hi.fst'
  have hbase := (((hn.unaryAdd hinitLen).comp hp).unaryAdd hpreLen).unarySub (hW.comp hp)
  have hB := (hW.comp hp).unaryAdd (ComputableInLogSpace.listLength.comp hblock.fst')
  have hb (p : α × ℕ) : BoundedReferences
      (W p.1 + ((codes p.1).getD p.2 ([], [])).1.length) ((codes p.1).getD p.2 ([], [])) :=
    getD_property (hbound p.1) (by simp [BoundedReferences]) p.2
  have hpar := ComputableInLogSpace.fst (encPair enc encUnary) encUnary
  have hix := ComputableInLogSpace.snd (encPair enc encUnary) encUnary
  have hw := ((hbase.comp hpar).unaryAdd hix).unaryToBinary
  have hshift := mapCode_logspace hblock hB hb hw
  have hcount := ComputableInLogSpace.listLength.comp hc
  have hgates := flatMap_range_list hcount hshift.fst'
  have hall := flatMapWithInput ([], []) hc (ComputableInLogSpace.snd enc encCode).fst'
  have hlastBase := ((hn.unaryAdd hinitLen).unaryAdd
    (ComputableInLogSpace.listLength.comp hall)).unarySub hW
  have houts := map_range hW (((hlastBase.comp hp).unaryAdd hj).unaryToBinary)
  exact (hi.fst'.listAppend hgates).pair houts

/-- Uniformity of the actual sequential composition follows from the local
normalization contracts, not from a uniformity premise for the entire chain. -/
theorem sequentialCodes_logspace
    (hn : ComputableInLogSpace n enc encUnary) (hW : ComputableInLogSpace W enc encUnary)
    (hi : ComputableInLogSpace initial enc encCode)
    (hc : ComputableInLogSpace codes enc (encList encCode))
    (hinit : ∀ a, Consecutive (n a) (W a) (initial a))
    (hsteps : ∀ a c, c ∈ codes a → Consecutive (W a) (W a) c)
    (hbound : ∀ a c, c ∈ codes a → BoundedReferences (W a + c.1.length) c) :
    ComputableInLogSpace (fun a => sequentialCodes (n a) (initial a) (codes a)) enc encCode :=
  (directChainCodes_logspace hn hW hi hc hbound).congr_fun
    (fun a => (directChainCodes_eq (n a) (W a) (initial a) (codes a) (hinit a) (hsteps a)).symm)

end Generator
end PredictionDepth.StandardComplexity.UniformComposition
