import PredictionDepth.FrozenPascal.CoefficientBits
import PredictionDepth.Complexity.LogspaceBatch
import PredictionDepth.Complexity.CodeLogspace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit

/-!
# Native uniform computation of the coefficient table

The table is computed from Lucas digit implications, never by constructing a
large binomial coefficient. Two interfaces are provided: genuine logarithmic
space from unary-index generators, and linear space in short binary metadata.
The latter is the local routine needed by a logspace circuit writer when the
metadata numbers are polynomially bounded in its input length.
-/

namespace PredictionDepth.FrozenPascal

open Turing.MultiTapeTM
open PredictionDepth.StandardComplexity

section Logspace
variable {α : Type} {enc : α ↪ List Bool} {n k i u s : α → ℕ}

theorem testBit_logspace
    (hn : ComputableInLogSpace n enc encUnary) (hi : ComputableInLogSpace i enc encUnary) :
    ComputableInLogSpace (fun a => (n a).testBit (i a)) enc encBool := by
  have hb : ComputableInLogSpace (fun a => (n a).bits) enc encBits :=
    hn.unaryToBinary.congr fun _ => rfl
  have h := (ComputableInLogSpace.bitsHeadD false).comp (hb.bitsDrop' hi)
  exact h.congr_fun fun a => by
    simp only [Function.comp_def, Nat.testBit_eq_inth, List.getI_eq_getElem?_getD,
      List.headD_eq_head?_getD, List.head?_drop]
    rfl

theorem chooseParity_logspace
    (hn : ComputableInLogSpace n enc encUnary) (hk : ComputableInLogSpace k enc encUnary) :
    ComputableInLogSpace (fun a => chooseParity (n a) (k a)) enc encBool := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hnb := testBit_logspace (hn.comp hp) hi
  have hkb := testBit_logspace (hk.comp hp) hi
  have hbit := hkb.bool_not.bool_or hnb
  have hword : ComputableInLogSpace
      (fun p : α × ℕ => [!(k p.1).testBit p.2 || (n p.1).testBit p.2])
      (encPair enc encUnary) encBits := hbit.congr fun _ => rfl
  have hcount := (hn.unaryMax hk).unaryAdd (ComputableInLogSpace.const 1)
  have hwords := LogspaceBatch.flatMap_range hcount hword
  have h := (ComputableInLogSpace.bitsAll id).comp hwords
  exact h.congr_fun fun a => by
    simp only [chooseParity, ← List.map_eq_flatMap, List.all_map, Function.comp_def, id_eq]

/-- Actual logspace coefficient lookup whenever its three indices are supplied
in unary by native logspace machines. -/
theorem tableBit_logspace
    (hu : ComputableInLogSpace u enc encUnary) (hk : ComputableInLogSpace k enc encUnary)
    (hs : ComputableInLogSpace s enc encUnary) :
    ComputableInLogSpace (fun a => tableBit (u a) (k a) (s a)) enc encBool := by
  have hd := hu.unarySub hk
  have htop := (hs.unaryAdd hd).unarySub (ComputableInLogSpace.const 1)
  have hc := chooseParity_logspace htop hd
  have h := (hk.unaryLe hu).ite hc (ComputableInLogSpace.const false)
  exact h.congr_fun fun a => by
    rw [← directTableBit_eq]
    simp only [directTableBit, decide_eq_true_eq]

end Logspace

namespace CoefficientSpace

open ComputableInSpace

abbrev State := (ℕ × ℕ) × (ℕ × Bool)
abbrev encState : State ↪ List Bool := encPair (encPair encNat encNat) (encPair encNat encBool)
abbrev encInput : (ℕ × ℕ) ↪ List Bool := encPair encNat encNat

def init (p : ℕ × ℕ) : State := (p, 0, true)
def advance (p : State) : State :=
  (p.1, p.2.1 + 1, p.2.2 && (!p.1.2.testBit p.2.1 || p.1.1.testBit p.2.1))

theorem advance_iterate (n k t : ℕ) :
    advance^[t] (init (n, k)) =
      ((n, k), t, (List.range t).all (fun i => !k.testBit i || n.testBit i)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [advance, List.range_succ]

theorem index_length_bound (n k i : ℕ) (hi : i ≤ max n k + 1) :
    (encNat i).length ≤ (encNat n).length + (encNat k).length + 1 := by
  have hn : n < 2 ^ (n.size + k.size) :=
    (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have hk : k < 2 ^ (n.size + k.size) :=
    (Nat.lt_size_self k).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  have hmax := max_lt hn hk
  have hp : 2 ^ (n.size + k.size) < 2 ^ (n.size + k.size + 1) :=
    Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  rw [encNat_apply, encNat_apply, encNat_apply, Nat.size_eq_bits_len, Nat.size_eq_bits_len,
    Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  exact (hi.trans (Nat.succ_le_of_lt hmax)).trans_lt hp

theorem state_length (n k t : ℕ) (ht : t ≤ max n k + 1) :
    (encState (advance^[t] (init (n, k)))).length ≤ 4 * (encInput (n, k)).length + 3 := by
  rw [advance_iterate]
  have h := index_length_bound n k t ht
  simp only [encState, encInput, length_encPair, encBool_apply, List.length_singleton]
  omega

theorem testBit_linear : ComputableInSpace (fun p : ℕ × ℕ => p.1.testBit p.2)
    encInput encBool (fun p => (encInput p).length) :=
  natTestBit.weaken (.of_le_linear 32 32 (fun p => by dsimp only [encInput]; omega))

theorem advance_inSpace : ComputableInSpace advance encState encState
    (fun p => (encState p).length) := by
  have hvals := ComputableInSpace.fst encInput (encPair encNat encBool)
  have hcur := ComputableInSpace.snd encInput (encPair encNat encBool)
  have hn := hvals.fst'
  have hk := hvals.snd'
  have hi := hcur.fst'
  have ha := hcur.snd'
  have hnb := budget_comp_linear testBit_linear (budget_prod hn hi)
  have hkb := budget_comp_linear testBit_linear (budget_prod hk hi)
  have himp := budget_finite (encC := encBool) (fun p : Bool × Bool => !p.1 || p.2)
    (budget_prod hkb hnb)
  have hacc := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod ha himp)
  exact budget_prod hvals (budget_prod (budget_natSucc hi) hacc)

/-- The bit loop uses space linear in the encoded binary inputs. Its loop
count is binary too; no list of all digits or large binomial is retained. -/
theorem chooseParity_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => chooseParity p.1 p.2) encInput encBool
      (fun p => (encInput p).length) := by
  have hn := ComputableInSpace.fst encNat encNat
  have hk := ComputableInSpace.snd encNat encNat
  have hmax : ComputableInSpace (fun p : ℕ × ℕ => max p.1 p.2) encInput encNat
      (fun p => (encInput p).length) := by
    refine (budget_ite (budget_natLt hn hk) hk hn).of_enc_eq ?_
    intro p
    by_cases h : p.1 < p.2
    · simp [h, max_eq_right h.le]
    · simp [h, max_eq_left (Nat.le_of_not_gt h)]
  have hcount := budget_natSucc hmax
  have hid : ComputableInSpace (id : ℕ × ℕ → ℕ × ℕ) encInput encInput
      (fun p => (encInput p).length) := of_inO ComputableInDegree.id'.inO_one
  have hi := budget_prod hid (budget_prod
    (budget_const (encB := encNat) 0 (.refl _)) (budget_const (encB := encBool) true (.refl _)))
  have h := budget_iterate (init := init) (step := advance)
    (B := fun p => 4 * (encInput p).length + 3) hcount hi advance_inSpace
    (fun p t ht => state_length p.1 p.2 t ht) (.of_le_linear 4 3 (fun _ => le_rfl))
  exact h.snd'.snd'.of_enc_eq fun p => by rw [advance_iterate]; rfl

end CoefficientSpace

section SpaceBudget

open ComputableInSpace
variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {u k s : α → ℕ}

/-- Binary local-metadata interface for circuit serializers. If the argument
routines use budget `S`, so does the complete coefficient computation. -/
theorem tableBit_budget
    (hu : ComputableInSpace u enc encNat S) (hk : ComputableInSpace k enc encNat S)
    (hs : ComputableInSpace s enc encNat S) (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => tableBit (u a) (k a) (s a)) enc encBool S := by
  have hd := budget_natSub hu hk
  have hn := budget_natPred (budget_natAdd hs hd)
  have hc := budget_comp_linear CoefficientSpace.chooseParity_inSpace (budget_prod hn hd)
  have hguard := budget_finite (encC := encBool) Bool.not (budget_natLt hu hk)
  refine (budget_ite hguard hc (budget_const false hin)).of_enc_eq ?_
  intro a
  rw [← directTableBit_eq]
  by_cases h : k a ≤ u a
  · simp [directTableBit, h, Nat.not_lt.mpr h]
  · simp [directTableBit, h, Nat.lt_of_not_ge h]

end SpaceBudget

abbrev coefficientEncoding : (ℕ × ℕ × ℕ) ↪ List Bool :=
  encPair encNat (encPair encNat encNat)

/-- A ready-to-use short-binary-metadata routine. Its space is linear in the
metadata bit length; a circuit writer uses logarithmically many such bits. -/
theorem tableBit_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ × ℕ => tableBit p.1 p.2.1 p.2.2)
      coefficientEncoding encBool (fun p => (coefficientEncoding p).length) := by
  have hu := ComputableInSpace.fst encNat (encPair encNat encNat)
  have hrest := ComputableInSpace.snd encNat (encPair encNat encNat)
  exact tableBit_budget hu hrest.fst' hrest.snd' (.refl _)

end PredictionDepth.FrozenPascal
