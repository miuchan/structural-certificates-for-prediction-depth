import PredictionDepth.CompiledComposition
import CslibFrontier.Foundations.Data.List.BalancedFold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn

/-!
# Ordered block summaries

A fixed-width summary reduces a list of leaf values in their original order.
The circuit compiler can change the parenthesization. Finite local checks
suffice for a supplied finite right-to-left evaluator and summary map. Failure
of the checks means the supplied certificate has not been established.

The last section gives a separate obstruction for summaries of one side of a
fixed cut. Its bit-width bound concerns that interface.
-/

namespace PredictionDepth.BlockSummary

open FastComposition (Bits)

variable {w : ℕ} {merge : Bits w → Bits w → Bits w} {empty : Bits w}

/-- The algebraic laws needed for an ordered reduction, including empty blocks. -/
structure Laws (merge : Bits w → Bits w → Bits w) (empty : Bits w) : Prop where
  assoc : ∀ a b c, merge (merge a b) c = merge a (merge b c)
  leftId : ∀ a, merge empty a = a
  rightId : ∀ a, merge a empty = a

/-- The semantic fold preserves the original order of the blocks. -/
def summarize (merge : Bits w → Bits w → Bits w) (empty : Bits w)
    (leaves : List (Bits w)) : Bits w :=
  leaves.foldr merge empty

theorem summarize_append (laws : Laws merge empty) (left right : List (Bits w)) :
    summarize merge empty (left ++ right) =
      merge (summarize merge empty left) (summarize merge empty right) := by
  induction left with
  | nil => simp [summarize, laws.leftId]
  | cons a left ih =>
    simp only [summarize, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, laws.assoc]

theorem balancedFold_eq_summarize (laws : Laws merge empty) (leaves : List (Bits w)) :
    leaves.balancedFold merge empty id = summarize merge empty leaves := by
  let : Std.Associative merge := ⟨laws.assoc⟩
  let : Std.LawfulIdentity merge empty :=
    { left_id := laws.leftId, right_id := laws.rightId }
  simpa [summarize] using List.balancedFold_eq_foldr (op := merge) (e := empty) (f := id) leaves

/-- Adjacent pair reduction preserves the ordered summary of a bank. -/
theorem summarize_pair_bank (laws : Laws merge empty) (v : Fin (m * 2) → Bits w) :
    summarize merge empty (List.ofFn (fun j : Fin m =>
      merge (v ⟨2 * j.val, by omega⟩) (v ⟨2 * j.val + 1, by omega⟩))) =
      summarize merge empty (List.ofFn v) := by
  have flatten (xs : List (List (Bits w))) :
      summarize merge empty xs.flatten =
        summarize merge empty (xs.map (summarize merge empty)) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change summarize merge empty (x ++ xs.flatten) =
        merge (summarize merge empty x) (summarize merge empty (xs.map (summarize merge empty)))
      rw [summarize_append laws, ih]
  rw [List.ofFn_mul v, flatten, List.map_ofFn]
  apply congrArg (summarize merge empty)
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply, List.ofFn_succ, List.ofFn_zero, summarize, List.foldr_cons,
    List.foldr_nil, laws.rightId]
  congr 1 <;> apply congrArg v <;> apply Fin.ext <;> simp <;> omega

/-- Padding the end of a bank with empty summaries does not change its value. -/
theorem summarize_pad (laws : Laws merge empty) (v : Fin m → Bits w) (pad : ℕ) :
    summarize merge empty (List.ofFn (Fin.addCases v (fun _ : Fin pad => empty))) =
      summarize merge empty (List.ofFn v) := by
  change summarize merge empty (List.ofFn (Fin.append v (fun _ : Fin pad => empty))) = _
  rw [List.ofFn_fin_append, summarize_append laws]
  have h (k : ℕ) : summarize merge empty (List.ofFn fun _ : Fin k => empty) = empty := by
    induction k with
    | zero => rfl
    | succ k ih => rw [List.ofFn_succ]; exact (congrArg (merge empty) ih).trans (laws.leftId empty)
  rw [h, laws.rightId]

theorem summarize_pad_le (laws : Laws merge empty) (v : Fin m → Bits w) (h : m ≤ n) :
    summarize merge empty (List.ofFn (fun j : Fin n =>
      if hj : j.val < m then v ⟨j.val, hj⟩ else empty)) =
      summarize merge empty (List.ofFn v) := by
  obtain ⟨pad, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← summarize_pad laws v pad]
  apply congrArg (summarize merge empty)
  apply congrArg List.ofFn
  funext j
  refine Fin.addCases (motive := fun j => (if hj : j.val < m then v ⟨j.val, hj⟩ else empty) =
    Fin.addCases v (fun _ : Fin pad => empty) j) ?_ ?_ j
  · intro i
    simp [i.isLt]
  · intro i
    simp [show ¬ m + i.val < m by omega]

/-- A block specification that respects empty blocks, leaves, and concatenation
is evaluated by the same ordered reduction for every list length. -/
theorem summarize_map_eq {α : Type*} (laws : Laws merge empty) (leaf : α → Bits w)
    (spec : List α → Bits w) (hEmpty : spec [] = empty)
    (hLeaf : ∀ a, spec [a] = leaf a)
    (hAppend : ∀ l r, spec (l ++ r) = merge (spec l) (spec r)) (l : List α) :
    summarize merge empty (l.map leaf) = spec l := by
  induction l with
  | nil => exact hEmpty.symm
  | cons a l ih =>
    rw [show a :: l = [a] ++ l from rfl, List.map_append, summarize_append laws,
      hAppend, ih, hLeaf]
    simp [summarize, laws.rightId]

/-- Test the supplied finite merge table, without testing commutativity. -/
def checkLaws (merge : Bits w → Bits w → Bits w) (empty : Bits w) : Bool :=
  decide ((∀ a b c, merge (merge a b) c = merge a (merge b c)) ∧
    (∀ a, merge empty a = a) ∧ (∀ a, merge a empty = a))

theorem checkLaws_eq_true :
    checkLaws merge empty = true ↔ Laws merge empty := by
  rw [checkLaws, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.assoc, h.leftId, h.rightId⟩⟩

section FiniteEvaluator

variable {α S β : Type*}

/-- A local check for a supplied finite evaluator of words. The forward
simulation step reads one leaf on the left of an already summarized suffix. -/
structure LocalLaws (step : α → S → S) (initial : S) (encode : S → Bits w)
    (leaf : α → Bits w) (observe : S → β) (readout : Bits w → β)
    (merge : Bits w → Bits w → Bits w) (empty : Bits w) : Prop where
  initial_eq : encode initial = empty
  step_eq : ∀ a s, encode (step a s) = merge (leaf a) (encode s)
  observe_eq : ∀ s, observe s = readout (encode s)

theorem LocalLaws.observe_foldr {step : α → S → S} {initial : S} {encode : S → Bits w}
    {leaf : α → Bits w} {observe : S → β} {readout : Bits w → β}
    (localLaws : LocalLaws step initial encode leaf observe readout merge empty) (l : List α) :
    observe (l.foldr step initial) = readout (summarize merge empty (l.map leaf)) := by
  have h (l : List α) : encode (l.foldr step initial) = summarize merge empty (l.map leaf) := by
    induction l with
    | nil => exact localLaws.initial_eq
    | cons a l ih =>
      simp only [List.foldr_cons, List.map_cons, summarize] at ih ⊢
      rw [localLaws.step_eq, ih]
  rw [localLaws.observe_eq, h]

/-- Exhaustively test a supplied finite local simulation. -/
def checkLocal [Fintype α] [Fintype S] [DecidableEq β]
    (step : α → S → S) (initial : S) (encode : S → Bits w)
    (leaf : α → Bits w) (observe : S → β) (readout : Bits w → β)
    (merge : Bits w → Bits w → Bits w) (empty : Bits w) : Bool :=
  decide (encode initial = empty ∧
    (∀ a s, encode (step a s) = merge (leaf a) (encode s)) ∧
    (∀ s, observe s = readout (encode s)))

theorem checkLocal_eq_true [Fintype α] [Fintype S] [DecidableEq β]
    {step : α → S → S} {initial : S} {encode : S → Bits w} {leaf : α → Bits w}
    {observe : S → β} {readout : Bits w → β} :
    checkLocal step initial encode leaf observe readout merge empty = true ↔
      LocalLaws step initial encode leaf observe readout merge empty := by
  rw [checkLocal, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩,
    fun h => ⟨h.initial_eq, h.step_eq, h.observe_eq⟩⟩

/-- Return a certificate for the supplied finite evaluator and summary
template when all local checks pass. A failed check returns `none`. -/
def recognize? [Fintype α] [Fintype S] [DecidableEq β]
    (step : α → S → S) (initial : S) (encode : S → Bits w)
    (leaf : α → Bits w) (observe : S → β) (readout : Bits w → β)
    (merge : Bits w → Bits w → Bits w) (empty : Bits w) :
    Option (PLift (Laws merge empty ∧ LocalLaws step initial encode leaf observe readout merge empty)) :=
  if h : checkLaws merge empty = true ∧
      checkLocal step initial encode leaf observe readout merge empty = true then
    some ⟨checkLaws_eq_true.mp h.1, checkLocal_eq_true.mp h.2⟩
  else none

end FiniteEvaluator

section Obstructions

variable {α S γ β : Type*}

/-- A pair of equal summaries that the same right context can distinguish. -/
def Collision (summary : α → S) (observe : α → γ → β) (u v : α) (z : γ) : Prop :=
  summary u = summary v ∧ observe u z ≠ observe v z

theorem Collision.noReadout {summary : α → S} {observe : α → γ → β} {u v : α} {z : γ}
    (h : Collision summary observe u v z) :
    ¬ ∃ readout : S → γ → β, ∀ a c, readout (summary a) c = observe a c := by
  rintro ⟨readout, hread⟩
  exact h.2 ((hread u z).symm.trans ((congrArg (readout · z) h.1).trans (hread v z)))

/-- Search the supplied lists of left blocks and right contexts for an obstruction. -/
def findCollision? [DecidableEq S] [DecidableEq β] (summary : α → S) (observe : α → γ → β)
    (left : List α) (contexts : List γ) : Option (α × α × γ) :=
  ((left.product (left.product contexts)).find? fun (u, v, z) =>
    decide (summary u = summary v ∧ observe u z ≠ observe v z))

theorem findCollision?_sound [DecidableEq S] [DecidableEq β]
    {summary : α → S} {observe : α → γ → β} {left : List α} {contexts : List γ}
    {u v : α} {z : γ} (h : findCollision? summary observe left contexts = some (u, v, z)) :
    Collision summary observe u v z := by
  have h' := List.find?_some (p := fun x : α × α × γ =>
    decide (summary x.1 = summary x.2.1 ∧ observe x.1 x.2.2 ≠ observe x.2.1 x.2.2)) h
  simpa only [Collision, decide_eq_true_eq] using h'

/-- A failed search only rules out collisions among the supplied candidates. -/
theorem findCollision?_eq_none_iff [DecidableEq S] [DecidableEq β]
    {summary : α → S} {observe : α → γ → β} {left : List α} {contexts : List γ} :
    findCollision? summary observe left contexts = none ↔
      ∀ u ∈ left, ∀ v ∈ left, ∀ z ∈ contexts, ¬ Collision summary observe u v z := by
  have hmem (u v : α) (z : γ) :
      (u, v, z) ∈ left.product (left.product contexts) ↔
        u ∈ left ∧ v ∈ left ∧ z ∈ contexts := by
    change (u, v, z) ∈ left ×ˢ (left ×ˢ contexts) ↔ _
    simp only [List.mem_product]
  simp only [findCollision?, List.find?_eq_none, Prod.forall, hmem,
    decide_eq_true_eq, Collision]
  exact ⟨fun h u hu v hv z hz => h u v z ⟨hu, hv, hz⟩,
    fun h u v z ⟨hu, hv, hz⟩ => h u hu v hv z hz⟩

/-- Pairwise distinguishable representatives need distinct summaries. This
bounds the bit width of an independent left summary for the given cut. -/
theorem width_lower_bound {r : ℕ} (summary : α → Bits w) (observe : α → γ → β)
    (readout : Bits w → γ → β) (correct : ∀ a z, readout (summary a) z = observe a z)
    (representative : Fin r → α)
    (distinguishable : ∀ i j, i ≠ j → ∃ z, observe (representative i) z ≠
      observe (representative j) z) :
    Nat.clog 2 r ≤ w := by
  have hinj : Function.Injective (summary ∘ representative) := by
    intro i j heq
    by_contra hne
    obtain ⟨z, hz⟩ := distinguishable i j hne
    exact Collision.noReadout (show Collision summary observe (representative i)
      (representative j) z from ⟨heq, hz⟩) ⟨readout, correct⟩
  apply (Nat.clog_le_iff_le_pow (b := 2) (by decide)).mpr
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa [Bits, Fintype.card_fun] using hcard

end Obstructions
end PredictionDepth.BlockSummary
