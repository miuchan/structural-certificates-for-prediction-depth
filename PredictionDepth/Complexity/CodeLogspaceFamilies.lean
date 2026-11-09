import PredictionDepth.Complexity.CodeLogspace

/-!
# Logspace construction of variable-length parallel circuit banks

Lists and their prefixes are accessed by recomputation. A block's relocation
offset is the length of the streamed gate lists preceding it. At no point is
the complete bank retained on a work tape.
-/

namespace PredictionDepth.StandardComplexity.CodeLogspaceFamilies

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM
open CodeLogspace

variable {α β γ : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}

theorem range_map_getD {δ ε : Type} (l : List δ) (fallback : δ) (f : δ → ε) :
    (List.range l.length).map (fun j => f (l.getD j fallback)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < l.length := by simpa using hi
    simp [hi']

theorem range_flatMap_getD {δ ε : Type} (l : List δ) (fallback : δ) (f : δ → List ε) :
    (List.range l.length).flatMap (fun j => f (l.getD j fallback)) = l.flatMap f := by
  have h := congrArg List.flatten (range_map_getD l fallback f)
  simpa only [List.flatMap_def] using h

/-- A worker may reread both the whole original input and the selected item. -/
theorem mapWithInput (fallback : β) {l : α → List β} {f : α × β → γ}
    (hl : ComputableInLogSpace l enc (encList encB))
    (hf : ComputableInLogSpace f (encPair enc encB) encC) :
    ComputableInLogSpace (fun a => (l a).map (fun b => f (a, b))) enc (encList encC) := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hv := getD fallback (hl.comp hp) hi
  have hw := hf.comp (hp.pair hv)
  have h := map_range (ComputableInLogSpace.listLength.comp hl) hw
  exact h.congr_fun fun a => (range_map_getD (l a) fallback (fun b => f (a, b))).symm

/-- Stream a variable-length list from every polynomially indexed call. -/
theorem flatMap_range_list {r : α → ℕ} {f : α × ℕ → List β}
    (hr : ComputableInLogSpace r enc encUnary)
    (hf : ComputableInLogSpace f (encPair enc encUnary) (encList encB)) :
    ComputableInLogSpace (fun a => (List.range (r a)).flatMap (fun j => f (a, j)))
      enc (encList encB) := by
  have hw : ComputableInLogSpace (fun p => encList encB (f p))
      (encPair enc encUnary) encBits := hf.congr fun _ => rfl
  have h := LogspaceBatch.flatMap_range hr hw
  refine h.congr ?_
  intro a
  change ((List.range (r a)).flatMap (fun j => f (a, j))).flatMap (frame ∘ encB) = _
  rw [List.flatMap_assoc]
  rfl

theorem flatMapWithInput (fallback : β) {l : α → List β} {f : α × β → List γ}
    (hl : ComputableInLogSpace l enc (encList encB))
    (hf : ComputableInLogSpace f (encPair enc encB) (encList encC)) :
    ComputableInLogSpace (fun a => (l a).flatMap (fun b => f (a, b))) enc (encList encC) := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hv := getD fallback (hl.comp hp) hi
  have hw := hf.comp (hp.pair hv)
  have h := flatMap_range_list (ComputableInLogSpace.listLength.comp hl) hw
  exact h.congr_fun fun a => (range_flatMap_getD (l a) fallback (fun b => f (a, b))).symm

/-- A prefix is emitted by its valid indices; there is no prefix-sized workspace. -/
theorem take (fallback : β) {l : α → List β} {j : α → ℕ}
    (hl : ComputableInLogSpace l enc (encList encB))
    (hj : ComputableInLogSpace j enc encUnary) :
    ComputableInLogSpace (fun a => (l a).take (j a)) enc (encList encB) := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hw := getD fallback (hl.comp hp) hi
  have hcount := hj.unaryMin (ComputableInLogSpace.listLength.comp hl)
  have h := map_range hcount hw
  refine h.congr_fun ?_
  intro a
  apply List.ext_getElem
  · simp
  · intro i hi' hi''
    have hlen : i < (l a).length := by
      have := List.length_take (i := j a) (l := l a)
      omega
    simp [hlen]

/-- Public indexed normal form of parallel concatenation. -/
def indexedAppendCodes (n : ℕ) (codes : List RawCode) : RawCode :=
  ((List.range codes.length).flatMap fun j =>
      (shiftCode n ((codes.take j).flatMap Prod.fst).length (codes.getD j ([], []))).1,
    (List.range codes.length).flatMap fun j =>
      (shiftCode n ((codes.take j).flatMap Prod.fst).length (codes.getD j ([], []))).2)

theorem indexedAppendCodes_snoc (n : ℕ) (codes : List RawCode) (code : RawCode) :
    indexedAppendCodes n (codes ++ [code]) =
      ((indexedAppendCodes n codes).1 ++ (shiftCode n (codes.flatMap Prod.fst).length code).1,
        (indexedAppendCodes n codes).2 ++ (shiftCode n (codes.flatMap Prod.fst).length code).2) := by
  have ht (j : ℕ) (hj : j < codes.length) : (codes ++ [code]).take j = codes.take j :=
    List.take_append_of_le_length hj.le
  have hg (j : ℕ) (hj : j < codes.length) :
      (codes ++ [code]).getD j ([], []) = codes.getD j ([], []) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hj]
  have hlast : (codes ++ [code]).getD codes.length ([], []) = code := by
    simp [List.getD_eq_getElem?_getD]
  simp only [indexedAppendCodes, List.length_append, List.length_singleton, List.range_succ,
    List.flatMap_append, List.flatMap_singleton, List.take_left, hlast]
  apply Prod.ext <;> dsimp only <;> congr 1 <;>
    apply List.flatMap_congr <;> intro j hj <;>
    rw [ht j (List.mem_range.mp hj), hg j (List.mem_range.mp hj)]

theorem indexedAppendCodes_eq (n : ℕ) (codes : List RawCode) :
    indexedAppendCodes n codes = appendCodes n codes := by
  induction codes using List.reverseRecOn with
  | nil => rfl
  | append_singleton codes code ih =>
    rw [indexedAppendCodes_snoc, appendCodes_append_singleton, ih]
    simp only [appendCode, length_appendCodes, shiftCode]

/-- Relocate a whole block by a computed unary offset. -/
theorem shiftCode_logspace {n offset : α → ℕ} {code : α → RawCode}
    (hn : ComputableInLogSpace n enc encUnary)
    (hoffset : ComputableInLogSpace offset enc encUnary)
    (hcode : ComputableInLogSpace code enc encCode)
    (hbound : ∀ a, BoundedReferences (n a + (code a).1.length) (code a)) :
    ComputableInLogSpace (fun a => shiftCode (n a) (offset a) (code a)) enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hw := shiftCodeWire_logspace (hn.comp hp) (hoffset.comp hp) hi
  have hB := hn.unaryAdd (ComputableInLogSpace.listLength.comp hcode.fst')
  exact mapCode_logspace hcode hB hbound hw

/-- Variable-size block concatenation, with offsets computed by streaming only
the earlier gate lists. Each individual block may have a different size. -/
theorem appendCodes_logspace {n : α → ℕ} {codes : α → List RawCode}
    (hn : ComputableInLogSpace n enc encUnary)
    (hcodes : ComputableInLogSpace codes enc (encList encCode))
    (hbound : ∀ a code, code ∈ codes a →
      BoundedReferences (n a + code.1.length) code) :
    ComputableInLogSpace (fun a => appendCodes (n a) (codes a)) enc encCode := by
  have hp := ComputableInLogSpace.fst enc encUnary
  have hi := ComputableInLogSpace.snd enc encUnary
  have hc := getD ([], []) (hcodes.comp hp) hi
  have hpre := take ([], []) (hcodes.comp hp) hi
  have hpreGates := flatMapWithInput ([], []) hpre
    (ComputableInLogSpace.snd (encPair enc encUnary) encCode).fst'
  have hoffset := ComputableInLogSpace.listLength.comp hpreGates
  have hb (p : α × ℕ) :
      BoundedReferences (n p.1 + ((codes p.1).getD p.2 ([], [])).1.length)
        ((codes p.1).getD p.2 ([], [])) :=
    getD_property (hbound p.1) (by simp [BoundedReferences]) p.2
  have hshift := shiftCode_logspace (hn.comp hp) hoffset hc hb
  have hcount := ComputableInLogSpace.listLength.comp hcodes
  have hg := flatMap_range_list hcount hshift.fst'
  have ho := flatMap_range_list hcount hshift.snd'
  exact (hg.pair ho).congr_fun fun a => (indexedAppendCodes_eq (n a) (codes a)).symm

/-- Parallel assembly of typed circuits; their types discharge all reference
conditions, so there is no caller-supplied correctness or memory assumption. -/
theorem circuit_pi_logspace {n m : α → ℕ}
    {cs : ∀ a, Fin (m a) → Circuit signature (n a) 1}
    (hn : ComputableInLogSpace n enc encUnary)
    (hcodes : ComputableInLogSpace (fun a => List.ofFn (fun j => (cs a j).code))
      enc (encList encCode)) :
    ComputableInLogSpace (fun a => (Circuit.pi (cs a)).code) enc encCode := by
  have h := appendCodes_logspace hn hcodes (fun a code hc => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    rw [Circuit.length_code_fst]
    exact circuit_boundedReferences (cs a j))
  exact h.congr_fun fun a => (appendCodes_code (cs a)).symm

/-- Entrywise form: the generator is queried with unary bank indices and the
bank length itself is generated in logspace. -/
theorem circuit_pi_of_indexed_logspace {n m : α → ℕ}
    {cs : ∀ a, Fin (m a) → Circuit signature (n a) 1}
    (hn : ComputableInLogSpace n enc encUnary)
    (hm : ComputableInLogSpace m enc encUnary)
    (hentry : ComputableInLogSpace
      (fun p : α × ℕ => if h : p.2 < m p.1 then (cs p.1 ⟨p.2, h⟩).code else ([], []))
      (encPair enc encUnary) encCode) :
    ComputableInLogSpace (fun a => (Circuit.pi (cs a)).code) enc encCode := by
  have hlist := map_range hm hentry
  apply circuit_pi_logspace hn
  refine hlist.congr_fun ?_
  intro a
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hidx : i < m a := by simpa using hi
    simp [hidx]

end PredictionDepth.StandardComplexity.CodeLogspaceFamilies
