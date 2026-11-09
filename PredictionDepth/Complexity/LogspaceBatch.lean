import PredictionDepth.Complexity.LogspaceBatch.Bounds
import PredictionDepth.Complexity.BatchList

/-!
# Polynomial batches of logarithmic-space computations

The controller proved below retains the original input on its read-only tape,
keeps a binary index, and runs the finite native machine on virtual framed
input. Output is streamed; neither the input copy nor previous output chunks
are charged as hidden workspace. The theorem applies to polynomially many
calls, not merely a fixed number of calls.
-/

namespace PredictionDepth.StandardComplexity.LogspaceBatch

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Turing.VirtualWord

/-- An arbitrary logspace word function can be run polynomially many times,
with the common original input and a different unary index, streaming all its
outputs in order. -/
theorem flatMap_polynomial {α : Type} {enc : α ↪ List Bool}
    {g : α × ℕ → List Bool}
    (hg : ComputableInLogSpace g (encPair enc encUnary) encBits) (C d : ℕ) :
    ComputableInLogSpace
      (fun a => (List.range (count C d (enc a).length)).flatMap (fun j => g (a, j)))
      enc encBits := by
  classical
  obtain ⟨tg, c, k, S, hS, tm, htm⟩ := hg
  let : Fintype S := Fintype.ofFinite S
  let eS : S ↪ ℕ := (Fintype.equivFin S).toEmbedding.trans Fin.valEmbedding
  let D := desc eS eBit tm
  have hspace (a : α) (j : ℕ) : tm.RunsInSpace (encPair enc encUnary (a, j))
      (c * (Nat.log2 (encPair enc encUnary (a, j)).length + 1)) := (htm (a, j)).2.2
  obtain ⟨K, hK⟩ := native_configuration_bound eS tm c C d hspace
  obtain ⟨L, hL⟩ := saved_states_bound (enc := enc) D C d K hK
  let Inv (a : α) (s : State) := (encState s).length ≤ L * (Nat.log2 (enc a).length + 1)
  have hchunks (a : α) (j : ℕ) : ∃ T,
      (∀ t < T, (Native.machine D).halted
        ((Native.machine D).run (frame (enc a) ++ List.replicate j true) t) = false) ∧
      (Native.machine D).halted
        ((Native.machine D).run (frame (enc a) ++ List.replicate j true) T) = true ∧
      (Native.machine D).output (frame (enc a) ++ List.replicate j true) T = g (a, j) := by
    obtain ⟨T, _, hh⟩ := exists_haltsAt_of_runsInTime (htm (a, j)).2.1
    have hv : encPair enc encUnary (a, j) = frame (enc a) ++ List.replicate j true := rfl
    refine ⟨T, ?_, ?_, ?_⟩
    · intro t ht
      rw [Native.halted_native, ← hv]
      exact Option.isNone_eq_false_iff.mpr (Option.isSome_iff_ne_none.mpr (hh.not_halted ht))
    · rw [Native.halted_native, ← hv, hh.halted]
      rfl
    · rw [Native.output_native, ← hv, output_haltsAt (htm (a, j)).1 hh]
      rfl
  have htraces (a : α) : Nonempty (Trace (machine D C d) (enc a) (Inv a)
      (machine D C d).init (itemState (enc a).length (count C d (enc a).length) (init D))
      ((List.range (count C d (enc a).length)).flatMap (fun j => g (a, j)))) :=
    complete_trace D C d (enc a) (Inv a) (fun j => g (a, j))
      (hL a).1 (hL a).2 (fun j _ => hchunks a j)
  let tr (a : α) := Classical.choice (htraces a)
  obtain ⟨hq, hn, he, hh, hf⟩ := components D C d
  refine (machine D C d).computableInLogSpace hq hn he hh hf (fun a => (tr a).time)
    ?_ ?_ ?_ ⟨L, ?_⟩
  · intro a
    change (machine D C d).halted ((machine D C d).runFrom (enc a) (machine D C d).init
      (tr a).time) = true
    rw [(tr a).reaches]
    simp [machine, itemState]
  · intro a t ht
    exact (tr a).live t ht
  · intro a
    have ho := (tr a).output
    change (machine D C d).output (enc a) (tr a).time =
      (List.range (count C d (enc a).length)).flatMap (fun j => g (a, j)) ++ [] at ho
    exact (ho.trans (List.append_nil _)).symm
  · intro a t ht
    exact (tr a).bounded t ht

/-- Full input-dependent batching: a logspace unary clock supplies the count,
and the same logspace worker may inspect the entire original input on every
call. The polynomial envelope follows from the actual clock machine. -/
theorem flatMap_range {α : Type} {enc : α ↪ List Bool}
    {r : α → ℕ} {g : α × ℕ → List Bool}
    (hr : ComputableInLogSpace r enc encUnary)
    (hg : ComputableInLogSpace g (encPair enc encUnary) encBits) :
    ComputableInLogSpace (fun a => (List.range (r a)).flatMap (fun j => g (a, j)))
      enc encBits := by
  obtain ⟨C, d, hbound⟩ := hr.polyBounded_length.exists_le
  have hbound' (a : α) : r a ≤ count C d (enc a).length := by
    simpa only [encUnary_apply, List.length_replicate, count] using hbound a
  have htest : ComputableInLogSpace (fun p : α × ℕ => decide (p.2 < r p.1))
      (encPair enc encUnary) encBool :=
    (ComputableInLogSpace.snd enc encUnary).unaryLt
      (hr.comp (ComputableInLogSpace.fst enc encUnary))
  have hmasked := htest.ite hg (ComputableInLogSpace.const ([] : List Bool))
  have hbatch := flatMap_polynomial hmasked C d
  refine hbatch.congr_fun ?_
  intro a
  simpa only [decide_eq_true_eq] using
    (range_flatMap_mask (fun j => g (a, j)) (hbound' a)).symm

end PredictionDepth.StandardComplexity.LogspaceBatch
