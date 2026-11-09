import PredictionDepth.Complexity.NCReductionConstruction
import PredictionDepth.Complexity.CodeLogspace

/-!
The scalar predicates used in reduction composition are genuine logspace
computations. Hardwiring their query index preserves their semantic answers.
-/

namespace PredictionDepth.StandardComplexity.ReductionConstruction

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM

def bitQuery (f : List Bool → List Bool) (q : Query) : Bool := (f q.2).getD q.1 false
def lengthQuery (f : List Bool → List Bool) (q : Query) : Bool := decide ((f q.2).length = q.1)

theorem bitQuery_logspace {f : List Bool → List Bool}
    (hf : ComputableInLogSpace f encBits encBits) :
    ComputableInLogSpace (bitQuery f) queryEncoding encBool := by
  have hw := hf.comp (ComputableInLogSpace.snd encUnary encBits)
  have hj := ComputableInLogSpace.fst encUnary encBits
  have h := (ComputableInLogSpace.bitsHeadD false).comp (hw.bitsDrop' hj)
  exact h.congr_fun fun q => by simp [bitQuery, List.getD_eq_getElem?_getD]

theorem lengthQuery_logspace {f : List Bool → List Bool}
    (hf : ComputableInLogSpace f encBits encBits) :
    ComputableInLogSpace (lengthQuery f) queryEncoding encBool := by
  have hw := hf.comp (ComputableInLogSpace.snd encUnary encBits)
  exact (CodeLogspace.bitsLength.comp hw).unaryEq
    (ComputableInLogSpace.fst encUnary encBits)

/-- A prefix circuit supplies exactly the encoded query `(j, original input)`;
the index is fixed in the circuit, while every source-input bit remains live. -/
theorem prefixed_correct (F : BooleanCircuitFamily) (g : Query → Bool)
    (hF : ∀ q, evaluateFamily F (queryEncoding q) = g q)
    (n j : ℕ) (x : Fin n → Bool) :
    (prefixed F n j).eval interpretation x 0 = g (j, List.ofFn x) := by
  have h := hF (j, List.ofFn x)
  dsimp only [evaluateFamily] at h
  rw [queryEncoding_eq] at h
  rw [List.length_append, List.length_ofFn] at h
  rw [BitString.ofList_append rfl (List.length_ofFn (f := x)), BitString.ofList_ofFn] at h
  have hp : BitString.ofList (queryPrefix j).length (queryPrefix j) =
      fun i : Fin (queryPrefix j).length => (queryPrefix j)[i.val] := by
    funext i
    rw [BitString.ofList, List.getD_eq_getElem _ _ i.isLt]
  rw [hp] at h
  simpa only [prefixed, eval_prefixCircuit] using h

theorem prefixed_bitQuery (F : BooleanCircuitFamily) (f : List Bool → List Bool)
    (hF : ∀ q, evaluateFamily F (queryEncoding q) = bitQuery f q)
    (n j : ℕ) (x : Fin n → Bool) :
    (prefixed F n j).eval interpretation x 0 = (f (List.ofFn x)).getD j false :=
  prefixed_correct F (bitQuery f) hF n j x

theorem prefixed_lengthQuery (F : BooleanCircuitFamily) (f : List Bool → List Bool)
    (hF : ∀ q, evaluateFamily F (queryEncoding q) = lengthQuery f q)
    (n j : ℕ) (x : Fin n → Bool) :
    (prefixed F n j).eval interpretation x 0 = decide ((f (List.ofFn x)).length = j) :=
  prefixed_correct F (lengthQuery f) hF n j x

/-- The fixed polynomial envelope used for candidate output lengths is printed
in unary by an actual logspace transducer. -/
theorem polynomialClock_logspace (C d : ℕ) :
    ComputableInLogSpace (fun n : ℕ => C * (n + 1) ^ d) encUnary encUnary := by
  have hs : ComputableInLogSpace (fun n : ℕ => n + 1) encUnary encUnary :=
    ComputableInLogSpace.id.unaryAdd (ComputableInLogSpace.const 1)
  have hp : ∀ d, ComputableInLogSpace (fun n : ℕ => (n + 1) ^ d) encUnary encUnary := by
    intro d
    induction d with
    | zero => simpa only [pow_zero] using (ComputableInLogSpace.const 1 (encIn := encUnary)
        (encMid := encUnary))
    | succ d ih => simpa only [pow_succ] using ih.unaryMul hs
  exact (ComputableInLogSpace.const C).unaryMul (hp d)

end PredictionDepth.StandardComplexity.ReductionConstruction
