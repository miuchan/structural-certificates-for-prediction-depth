import PredictionDepth.SparseCorrections.Compiler
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-! Bit-length bounds for the exact CSLib gate serialization, including wire addresses. -/

namespace PredictionDepth.SparseCorrections

open Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

/-- Each address has at most w binary digits. Framing its digits takes
2 * w + 1 bits. A framed gate charges a constant operation field and at
most two framed addresses. The gate list itself is framed before the
output addresses. -/
def codeBitBound (n m G : ℕ) : ℕ :=
  let w := Nat.log2 (n + G) + 1
  2 * (G * (8 * w + 23)) + 1 + m * (2 * w + 1)

/-- Bound the raw serialized code using any upper bound on the gate count.
The number of output addresses is charged even when the circuit is wiring. -/
theorem circuit_code_length_le (c : Gates n m) (hG : c.size ≤ G) :
    (Boolean.encCode c.code).length ≤ codeBitBound n m G := by
  let w := Nat.log2 (n + G) + 1
  have hvalid := (Circuit.isSome_ofCode_iff (n := n) (m := m) (code := c.code)).mp
    (by rw [Circuit.ofCode_code]; rfl)
  have href := StandardComplexity.CodeLogspace.circuit_boundedReferences c
  have haddr (i : ℕ) (hi : i ≤ n + c.size) : (encNat i).length ≤ w :=
    length_encNat_le_log2 (hi.trans (Nat.add_le_add_left hG n))
  have hgate (g : Op × List ℕ) (hg : g ∈ c.code.1) :
      (Boolean.encGate g).length ≤ 4 * w + 11 := by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    let gate := c.code.1[j]
    have harity : gate.2.length ≤ 2 := by
      rw [(hvalid.1.getElem j hj).1]
      cases gate.1 <;> simp
    have hargs := length_encList_le encNat gate.2 (fun i hi =>
      haddr i (href.1 gate (List.getElem_mem hj) i hi))
    have hop : (encOp gate.1).length ≤ 4 := by
      simp only [encOp, Function.Embedding.coeFn_mk, encUnary_apply, List.length_replicate]
      cases gate.1 with
      | const b => cases b <;> decide
      | not | and | or => decide
    have ha := hargs.trans (Nat.mul_le_mul_right (2 * w + 1) harity)
    change (encPair encOp (encList encNat) gate).length ≤ _
    rw [length_encPair]
    omega
  have hgateList := length_encList_le Boolean.encGate c.code.1 hgate
  rw [Circuit.length_code_fst] at hgateList
  have hgateList' := hgateList.trans (Nat.mul_le_mul_right (2 * (4 * w + 11) + 1) hG)
  have hout := length_encList_le encNat c.code.2 (fun i hi => haddr i (href.2 i hi))
  rw [hvalid.2.1] at hout
  change (encPair (encList Boolean.encGate) (encList encNat) c.code).length ≤ _
  rw [length_encPair]
  change _ ≤ 2 * (G * (8 * w + 23)) + 1 + m * (2 * w + 1)
  have hb : 2 * (4 * w + 11) + 1 = 8 * w + 23 := by omega
  rw [hb] at hgateList'
  omega

/-- In the full encoding used by uniform circuit families, the unary input
arity is also framed. The output arity is fixed by the encoding's type. -/
theorem circuit_description_length_le (c : Gates n m) (hG : c.size ≤ G) :
    (Boolean.encCircuit m ⟨n, c⟩).length ≤ 2 * n + 1 + codeBitBound n m G := by
  rw [Boolean.encCircuit_apply, length_encPair, encUnary_apply, List.length_replicate]
  exact Nat.add_le_add_left (circuit_code_length_le c hG) _

/-- The actual two-output description is bounded by the proved gate budget
times logarithmic wire-address width, plus the unary input-arity header. -/
theorem compile_description_length_le (response : Gates (M + n) V) (check : Fin M → Gates V 1)
    (obs : Fin V) (candidates : Fin N → Fin M → Bool) (hcheck : ∀ j, (check j).size ≤ s) :
    let G := N * 2 * (response.size + M * s + 8 * (M + 1) + 3) + 16 * (N + 1)
    (Boolean.encCircuit 2 ⟨n, compile response check obs candidates⟩).length ≤
      2 * n + 1 + codeBitBound n 2 G :=
  circuit_description_length_le _ (compile_size response check obs candidates hcheck)

end PredictionDepth.SparseCorrections
