import PredictionDepth.FrozenPascal.UniformGuards
import PredictionDepth.SparseCorrections.Semantics

/-! The common-cone input format, with total deciders at all raw word lengths. -/

namespace PredictionDepth.SparseCorrections

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open StandardComplexity Turing.MultiTapeTM
open FrozenPascal (constBit constBit_depth)
open FrozenPascal.UniformGuards (castInputs castInputs_code castInputs_depth)

abbrev Gates := Circuit signature

abbrev inputWidth (q R T : ℕ) : ℕ := coneWidth q R T 0

def timeOfLength (q R n : ℕ) : ℕ := (n / q - 1) / (2 * R)

/-- Using the round trip as the validity test avoids special cases in the
decoder and directly identifies the arity required by the typed circuit. -/
abbrev LegalLength (q R n : ℕ) : Prop := inputWidth q R (timeOfLength q R n) = n

instance (q R n : ℕ) : Decidable (LegalLength q R n) := inferInstanceAs (Decidable (_ = _))

@[simp] theorem timeOfLength_inputWidth {q R : ℕ} (hq : 0 < q) (hR : 0 < R) (T : ℕ) :
    timeOfLength q R (inputWidth q R T) = T := by
  simp only [timeOfLength, inputWidth, coneWidth, Nat.sub_zero, Nat.mul_div_cancel _ hq,
    Nat.add_sub_cancel, ← Nat.mul_assoc]
  exact Nat.mul_div_cancel_left _ (by omega)

theorem legalLength_inputWidth {q R : ℕ} (hq : 0 < q) (hR : 0 < R) (T : ℕ) :
    LegalLength q R (inputWidth q R T) := by
  simp [LegalLength, timeOfLength_inputWidth hq hR]

theorem legalLength_iff_exists {q R n : ℕ} (hq : 0 < q) (hR : 0 < R) :
    LegalLength q R n ↔ ∃ T, inputWidth q R T = n := by
  constructor
  · exact fun h => ⟨_, h⟩
  · rintro ⟨T, rfl⟩
    exact legalLength_inputWidth hq hR T

theorem inputWidth_logspace (q R : ℕ) :
    ComputableInLogSpace (inputWidth q R) encUnary encUnary :=
  ((ComputableInLogSpace.id.unaryMulConst (2 * R)).unaryAdd
    (ComputableInLogSpace.const 1)).unaryMulConst q |>.congr_fun
    (fun T => by simp [inputWidth, coneWidth, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm])

theorem timeOfLength_logspace (q R : ℕ) :
    ComputableInLogSpace (timeOfLength q R) encUnary encUnary :=
  ((ComputableInLogSpace.id.unaryDiv (ComputableInLogSpace.const q)).unarySub
    (ComputableInLogSpace.const 1)).unaryDiv (ComputableInLogSpace.const (2 * R))

theorem legalLength_logspace (q R : ℕ) :
    ComputableInLogSpace (fun n => decide (LegalLength q R n)) encUnary encBool :=
  ((inputWidth_logspace q R).comp (timeOfLength_logspace q R)).unaryEq
    ComputableInLogSpace.id

/-- Project either output of a two-output certificate and reject malformed
lengths, including zero when the number of tracks is positive. -/
def lengthFamily {q R : ℕ} (P : ∀ T, Gates (inputWidth q R T) 2)
    (lane : Fin 2) : BooleanCircuitFamily := fun n =>
  if h : LegalLength q R n then
    castInputs h ((Circuit.wiring signature (fun _ : Fin 1 => lane)).comp
      (P (timeOfLength q R n)))
  else constBit n false

private theorem castInputs_eval {n m k : ℕ} (h : n = m) (c : Gates n k)
    (x : Fin m → Bool) :
    (castInputs h c).eval interpretation x = c.eval interpretation (x ∘ Fin.cast h) := by
  subst m
  rfl

theorem lengthFamily_eval {q R n : ℕ} (P : ∀ T, Gates (inputWidth q R T) 2) (lane : Fin 2)
    (x : Fin n → Bool) :
    (lengthFamily P lane n).eval interpretation x 0 =
      if h : LegalLength q R n then
        (P (timeOfLength q R n)).eval interpretation (x ∘ Fin.cast h) lane
      else false := by
  unfold lengthFamily
  split_ifs with h
  · simp [castInputs_eval]
  · simp

theorem lengthFamily_eval_at_time {q R : ℕ} (hq : 0 < q) (hR : 0 < R)
    (P : ∀ T, Gates (inputWidth q R T) 2) (lane : Fin 2) (T : ℕ)
    (x : Fin (inputWidth q R T) → Bool) :
    (lengthFamily P lane (inputWidth q R T)).eval interpretation x 0 =
      (P T).eval interpretation x lane := by
  have he : lengthFamily P lane (inputWidth q R T) =
      (Circuit.wiring signature (fun _ : Fin 1 => lane)).comp (P T) := by
    apply Circuit.code_injective
    simp only [lengthFamily, dite_eq_left (legalLength_inputWidth hq hR T), castInputs_code,
      ← compCode_code]
    exact congrArg (fun t => compCode (inputWidth q R t)
      (Circuit.wiring signature (fun _ : Fin 1 => lane)).code (P t).code)
      (timeOfLength_inputWidth hq hR T)
  simp [he]

theorem lengthFamily_uniform {q R : ℕ} (P : ∀ T, Gates (inputWidth q R T) 2) (lane : Fin 2)
    (hP : ComputableInLogSpace (fun T => (P T).code) encUnary encCode) :
    LogspaceUniform (lengthFamily P lane) := by
  let sel : Gates 2 1 := Circuit.wiring signature (fun _ : Fin 1 => lane)
  have hsel := CodeLogspace.circuit_comp_logspace (inputWidth_logspace q R) hP
    (ComputableInLogSpace.const sel.code)
  have hc : ComputableInLogSpace (fun n => (lengthFamily P lane n).code) encUnary encCode := by
    refine ((legalLength_logspace q R).ite (hsel.comp (timeOfLength_logspace q R))
      (FrozenPascal.Code.constant ComputableInLogSpace.id false)).congr_fun ?_
    intro n
    simp only [lengthFamily, decide_eq_true_eq, Function.comp_apply]
    split_ifs <;> simp [sel]
  exact (ComputableInLogSpace.id.pair hc).congr (fun _ => rfl)

def lengthLanguage {q R : ℕ} (P : ∀ T, Gates (inputWidth q R T) 2) (lane : Fin 2) :
    Set (List Bool) :=
  {x | evaluateFamily (lengthFamily P lane) x = true}

/-- Time-indexed polylogarithmic bounds transfer to the actual input length,
including the constant-depth rejection circuits for malformed lengths. -/
theorem lengthLanguage_mem_uniformNCLevel {q R : ℕ}
    (P : ∀ T, Gates (inputWidth q R T) 2) (lane : Fin 2)
    (hP : ComputableInLogSpace (fun T => (P T).code) encUnary encCode) (d C K : ℕ)
    (hd : ∀ T, (P T).depth ≤ C + K * (Nat.clog 2 (T + 1)) ^ d) :
    lengthLanguage P lane ∈ UniformNCLevel d := by
  apply mem_uniformNCLevel_of_uniform (c := C + K + 1) (lengthFamily_uniform P lane hP)
    (fun _ => Iff.rfl)
  intro n
  have hpos : 1 ≤ (Nat.log 2 n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  unfold lengthFamily
  split_ifs with h
  · rw [castInputs_depth]
    have ht : timeOfLength q R n ≤ n :=
      (Nat.div_le_self ..).trans ((Nat.sub_le ..).trans (Nat.div_le_self ..))
    have hl := (Nat.clog_mono_right 2 (Nat.succ_le_succ ht)).trans
      (clog_succ_le_log_add_one n)
    have hs := Circuit.depth_comp_le (Circuit.wiring signature (fun _ : Fin 1 => lane))
      (P (timeOfLength q R n))
    simp only [Circuit.depth_wiring, zero_add] at hs
    refine hs.trans ((hd _).trans ?_)
    calc
      C + K * (Nat.clog 2 (timeOfLength q R n + 1)) ^ d ≤
          C * (Nat.log 2 n + 1) ^ d + K * (Nat.log 2 n + 1) ^ d :=
        Nat.add_le_add (Nat.le_mul_of_pos_right C hpos)
          (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hl d))
      _ ≤ (C + K + 1) * (Nat.log 2 n + 1) ^ d := by rw [Nat.add_mul, Nat.add_mul]; omega
  · simp only [constBit_depth]
    exact Nat.mul_le_mul (by omega : 1 ≤ C + K + 1) hpos

theorem lengthLanguage_mem_uniformNC_one {q R : ℕ}
    (P : ∀ T, Gates (inputWidth q R T) 2) (lane : Fin 2)
    (hP : ComputableInLogSpace (fun T => (P T).code) encUnary encCode) (C K : ℕ)
    (hd : ∀ T, (P T).depth ≤ C + K * Nat.clog 2 (T + 1)) :
    lengthLanguage P lane ∈ UniformNCLevel 1 :=
  lengthLanguage_mem_uniformNCLevel P lane hP 1 C K (by simpa only [pow_one] using hd)

end PredictionDepth.SparseCorrections
