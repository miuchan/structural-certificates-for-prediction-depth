import PredictionDepth.Complexity.NCReductionConstruction
import PredictionDepth.LogBounds
import CslibFrontier.Computability.Circuit.Boolean.Substitution

/-! Polynomial size and polylogarithmic depth for variable-length reduction banks. -/
namespace PredictionDepth.StandardComplexity.ReductionConstruction
open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators

theorem prefixed_depth (F : BooleanCircuitFamily) (n j : ℕ) :
    (prefixed F n j).depth ≤ (F (2 * j + 1 + n)).depth + 1 := by
  have h := Circuit.depth_comp_le (F ((queryPrefix j).length + n))
    (substituteCircuit (prefixInputs (queryPrefix j) n))
  apply h.trans
  have he : (queryPrefix j).length + n = 2 * j + 1 + n := by rw [queryPrefix_length]
  have hF := congrArg (fun k => (F k).depth) he
  calc
    _ ≤ (F ((queryPrefix j).length + n)).depth + 1 :=
      Nat.add_le_add_left (depth_substituteCircuit_le (prefixInputs (queryPrefix j) n)) _
    _ = (F (2 * j + 1 + n)).depth + 1 := congrArg (· + 1) hF

theorem bitBank_size_le (F : BooleanCircuitFamily) (n m bound : ℕ)
    (h : ∀ j < m, (prefixed F n j).size ≤ bound) :
    (bitBank F n m).size ≤ m * bound := by
  simp only [bitBank, Circuit.size_pi]
  calc
    _ ≤ ∑ _j : Fin m, bound := Finset.sum_le_sum (fun j _ => h j.val j.isLt)
    _ = m * bound := by simp

theorem bitBank_depth_le (F : BooleanCircuitFamily) (n m bound : ℕ)
    (h : ∀ j < m, (prefixed F n j).depth ≤ bound) :
    (bitBank F n m).depth ≤ bound := Circuit.depth_pi_le _ (fun j => h j.val j.isLt)

theorem family_size_le (target bits lengthTest : BooleanCircuitFamily) (bound : ℕ → ℕ)
    (n T B L : ℕ)
    (ht : ∀ m ≤ bound n, (target m).size ≤ T)
    (hb : ∀ j ≤ bound n, (prefixed bits n j).size ≤ B)
    (hl : ∀ j ≤ bound n, (prefixed lengthTest n j).size ≤ L) :
    (family target bits lengthTest bound n).size ≤
      (UniformOR.family (bound n + 1)).size + (bound n + 1) * (T + bound n * B + L + 1) := by
  have hbranch (m : Fin (bound n + 1)) :
      (branch target bits lengthTest n m.val).size ≤ T + bound n * B + L + 1 := by
    have hbank := bitBank_size_le bits n m.val B (fun j hj => hb j (by omega))
    have hmul := Nat.mul_le_mul_right B (show m.val ≤ bound n by omega)
    have ht' := ht m.val (by omega)
    have hl' := hl m.val (by omega)
    simp only [branch, Circuit.size_comp, Circuit.size_append, Circuit.size_oneGate]
    omega
  simp only [family, Circuit.size_comp, Circuit.size_pi]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun m _ => hbranch m)
  simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul] at hsum
  omega

theorem family_depth_le (target bits lengthTest : BooleanCircuitFamily) (bound : ℕ → ℕ)
    (n T B L : ℕ)
    (ht : ∀ m ≤ bound n, (target m).depth ≤ T)
    (hb : ∀ j ≤ bound n, (prefixed bits n j).depth ≤ B)
    (hl : ∀ j ≤ bound n, (prefixed lengthTest n j).depth ≤ L) :
    (family target bits lengthTest bound n).depth ≤
      (UniformOR.family (bound n + 1)).depth + (T + B + L + 1) := by
  apply (Circuit.depth_comp_le _ _).trans
  apply Nat.add_le_add_left
  apply Circuit.depth_pi_le
  intro m
  have hbank := bitBank_depth_le bits n m.val B (fun j hj => hb j (by omega))
  have ht' := ht m.val (by omega)
  have hl' := hl m.val (by omega)
  have htb := (Circuit.depth_comp_le (target m.val) (bitBank bits n m.val)).trans
    (Nat.add_le_add ht' hbank)
  have happ := Circuit.depth_append_le ((target m.val).comp (bitBank bits n m.val))
    (prefixed lengthTest n m.val)
  have hmax : max (((target m.val).comp (bitBank bits n m.val)).depth)
      (prefixed lengthTest n m.val).depth ≤ T + B + L :=
    max_le (htb.trans (by omega)) (hl'.trans (by omega))
  have hg := Circuit.depth_comp_le (Circuit.oneGate (σ := signature) .and id)
    (((target m.val).comp (bitBank bits n m.val)).append (prefixed lengthTest n m.val))
  change (branch target bits lengthTest n m.val).depth ≤ _ at hg
  rw [Circuit.depth_oneGate] at hg
  exact hg.trans (by have := happ.trans hmax; omega)

theorem family_polynomialSize {target bits lengthTest : BooleanCircuitFamily} {bound : ℕ → ℕ}
    (hb : PolynomiallyBounded bound)
    (ht : PolynomiallyBounded (fun n => (target n).size))
    (hbits : PolynomiallyBounded (fun n => (bits n).size))
    (hlen : PolynomiallyBounded (fun n => (lengthTest n).size)) :
    PolynomiallyBounded (fun n => (family target bits lengthTest bound n).size) := by
  obtain ⟨At, kt, ht⟩ := polynomiallyBounded_iff_le.mp ht
  obtain ⟨Ab, kb, hbits⟩ := polynomiallyBounded_iff_le.mp hbits
  obtain ⟨Al, kl, hlen⟩ := polynomiallyBounded_iff_le.mp hlen
  let Q (n : ℕ) := 2 * bound n + 1 + n
  have hQ : PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  have hOR : PolynomiallyBounded (fun n => (UniformOR.family n).size) := by
    convert UniformOR.gateCount_polynomial using 1
    funext n
    exact UniformOR.family_size n
  have hbp : PolynomiallyBounded (fun n => bound n + 1) := hb.add (PolynomiallyBounded.const 1)
  have hQp : PolynomiallyBounded (fun n => Q n + 1) := hQ.add (PolynomiallyBounded.const 1)
  have hOR' : PolynomiallyBounded (fun n => (UniformOR.family (bound n + 1)).size) := hOR.comp hbp
  have hpoly : PolynomiallyBounded (fun n =>
      (UniformOR.family (bound n + 1)).size + (bound n + 1) *
        (At * (bound n + 1) ^ kt + bound n * (2 + Ab * (Q n + 1) ^ kb) +
          (2 + Al * (Q n + 1) ^ kl) + 1)) := by fun_prop
  apply hpoly.mono_of_le
  intro n
  apply family_size_le
  · intro m hm
    exact (ht m).trans (Nat.mul_le_mul_left At (Nat.pow_le_pow_left (by omega) kt))
  · intro j hj
    have ha : (queryPrefix j).length + n + 1 ≤ Q n + 1 := by
      rw [queryPrefix_length]
      dsimp only [Q]
      omega
    simp only [prefixed, size_prefixCircuit]
    exact Nat.add_le_add_left ((hbits _).trans
      (Nat.mul_le_mul_left Ab (Nat.pow_le_pow_left ha kb))) 2
  · intro j hj
    have ha : (queryPrefix j).length + n + 1 ≤ Q n + 1 := by
      rw [queryPrefix_length]
      dsimp only [Q]
      omega
    simp only [prefixed, size_prefixCircuit]
    exact Nat.add_le_add_left ((hlen _).trans
      (Nat.mul_le_mul_left Al (Nat.pow_le_pow_left ha kl))) 2

/-- One polynomial envelope gives a common logarithmic bound for every bank index. -/
theorem polynomial_log_envelope {q : ℕ → ℕ} (hq : PolynomiallyBounded q) :
    ∃ K : ℕ, ∀ n m, m ≤ q n → Nat.log 2 m + 1 ≤ K * (Nat.log 2 n + 1) := by
  obtain ⟨A, d, hq⟩ := polynomiallyBounded_iff_le.mp hq
  refine ⟨Nat.clog 2 A + d + 1, ?_⟩
  intro n m hm
  have hc := clog_of_polynomial_bound (hm.trans (hq n))
  have hl := Nat.log_le_clog 2 m
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem family_polylogDepth {target bits lengthTest : BooleanCircuitFamily} {bound : ℕ → ℕ}
    (hb : PolynomiallyBounded bound) {kt Ct Cb Cl : ℕ}
    (ht : ∀ n, (target n).depth ≤ Ct * (Nat.log 2 n + 1) ^ kt)
    (hbits : ∀ n, (bits n).depth ≤ Cb * (Nat.log 2 n + 1) ^ 2)
    (hlen : ∀ n, (lengthTest n).depth ≤ Cl * (Nat.log 2 n + 1) ^ 2) :
    ∃ k C : ℕ, ∀ n,
      (family target bits lengthTest bound n).depth ≤ C * (Nat.log 2 n + 1) ^ k := by
  let Q (n : ℕ) := 2 * bound n + 1 + n
  have hQ : PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  obtain ⟨K, hK⟩ := polynomial_log_envelope hQ
  refine ⟨kt + 3, (K + 1) + Ct * K ^ kt + (Cb * K ^ 2 + 1) + (Cl * K ^ 2 + 1) + 1, ?_⟩
  intro n
  let b := Nat.log 2 n + 1
  let E := b ^ (kt + 3)
  have hb₁ : 1 ≤ b := by dsimp [b]; omega
  have hE : 1 ≤ E := Nat.one_le_pow _ _ hb₁
  have hbE : b ≤ E := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb₁ (show 1 ≤ kt + 3 by omega)
  have h2E : b ^ 2 ≤ E := Nat.pow_le_pow_right hb₁ (by omega)
  have htE : b ^ kt ≤ E := Nat.pow_le_pow_right hb₁ (by omega)
  have htarget (m : ℕ) (hm : m ≤ bound n) : (target m).depth ≤ (Ct * K ^ kt) * E := by
    have hlog := hK n m (show m ≤ Q n by dsimp [Q]; omega)
    have hp := Nat.mul_le_mul_left Ct (Nat.pow_le_pow_left hlog kt)
    rw [mul_pow] at hp
    exact (ht m).trans (hp.trans (by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (Ct * K ^ kt) htE))
  have hpref (F : BooleanCircuitFamily) (C : ℕ)
      (hF : ∀ a, (F a).depth ≤ C * (Nat.log 2 a + 1) ^ 2)
      (j : ℕ) (hj : j ≤ bound n) : (prefixed F n j).depth ≤ (C * K ^ 2 + 1) * E := by
    have hlog := hK n (2 * j + 1 + n) (show 2 * j + 1 + n ≤ Q n by dsimp [Q]; omega)
    have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hlog 2)
    rw [mul_pow] at hp
    have hp' := Nat.mul_le_mul_left (C * K ^ 2) h2E
    have hf := prefixed_depth F n j
    have hval := hF (2 * j + 1 + n)
    dsimp only [E, b] at hp' hE ⊢
    nlinarith
  have hor : (UniformOR.family (bound n + 1)).depth ≤ (K + 1) * E := by
    have ho := UniformOR.family_depth (bound n + 1)
    have hc : Nat.clog 2 (bound n + 1) ≤ Nat.log 2 (bound n + 1) + 1 :=
      Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) _).le
    have hlog := hK n (bound n + 1) (by dsimp [Q]; omega)
    have hm := Nat.mul_le_mul_left K hbE
    dsimp only [E, b] at hm hE ⊢
    nlinarith
  have htotal := family_depth_le target bits lengthTest bound n
    ((Ct * K ^ kt) * E) ((Cb * K ^ 2 + 1) * E) ((Cl * K ^ 2 + 1) * E)
    htarget (hpref bits Cb hbits) (hpref lengthTest Cl hlen)
  change (family target bits lengthTest bound n).depth ≤ _ * E
  nlinarith

end PredictionDepth.StandardComplexity.ReductionConstruction
