import PredictionDepth.Complexity.StandardPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow

/-! Native small-workspace arithmetic for the regular matrix-power layout. -/

namespace PredictionDepth.StandardComplexity.StandardPower
open Cslib
open Turing.MultiTapeTM ComputableInSpace

variable {α : Type} {enc : α ↪ List Bool} {budget : α → ℕ}
  {N : α → ℕ}

theorem size_budget (hN : ComputableInSpace N enc encNat budget) :
    ComputableInSpace (fun a => (N a).size) enc encNat budget :=
  budget_comp_linear natSize hN

/-- The padded width is produced in binary. Its bit length is only one more
than that of `N`; no exponential workspace is charged as constant. -/
theorem width_budget (hN : ComputableInSpace N enc encNat budget)
    (hin : (fun a => (enc a).length) ≼ budget) :
    ComputableInSpace (fun a => width (N a)) enc encNat budget := by
  apply budget_natPow_variable (budget_const (encB := encNat) 2 hin) (size_budget hN)
  have hb : (fun a => ((N a).size + 1) * (encNat 2).length +
      (encNat (N a).size).length + 1) ≼ fun a => (encNat (N a)).length := by
    refine .of_le_linear 3 3 ?_
    intro a
    have h := length_encNat_le_self (N a).size
    simp only [show (encNat 2).length = 2 from rfl, length_encNat_eq_size]
    simp only [length_encNat_eq_size] at h
    omega
  exact hb.trans hN.length_le

theorem layerWidth_budget (hN : ComputableInSpace N enc encNat budget)
    (hin : (fun a => (enc a).length) ≼ budget) :
    ComputableInSpace (fun a => layerWidth (N a)) enc encNat budget :=
  budget_natMul (budget_natMul hN hN) (width_budget hN hin)

theorem blockDepth_budget (hN : ComputableInSpace N enc encNat budget)
    (hin : (fun a => (enc a).length) ≼ budget) :
    ComputableInSpace (fun a => (N a).size + 1) enc encNat budget :=
  budget_natAdd (size_budget hN) (budget_const 1 hin)

theorem powerGateCount_budget {rounds : α → ℕ}
    (hN : ComputableInSpace N enc encNat budget)
    (hr : ComputableInSpace rounds enc encNat budget)
    (hin : (fun a => (enc a).length) ≼ budget) :
    ComputableInSpace (fun a => rounds a * (((N a).size + 1) * layerWidth (N a)))
      enc encNat budget :=
  budget_natMul hr (budget_natMul (blockDepth_budget hN hin) (layerWidth_budget hN hin))

theorem deciderGateCount_budget (hN : ComputableInSpace N enc encNat budget)
    (hin : (fun a => (enc a).length) ≼ budget) :
    ComputableInSpace (fun a => ((N a).size + 1) ^ 2 * layerWidth (N a)) enc encNat budget :=
  budget_natMul (budget_natPow (blockDepth_budget hN hin) hin 2) (layerWidth_budget hN hin)

theorem width_le (N : ℕ) : width N ≤ 2 * N + 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hn
  · decide
  · exact (RegularReduction.two_pow_size_le hn).trans (by omega)

theorem size_le_self (N : ℕ) : N.size ≤ N :=
  Nat.size_le.mpr Nat.lt_two_pow_self

theorem polynomiallyBounded_width {N : ℕ → ℕ} (hN : PolynomiallyBounded N) :
    PolynomiallyBounded (fun n => width (N n)) := by
  have h : PolynomiallyBounded (fun n => 2 * N n + 1) := by fun_prop
  exact h.mono_of_le (fun n => width_le (N n))

theorem polynomiallyBounded_size {N : ℕ → ℕ} (hN : PolynomiallyBounded N) :
    PolynomiallyBounded (fun n => (N n).size) :=
  hN.mono_of_le (fun n => size_le_self (N n))

theorem polynomiallyBounded_layerWidth {N : ℕ → ℕ} (hN : PolynomiallyBounded N) :
    PolynomiallyBounded (fun n => layerWidth (N n)) := by
  have hp := polynomiallyBounded_width hN
  unfold layerWidth
  fun_prop

theorem polynomiallyBounded_deciderGateCount {N : ℕ → ℕ} (hN : PolynomiallyBounded N) :
    PolynomiallyBounded (fun n => ((N n).size + 1) ^ 2 * layerWidth (N n)) := by
  have hd := polynomiallyBounded_size hN
  have hw := polynomiallyBounded_layerWidth hN
  fun_prop

end PredictionDepth.StandardComplexity.StandardPower
