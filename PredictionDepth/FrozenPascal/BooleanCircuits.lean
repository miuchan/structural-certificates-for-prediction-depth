import PredictionDepth.FrozenPascal.Semantics
import PredictionDepth.Complexity.UniformOROptimal
import CslibFrontier.Computability.Circuit.Boolean.CarrySave

/-! Small Boolean circuit combinators for the frozen-control decoder. -/

namespace PredictionDepth.FrozenPascal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open FastComposition
open Linear (F₂)
open scoped BigOperators

abbrev Gates := Circuit signature

@[simp] theorem bit_ofBoolRing (v : F₂) : bit (ofBoolRing v) = v := by
  obtain ⟨b, rfl⟩ := (@toBoolRing Bool).surjective v
  cases b <;> rfl

theorem bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact congrArg ofBoolRing h

@[simp] theorem bit_and (a b : Bool) : bit (a && b) = bit a * bit b := by
  cases a <;> cases b <;> simp

@[simp] theorem bit_xor (a b : Bool) : bit (a ^^ b) = bit a + bit b := by
  cases a <;> cases b <;> rfl

def wireBit {n : ℕ} (i : Fin n) : Gates n 1 :=
  Circuit.wiring signature (fun _ => i)

def constBit (n : ℕ) (b : Bool) : Gates n 1 :=
  Circuit.oneGate (σ := signature) (.const b) Fin.elim0

def andGate : Gates 2 1 := Circuit.oneGate (σ := signature) .and id

def xorGate : Gates 2 1 :=
  ((Formula.input (n := 2) 0).xor (.input 1)).toCircuit

@[simp] theorem wireBit_eval {n : ℕ} (i : Fin n) (x : Bits n) :
    (wireBit i).eval interpretation x 0 = x i := rfl

@[simp] theorem constBit_eval (b : Bool) (x : Bits n) :
    (constBit n b).eval interpretation x 0 = b := rfl

@[simp] theorem andGate_eval (x : Bits 2) :
    andGate.eval interpretation x 0 = (x 0 && x 1) := rfl

@[simp] theorem xorGate_eval (x : Bits 2) :
    xorGate.eval interpretation x 0 = (x 0 ^^ x 1) := by
  simp [xorGate]

@[simp] theorem andGate_depth : andGate.depth = 1 := Circuit.depth_oneGate _ _
@[simp] theorem andGate_size : andGate.size = 1 := rfl
@[simp] theorem xorGate_depth : xorGate.depth = 3 := by decide +kernel
@[simp] theorem xorGate_size : xorGate.size = 5 := by decide +kernel

@[simp] theorem wireBit_depth (i : Fin n) : (wireBit i).depth = 0 := Circuit.depth_wiring _
@[simp] theorem wireBit_size (i : Fin n) : (wireBit i).size = 0 := rfl
@[simp] theorem constBit_depth (n : ℕ) (b : Bool) : (constBit n b).depth = 1 :=
  Circuit.depth_oneGate _ _
@[simp] theorem constBit_size (n : ℕ) (b : Bool) : (constBit n b).size = 1 := rfl

def conjoin (a b : Gates n 1) : Gates n 1 := andGate.comp (a.append b)

@[simp] theorem conjoin_eval (a b : Gates n 1) (x : Bits n) :
    (conjoin a b).eval interpretation x 0 =
      (a.eval interpretation x 0 && b.eval interpretation x 0) := by
  rw [conjoin, Circuit.eval_comp, Circuit.eval_append, andGate_eval]
  rfl

theorem conjoin_depth (a b : Gates n 1) :
    (conjoin a b).depth ≤ 1 + max a.depth b.depth :=
  (Circuit.depth_comp_le _ _).trans (Nat.add_le_add (by simp) (Circuit.depth_append_le _ _))

@[simp] theorem conjoin_size (a b : Gates n 1) : (conjoin a b).size = a.size + b.size + 1 := rfl

def parity (cs : List (Gates n 1)) : Gates n 1 :=
  Circuit.balanced xorGate (constBit n false) cs

def conjunction (cs : List (Gates n 1)) : Gates n 1 :=
  Circuit.balanced andGate (constBit n true) cs

theorem parity_eval (cs : List (Gates n 1)) (x : Bits n) :
    bit ((parity cs).eval interpretation x 0) =
      (cs.map fun c => bit (c.eval interpretation x 0)).sum := by
  rw [parity, Circuit.eval_balanced]
  have hh (a b : Bits 1) :
      bit (xorGate.eval interpretation (Fin.append a b) 0) = bit (a 0) + bit (b 0) := by
    rw [xorGate_eval]
    change bit (a 0 ^^ b 0) = _
    exact bit_xor _ _
  rw [List.balancedFold_hom (fun u : Bits 1 => bit (u 0)) hh]
  change cs.balancedFold (· + ·) (0 : F₂) (fun c => bit (c.eval interpretation x 0)) = _
  rw [List.balancedFold_eq_foldr]
  rfl

theorem conjunction_eval (cs : List (Gates n 1)) (x : Bits n) :
    bit ((conjunction cs).eval interpretation x 0) =
      (cs.map fun c => bit (c.eval interpretation x 0)).prod := by
  rw [conjunction, Circuit.eval_balanced]
  have hh (a b : Bits 1) :
      bit (andGate.eval interpretation (Fin.append a b) 0) = bit (a 0) * bit (b 0) :=
    bit_and _ _
  rw [List.balancedFold_hom (fun u : Bits 1 => bit (u 0)) hh]
  change cs.balancedFold (· * ·) (1 : F₂) (fun c => bit (c.eval interpretation x 0)) = _
  rw [List.balancedFold_eq_foldr]
  rfl

theorem parity_depth (cs : List (Gates n 1)) (D : ℕ) (hD : 1 ≤ D)
    (hc : ∀ c ∈ cs, c.depth ≤ D) :
    (parity cs).depth ≤ D + 3 * Nat.clog 2 cs.length := by
  simpa [parity] using Circuit.depth_balanced_le xorGate (constBit n false) hc (fun _ => by simpa)

theorem conjunction_depth (cs : List (Gates n 1)) (D : ℕ) (hD : 1 ≤ D)
    (hc : ∀ c ∈ cs, c.depth ≤ D) :
    (conjunction cs).depth ≤ D + Nat.clog 2 cs.length := by
  simpa [conjunction] using Circuit.depth_balanced_le andGate (constBit n true) hc (fun _ => by simpa)

theorem parity_size (cs : List (Gates n 1)) :
    (parity cs).size ≤ 1 + (cs.map Circuit.size).sum + cs.length * 5 := by
  simpa [parity] using Circuit.size_balanced_le xorGate (constBit n false) cs

theorem conjunction_size (cs : List (Gates n 1)) :
    (conjunction cs).size ≤ 1 + (cs.map Circuit.size).sum + cs.length := by
  simpa [conjunction] using Circuit.size_balanced_le andGate (constBit n true) cs

theorem parity_eval_fin (cs : Fin m → Gates n 1) (x : Bits n) :
    bit ((parity (List.ofFn cs)).eval interpretation x 0) =
      ∑ j, bit ((cs j).eval interpretation x 0) := by
  rw [parity_eval, List.map_ofFn, List.sum_ofFn]
  rfl

theorem conjunction_eval_fin (cs : Fin m → Gates n 1) (x : Bits n) :
    bit ((conjunction (List.ofFn cs)).eval interpretation x 0) =
      ∏ j, bit ((cs j).eval interpretation x 0) := by
  rw [conjunction_eval, List.map_ofFn, List.prod_ofFn]
  rfl

theorem parity_depth_fin (cs : Fin m → Gates n 1) (D : ℕ) (hD : 1 ≤ D)
    (hc : ∀ j, (cs j).depth ≤ D) :
    (parity (List.ofFn cs)).depth ≤ D + 3 * Nat.clog 2 m := by
  simpa only [List.length_ofFn] using parity_depth (List.ofFn cs) D hD (by
    intro c h
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    exact hc j)

theorem conjunction_depth_fin (cs : Fin m → Gates n 1) (D : ℕ) (hD : 1 ≤ D)
    (hc : ∀ j, (cs j).depth ≤ D) :
    (conjunction (List.ofFn cs)).depth ≤ D + Nat.clog 2 m := by
  simpa only [List.length_ofFn] using conjunction_depth (List.ofFn cs) D hD (by
    intro c h
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    exact hc j)

theorem parity_size_fin (cs : Fin m → Gates n 1) (G : ℕ)
    (hc : ∀ j, (cs j).size ≤ G) : (parity (List.ofFn cs)).size ≤ 1 + m * (G + 5) := by
  have h := parity_size (List.ofFn cs)
  have hsum : ∑ j : Fin m, (cs j).size ≤ m * G := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hc j)
  rw [List.map_ofFn, List.sum_ofFn, List.length_ofFn] at h
  simp only [Function.comp_apply] at h
  simp only [Nat.mul_add]
  omega

theorem conjunction_size_fin (cs : Fin m → Gates n 1) (G : ℕ)
    (hc : ∀ j, (cs j).size ≤ G) : (conjunction (List.ofFn cs)).size ≤ 1 + m * (G + 1) := by
  have h := conjunction_size (List.ofFn cs)
  have hsum : ∑ j : Fin m, (cs j).size ≤ m * G := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hc j)
  rw [List.map_ofFn, List.sum_ofFn, List.length_ofFn] at h
  simp only [Function.comp_apply] at h
  simp only [Nat.mul_add, Nat.mul_one]
  omega

end PredictionDepth.FrozenPascal
