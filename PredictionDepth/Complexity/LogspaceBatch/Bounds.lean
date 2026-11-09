import PredictionDepth.Complexity.LogspaceBatch.Components
import PredictionDepth.Complexity.LogspaceBatch.Semantics

/-! Logarithmic storage of the real native configurations and batch counters. -/

namespace PredictionDepth.StandardComplexity.LogspaceBatch

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Turing.VirtualWord

theorem virtual_length_bound (C d n j : ℕ) (hj : j ≤ count C d n) :
    2 * n + 1 + j + 1 ≤ (C + 3) * (n + 1) ^ (d + 1) := by
  have hpow : (n + 1) ^ d ≤ (n + 1) ^ (d + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ n + 1)
      (show 1 ≤ d + 1 by omega)
  have hj' := hj.trans (Nat.mul_le_mul_left C hpow)
  nlinarith

theorem log_succ_le_binary_length (m : ℕ) : Nat.log2 m + 1 ≤ (encNat (m + 1)).length := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.succ_le_iff, Nat.lt_size]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact (Nat.log2_self_le hm.ne').trans (Nat.le_succ m)

theorem native_configuration_bound {α : Type} {enc : α ↪ List Bool}
    {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ) (tm : MultiTapeTM k Bool S)
    (c C d : ℕ)
    (hspace : ∀ a j, tm.RunsInSpace (encPair enc encUnary (a, j))
      (c * (Nat.log2 (encPair enc encUnary (a, j)).length + 1))) :
    ∃ K, ∀ a j, j ≤ count C d (enc a).length → ∀ t,
      (eCfg ((Native.machine (desc eS eBit tm)).run
        (frame (enc a) ++ List.replicate j true) t)).length ≤
        K * (Nat.log2 (enc a).length + 1) := by
  let D := desc eS eBit tm
  let A := Nat.size (C + 3) + 2 * (d + 1) + 1
  let B := 3 * (2 * descLen D + 5) * 2
  refine ⟨(2 * descLen D + 4 + k) + 2 * A + B * c * A, ?_⟩
  intro a j hj t
  let w := frame (enc a) ++ List.replicate j true
  have hw : w.length + 1 ≤ (C + 3) * ((enc a).length + 1) ^ (d + 1) := by
    simpa only [w, List.length_append, length_frame, List.length_replicate] using
      virtual_length_bound C d (enc a).length j hj
  have hlen : (encNat (w.length + 1)).length ≤ A * (Nat.log2 (enc a).length + 1) :=
    length_encNat_le_of_le_mul_pow hw
  have hlog : Nat.log2 w.length + 1 ≤ A * (Nat.log2 (enc a).length + 1) :=
    (log_succ_le_binary_length w.length).trans hlen
  have hs : tm.RunsInSpace w (c * (Nat.log2 w.length + 1)) := by
    simpa only [encPair_apply, encUnary_apply] using hspace a j
  have hnative := Native.length_native_run_le_of_space eS tm w t
    (c * (Nat.log2 w.length + 1)) hs
  change _ ≤ 2 * descLen D + 3 + 2 * (encNat (w.length + 1)).length + 1 +
    B * (c * (Nat.log2 w.length + 1)) + k at hnative
  have hb := Nat.mul_le_mul_left (B * c) hlog
  have hl := Nat.mul_le_mul_left 2 hlen
  have hbase : 1 ≤ Nat.log2 (enc a).length + 1 := by omega
  dsimp only [w] at hnative
  nlinarith

theorem state_encoding_length (phase : Bool) (n j : ℕ) (q : SCfg) :
    (encState (phase, n, j, q)).length =
      5 + 2 * (encNat n).length + 2 * (encNat j).length + (eCfg q).length := by
  simp only [encState, length_encPair, encBool_apply, List.length_singleton]
  omega

theorem saved_states_bound {α : Type} {enc : α ↪ List Bool} (D : Desc) (C d K : ℕ)
    (hcfg : ∀ a j, j ≤ count C d (enc a).length → ∀ t,
      (eCfg ((Native.machine D).run (frame (enc a) ++ List.replicate j true) t)).length ≤
        K * (Nat.log2 (enc a).length + 1)) :
    ∃ L, ∀ a,
      (∀ i ≤ (enc a).length, (encState (scanState D i)).length ≤
        L * (Nat.log2 (enc a).length + 1)) ∧
      (∀ j ≤ count C d (enc a).length, ∀ t,
        (encState (itemState (enc a).length j
          ((Native.machine D).run (frame (enc a) ++ List.replicate j true) t))).length ≤
          L * (Nat.log2 (enc a).length + 1)) := by
  let J := Nat.size C + 2 * d + 1
  refine ⟨7 + 2 * J + K, ?_⟩
  intro a
  have hlogpos : 1 ≤ Nat.log2 (enc a).length + 1 := by omega
  constructor
  · intro i hi
    have hi' := length_encNat_le_log2 hi
    have hc := hcfg a 0 (Nat.zero_le _) 0
    simp only [QueryMachine.run_zero, Native.machine] at hc
    rw [scanState, state_encoding_length]
    rw [show (encNat 0).length = 0 from rfl]
    nlinarith
  · intro j hj t
    have hn := length_encNat_le_log2 (le_refl (enc a).length)
    have hj' : (encNat j).length ≤ J * (Nat.log2 (enc a).length + 1) :=
      length_encNat_le_of_le_mul_pow hj
    have hc := hcfg a j hj t
    rw [itemState, state_encoding_length]
    nlinarith

end PredictionDepth.StandardComplexity.LogspaceBatch
