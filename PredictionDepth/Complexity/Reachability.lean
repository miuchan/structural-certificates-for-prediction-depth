import PredictionDepth.CircuitInterop
import PredictionDepth.LinearSize

/-!
# Parallel Boolean relation powering

One matrix-square layer uses AND followed by balanced OR. Repeated squaring
therefore computes length-`2^k` walk existence with depth `k*(1+clog₂ n)` and
polynomial size. The machine-specific configuration graph and uniform circuit
serialization are separate constructions.
-/
namespace PredictionDepth.ParallelReachability
open FastComposition

abbrev Relation (n : ℕ) := Fin n → Fin n → Bool

def encode {n : ℕ} (R : Relation n) : Bits (n * n) :=
  fun p => R (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2

def index {n : ℕ} (i j : Fin n) : Fin (n * n) := finProdFinEquiv (i, j)

@[simp] theorem encode_index {n : ℕ} (R : Relation n) (i j : Fin n) :
    encode R (index i j) = R i j := by simp [encode, index]

def compose {n : ℕ} (R S : Relation n) : Relation n :=
  fun i j => boolOr n (fun k => R i k && S k j)

@[simp] theorem compose_true {n : ℕ} (R S : Relation n) (i j : Fin n) :
    compose R S i j = true ↔ ∃ k, R i k = true ∧ S k j = true := by
  simp [compose, boolOr]

def squares {n : ℕ} (R : Relation n) : ℕ → Relation n
  | 0 => R
  | k + 1 => compose (squares R k) (squares R k)

def Walk {n : ℕ} (R : Relation n) : ℕ → Fin n → Fin n → Prop
  | 0, i, j => i = j
  | t + 1, i, j => ∃ k, Walk R t i k ∧ R k j = true

theorem walk_add {n : ℕ} (R : Relation n) (a b : ℕ) (i j : Fin n) :
    Walk R (a + b) i j ↔ ∃ k, Walk R a i k ∧ Walk R b k j := by
  induction b generalizing j with
  | zero => simp [Walk]
  | succ b ih =>
    change (∃ l, Walk R (a + b) i l ∧ R l j = true) ↔
      ∃ k, Walk R a i k ∧ ∃ l, Walk R b k l ∧ R l j = true
    constructor
    · rintro ⟨l, hil, hlj⟩
      obtain ⟨k, hik, hkl⟩ := (ih l).mp hil
      exact ⟨k, hik, l, hkl, hlj⟩
    · rintro ⟨k, hik, l, hkl, hlj⟩
      exact ⟨l, (ih l).mpr ⟨k, hik, hkl⟩, hlj⟩

/-- Exact path-length semantics of repeated Boolean squaring. -/
theorem squares_true_iff_walk {n : ℕ} (R : Relation n) (k : ℕ) (i j : Fin n) :
    squares R k i j = true ↔ Walk R (2 ^ k) i j := by
  induction k generalizing i j with
  | zero => simp [squares, Walk]
  | succ k ih =>
    rw [pow_succ]
    have htwo : 2 ^ k * 2 = 2 ^ k + 2 ^ k := by omega
    rw [htwo, walk_add]
    simp only [squares, compose_true, ih]

/-- Self-loops pad any shorter walk to the chosen common power-of-two length. -/
theorem walk_mono_of_reflexive {n : ℕ} {R : Relation n} (hr : ∀ i, R i i = true)
    {a b : ℕ} (hab : a ≤ b) {i j : Fin n} (h : Walk R a i j) : Walk R b i j := by
  induction b, hab using Nat.le_induction with
  | base => exact h
  | succ b hab ih => exact ⟨j, ih, hr j⟩

theorem walk_detected_by_squares {n : ℕ} {R : Relation n} (hr : ∀ i, R i i = true)
    {t k : ℕ} (ht : t ≤ 2 ^ k) {i j : Fin n} (h : Walk R t i j) :
    squares R k i j = true :=
  (squares_true_iff_walk R k i j).mpr (walk_mono_of_reflexive hr ht h)

theorem walk_reachable {n t : ℕ} {R : Relation n} {i j : Fin n} (h : Walk R t i j) :
    Relation.ReflTransGen (fun a b => R a b = true) i j := by
  induction t generalizing j with
  | zero => cases h; exact .refl
  | succ t ih =>
    obtain ⟨k, hik, hkj⟩ := h
    exact (ih hik).tail hkj

theorem reachable_has_walk {n : ℕ} {R : Relation n} {i j : Fin n}
    (h : Relation.ReflTransGen (fun a b => R a b = true) i j) : ∃ t, Walk R t i j := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @tail j k h hstep ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t + 1, j, ht, hstep⟩

/-- A shortest directed walk has fewer edges than the number of vertices.
Distinct prefix lengths must reach distinct vertices: otherwise concatenating
the shorter prefix with the later suffix contradicts minimality. -/
theorem reachable_has_short_walk {n : ℕ} {R : Relation n} {i j : Fin n}
    (h : Relation.ReflTransGen (fun a b => R a b = true) i j) :
    ∃ t, t < n ∧ Walk R t i j := by
  classical
  have hex := reachable_has_walk h
  let d := Nat.find hex
  have hd : Walk R d i j := Nat.find_spec hex
  have split (k : Fin (d + 1)) : ∃ v, Walk R k.val i v ∧ Walk R (d - k.val) v j := by
    apply (walk_add R k.val (d - k.val) i j).mp
    simpa only [Nat.add_sub_of_le (show k.val ≤ d by omega)] using hd
  let mid (k : Fin (d + 1)) : Fin n := Classical.choose (split k)
  have hs (k : Fin (d + 1)) : Walk R k.val i (mid k) ∧ Walk R (d - k.val) (mid k) j :=
    Classical.choose_spec (split k)
  have hinj : Function.Injective mid := by
    intro a b hab
    apply Fin.ext
    have hab₁ : a.val ≤ b.val := by
      by_contra hn
      have hp : Walk R (b.val + (d - a.val)) i j :=
        (walk_add R b.val (d - a.val) i j).mpr
          ⟨mid b, (hs b).1, by simpa only [hab] using (hs a).2⟩
      have hm := Nat.find_min' hex hp
      change d ≤ b.val + (d - a.val) at hm
      omega
    have hab₂ : b.val ≤ a.val := by
      by_contra hn
      have hp : Walk R (a.val + (d - b.val)) i j :=
        (walk_add R a.val (d - b.val) i j).mpr
          ⟨mid a, (hs a).1, by simpa only [hab] using (hs b).2⟩
      have hm := Nat.find_min' hex hp
      change d ≤ a.val + (d - b.val) at hm
      omega
    omega
  have hcard := Fintype.card_le_of_injective mid hinj
  simp only [Fintype.card_fin] at hcard
  exact ⟨d, by omega, hd⟩

/-- At least `ceil(log₂ n)` squarings decide reflexive directed reachability. -/
theorem reachable_iff_squares {n : ℕ} {R : Relation n} (hr : ∀ i, R i i = true)
    {k : ℕ} (hn : n ≤ 2 ^ k) (i j : Fin n) :
    Relation.ReflTransGen (fun a b => R a b = true) i j ↔ squares R k i j = true := by
  constructor
  · intro h
    obtain ⟨t, ht, hw⟩ := reachable_has_short_walk h
    exact walk_detected_by_squares hr (by omega) hw
  · intro h
    exact walk_reachable ((squares_true_iff_walk R k i j).mp h)

def conjunctions {n : ℕ} (i j : Fin n) : BinaryCircuit (n * n) n :=
  Linear.Circuits.collect (fun k => .seq
    (BinaryCircuit.select ![index i k, index k j]) (.gate Bool.and))

@[simp] theorem conjunctions_eval {n : ℕ} (R : Relation n) (i j k : Fin n) :
    (conjunctions i j).eval (encode R) k = (R i k && R k j) := by
  rw [conjunctions, Linear.Circuits.collect_eval]
  simp [BinaryCircuit.eval, BinaryCircuit.select, Function.comp_def]

def squareCircuit (n : ℕ) : BinaryCircuit (n * n) (n * n) :=
  Linear.Circuits.collect (fun p => .seq
    (conjunctions (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
    (orCircuit n).toBinary)

theorem squareCircuit_correct {n : ℕ} (R : Relation n) :
    (squareCircuit n).eval (encode R) = encode (compose R R) := by
  funext p
  rw [squareCircuit, Linear.Circuits.collect_eval]
  simp only [BinaryCircuit.eval, BoundedCircuit.toBinary_eval, orCircuit_eval, encode, compose]
  congr 1
  funext k
  exact conjunctions_eval R _ _ k

theorem squareCircuit_depth_le (n : ℕ) :
    (squareCircuit n).depth ≤ 1 + Nat.clog 2 n := by
  apply Linear.Circuits.collect_depth_le
  intro p
  change (conjunctions _ _).depth + (orCircuit n).toBinary.depth ≤ _
  have hc : (conjunctions (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).depth ≤ 1 := by
    apply Linear.Circuits.collect_depth_le
    intro k
    exact le_rfl
  exact Nat.add_le_add hc (orCircuit n).toBinary_depth

theorem squareCircuit_gateCount_le (n : ℕ) :
    (squareCircuit n).gateCount ≤ (n * n) * (3 * n) := by
  apply Linear.Circuits.collect_gateCount_le
  intro p
  change (conjunctions _ _).gateCount + (orCircuit n).toBinary.gateCount ≤ _
  have hc : (conjunctions (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).gateCount ≤ n := by
    simpa only [conjunctions, Nat.mul_one] using
      Linear.Circuits.collect_gateCount_le _ (G := 1) (fun _ => le_rfl)
  rw [BoundedCircuit.toBinary_gateCount]
  have ho := orCircuit_linear_size n
  omega

theorem squareCircuit_descriptionSize_le (n : ℕ) :
    (squareCircuit n).descriptionSize ≤ (n * n) * (16 * n + 5) + 1 := by
  apply Linear.Circuits.collect_descriptionSize_le
  intro p
  change 1 + (conjunctions _ _).descriptionSize + (orCircuit n).toBinary.descriptionSize ≤ 16 * n + 4
  have hc : (conjunctions (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).descriptionSize ≤
      n * (5 + 1) + 1 :=
    Linear.Circuits.collect_descriptionSize_le _ (fun _ => le_rfl)
  rw [BoundedCircuit.toBinary_descriptionSize]
  have ho := orCircuit_linear_size n
  omega

/-- One shared relation matrix is passed between squaring stages. -/
def powerCircuit (n : ℕ) : ℕ → BinaryCircuit (n * n) (n * n)
  | 0 => BinaryCircuit.select id
  | k + 1 => .seq (powerCircuit n k) (squareCircuit n)

theorem powerCircuit_correct {n : ℕ} (R : Relation n) (k : ℕ) :
    (powerCircuit n k).eval (encode R) = encode (squares R k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (squareCircuit n).eval ((powerCircuit n k).eval (encode R)) = _
    rw [ih, squareCircuit_correct]
    rfl

theorem powerCircuit_depth_le (n k : ℕ) :
    (powerCircuit n k).depth ≤ k * (1 + Nat.clog 2 n) := by
  induction k with
  | zero => simp [powerCircuit, BinaryCircuit.select, BinaryCircuit.depth]
  | succ k ih =>
    simpa only [powerCircuit, BinaryCircuit.depth, Nat.succ_mul] using
      Nat.add_le_add ih (squareCircuit_depth_le n)

theorem powerCircuit_gateCount_le (n k : ℕ) :
    (powerCircuit n k).gateCount ≤ k * ((n * n) * (3 * n)) := by
  induction k with
  | zero => simp [powerCircuit, BinaryCircuit.select, BinaryCircuit.gateCount]
  | succ k ih =>
    simpa only [powerCircuit, BinaryCircuit.gateCount, Nat.succ_mul] using
      Nat.add_le_add ih (squareCircuit_gateCount_le n)

theorem powerCircuit_descriptionSize_le (n k : ℕ) :
    (powerCircuit n k).descriptionSize ≤
      (1 + n * n) + k * ((n * n) * (16 * n + 5) + 2) := by
  induction k with
  | zero => simp [powerCircuit, BinaryCircuit.select, BinaryCircuit.descriptionSize]
  | succ k ih =>
    change 1 + (powerCircuit n k).descriptionSize + (squareCircuit n).descriptionSize ≤ _
    have h := squareCircuit_descriptionSize_le n
    rw [Nat.succ_mul]
    omega

theorem reachability_depth_le (n : ℕ) :
    (powerCircuit n (Nat.clog 2 n)).depth ≤ (Nat.clog 2 n + 1) ^ 2 := by
  have h := powerCircuit_depth_le n (Nat.clog 2 n)
  nlinarith

end PredictionDepth.ParallelReachability
