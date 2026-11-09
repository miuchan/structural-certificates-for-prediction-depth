import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Simulation witnesses and hardness transfer

The semantic reduction and unary resource bounds are proved here. Sequential
polynomial time is defined using actual finite-alphabet TM2 machines. The class
of admissible reductions, its closure under composition, the hardness of the
source problem (usually CVP), and the standard closure/inclusion facts for NC
are explicit parameters. In particular this file does not declare an axiom
that CVP is complete, or call an arbitrary function "logspace computable".
-/

namespace PredictionDepth.Hardness

abbrev Word := List Bool
abbrev DecisionProblem := Word → Bool

/-- Actual sequential polynomial-time decidability. All stack alphabets must
be finite; mathlib's bundled `FinTM2` by itself asserts this only for input. -/
def InP (A : DecisionProblem) : Prop :=
  ∃ c : Turing.TM2ComputableInPolyTime (id : Word → Word) (fun b : Bool => [b]) A,
    ∀ k, Finite (c.tm.Γ k)

/-- An explicitly supplied class of admissible maps. Instantiate with total
logspace transducers once their machine semantics and closure are available. -/
structure ReductionSystem where
  Admissible : (Word → Word) → Prop
  identity_admissible : Admissible id
  compose_admissible : ∀ f g, Admissible f → Admissible g → Admissible (g ∘ f)

/-- A many-one reduction carrying its map and a semantic proof for every word. -/
structure Reduction (S : ReductionSystem) (A B : DecisionProblem) where
  map : Word → Word
  admissible : S.Admissible map
  correct : ∀ x, B (map x) = A x

namespace Reduction

def refl (S : ReductionSystem) (A : DecisionProblem) : Reduction S A A :=
  ⟨id, S.identity_admissible, fun _ => rfl⟩

def trans {S : ReductionSystem} {A B C : DecisionProblem}
    (f : Reduction S A B) (g : Reduction S B C) : Reduction S A C where
  map := g.map ∘ f.map
  admissible := S.compose_admissible _ _ f.admissible g.admissible
  correct x := (g.correct (f.map x)).trans (f.correct x)

end Reduction

def PHard (S : ReductionSystem) (A : DecisionProblem) : Prop :=
  ∀ B, InP B → Nonempty (Reduction S B A)

def PComplete (S : ReductionSystem) (A : DecisionProblem) : Prop :=
  InP A ∧ PHard S A

theorem hard_of_reduction {S : ReductionSystem} {A B : DecisionProblem}
    (hA : PHard S A) (r : Reduction S A B) : PHard S B := by
  intro C hC
  obtain ⟨q⟩ := hA C hC
  exact ⟨q.trans r⟩

theorem complete_of_reduction {S : ReductionSystem} {A B : DecisionProblem}
    (hA : PHard S A) (r : Reduction S A B) (hB : InP B) : PComplete S B :=
  ⟨hB, hard_of_reduction hA r⟩

/-- Only these standard properties of a proposed parallel class are used in
the conditional obstruction. They are hypotheses, not a definition of NC. -/
structure ParallelClassAssumptions (S : ReductionSystem) (NC : DecisionProblem → Prop) : Prop where
  included_in_P : ∀ A, NC A → InP A
  closed_under_reduction : ∀ A B, Reduction S A B → NC B → NC A

theorem hard_in_parallel_implies_eq {S : ReductionSystem}
    {NC : DecisionProblem → Prop} (hNC : ParallelClassAssumptions S NC)
    {A : DecisionProblem} (hA : PHard S A) (hparallel : NC A) : InP = NC := by
  funext B
  apply propext
  constructor
  · intro hB
    obtain ⟨r⟩ := hA B hB
    exact hNC.closed_under_reduction B A r hparallel
  · exact hNC.included_in_P B

/-- Conditional no-NC consequence. This proves no numerical linear-depth bound. -/
theorem hard_not_parallel {S : ReductionSystem} {NC : DecisionProblem → Prop}
    (hNC : ParallelClassAssumptions S NC) (hne : InP ≠ NC)
    {A : DecisionProblem} (hA : PHard S A) : ¬ NC A := by
  intro h
  exact hne (hard_in_parallel_implies_eq hNC hA h)

/-- Time is encoded in unary, before a zero delimiter and an arbitrary payload. -/
def encodeQuery (time : ℕ) (payload : Word) : Word :=
  List.replicate time true ++ false :: payload

def decodeQuery : Word → Option (ℕ × Word)
  | [] => none
  | false :: xs => some (0, xs)
  | true :: xs => (decodeQuery xs).map (fun p => (p.1 + 1, p.2))

@[simp] theorem decode_encodeQuery (time : ℕ) (payload : Word) :
    decodeQuery (encodeQuery time payload) = some (time, payload) := by
  induction time with
  | zero => rfl
  | succ t ih =>
    simpa [encodeQuery, List.replicate_succ, decodeQuery] using
      congrArg (Option.map (fun p : ℕ × Word => (p.1 + 1, p.2))) ih

@[simp] theorem encodeQuery_length (time : ℕ) (payload : Word) :
    (encodeQuery time payload).length = time + 1 + payload.length := by
  simp only [encodeQuery, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem encodeQuery_injective : Function.Injective (fun p : ℕ × Word => encodeQuery p.1 p.2) := by
  intro p q h
  have := congrArg decodeQuery h
  simpa using this

/-- Successful decoding recovers the entire query, not just a prefix. -/
theorem encode_decodeQuery {query : Word} {time : ℕ} {payload : Word}
    (h : decodeQuery query = some (time, payload)) : encodeQuery time payload = query := by
  induction query generalizing time payload with
  | nil => simp [decodeQuery] at h
  | cons b xs ih =>
    cases b with
    | false =>
      have hp : (0, xs) = (time, payload) := Option.some.inj h
      cases hp
      rfl
    | true =>
      simp only [decodeQuery, Option.map_eq_some_iff] at h
      obtain ⟨⟨t, p⟩, ht, hp⟩ := h
      cases hp
      simpa [encodeQuery, List.replicate_succ] using congrArg (List.cons true) (ih ht)

/-- Unary time is at most the input length for every valid query. -/
theorem decoded_time_le_length {query : Word} {time : ℕ} {payload : Word}
    (h : decodeQuery query = some (time, payload)) : time ≤ query.length := by
  rw [← encode_decodeQuery h, encodeQuery_length]
  omega

/-- Invalid queries are rejected; valid queries predict an explicitly decoded state. -/
def predictionProblem {X : Type*} (F : X → X) (observe : X → Bool)
    (decodeState : Word → X) (query : Word) : Bool :=
  match decodeQuery query with
  | none => false
  | some (time, payload) => observe ((F^[time]) (decodeState payload))

@[simp] theorem predictionProblem_encode {X : Type*} (F : X → X) (observe : X → Bool)
    (decodeState : Word → X) (time : ℕ) (payload : Word) :
    predictionProblem F observe decodeState (encodeQuery time payload) =
      observe ((F^[time]) (decodeState payload)) := by
  simp [predictionProblem]

/-- A conventional pointwise polynomial upper bound with an explicit input size. -/
def PolynomiallyBounded (f : Word → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ x, f x ≤ c * (x.length + 1) ^ k

theorem polynomial_unary_query_length {time : Word → ℕ} {payload : Word → Word}
    (ht : PolynomiallyBounded time)
    (hp : PolynomiallyBounded (fun x => (payload x).length)) :
    PolynomiallyBounded (fun x => (encodeQuery (time x) (payload x)).length) := by
  obtain ⟨ct, kt, ht⟩ := ht
  obtain ⟨cp, kp, hp⟩ := hp
  refine ⟨ct + cp + 1, kt + kp, ?_⟩
  intro x
  have hb : 1 ≤ x.length + 1 := by omega
  have htPow : (x.length + 1) ^ kt ≤ (x.length + 1) ^ (kt + kp) :=
    Nat.pow_le_pow_right hb (by omega)
  have hpPow : (x.length + 1) ^ kp ≤ (x.length + 1) ^ (kt + kp) :=
    Nat.pow_le_pow_right hb (by omega)
  have hOne : 1 ≤ (x.length + 1) ^ (kt + kp) := Nat.one_le_pow _ _ hb
  have h₁ := (ht x).trans (Nat.mul_le_mul_left ct htPow)
  have h₂ := (hp x).trans (Nat.mul_le_mul_left cp hpPow)
  dsimp only
  rw [encodeQuery_length]
  nlinarith

/-- The data and semantic equality to verify for a simulation. The complexity
of writing the complete unary query is a separate, explicit obligation. -/
structure SimulationWitness {X : Type*} (F : X → X) (observe : X → Bool)
    (decodeState : Word → X) (source : DecisionProblem) where
  time : Word → ℕ
  payload : Word → Word
  time_polynomial : PolynomiallyBounded time
  payload_polynomial : PolynomiallyBounded (fun x => (payload x).length)
  simulation_correct : ∀ x,
    observe ((F^[time x]) (decodeState (payload x))) = source x

namespace SimulationWitness

variable {X : Type*} {F : X → X} {observe : X → Bool}
  {decodeState : Word → X} {source : DecisionProblem}

def query (w : SimulationWitness F observe decodeState source) (x : Word) : Word :=
  encodeQuery (w.time x) (w.payload x)

theorem query_length_polynomial (w : SimulationWitness F observe decodeState source) :
    PolynomiallyBounded (fun x => (w.query x).length) :=
  polynomial_unary_query_length w.time_polynomial w.payload_polynomial

theorem query_correct (w : SimulationWitness F observe decodeState source) (x : Word) :
    predictionProblem F observe decodeState (w.query x) = source x := by
  simpa [query] using w.simulation_correct x

/-- Theorem B's constructed reduction. Its correctness is derived from simulation. -/
def reduction (w : SimulationWitness F observe decodeState source)
    (S : ReductionSystem) (hencode : S.Admissible w.query) :
    Reduction S source (predictionProblem F observe decodeState) :=
  ⟨w.query, hencode, w.query_correct⟩

/-- For CVP, supply its standard P-hardness theorem as `hsource`. -/
theorem prediction_P_hard (w : SimulationWitness F observe decodeState source)
    (S : ReductionSystem) (hencode : S.Admissible w.query) (hsource : PHard S source) :
    PHard S (predictionProblem F observe decodeState) :=
  hard_of_reduction hsource (w.reduction S hencode)

theorem prediction_P_complete (w : SimulationWitness F observe decodeState source)
    (S : ReductionSystem) (hencode : S.Admissible w.query) (hsource : PHard S source)
    (hP : InP (predictionProblem F observe decodeState)) :
    PComplete S (predictionProblem F observe decodeState) :=
  ⟨hP, w.prediction_P_hard S hencode hsource⟩

theorem prediction_not_NC (w : SimulationWitness F observe decodeState source)
    (S : ReductionSystem) (hencode : S.Admissible w.query) (hsource : PHard S source)
    {NC : DecisionProblem → Prop} (hNC : ParallelClassAssumptions S NC)
    (hne : InP ≠ NC) : ¬ NC (predictionProblem F observe decodeState) :=
  hard_not_parallel hNC hne (w.prediction_P_hard S hencode hsource)

end SimulationWitness
end PredictionDepth.Hardness
