# Theorem B. Simulation Reductions and Conditional Hardness

**English** · [简体中文](../i18n/zh-CN/docs/hardness.md) · [日本語](../i18n/ja/docs/hardness.md) · [Esperanto](../i18n/eo/docs/hardness.md)

The standard complexity layer is in `PredictionDepth/Complexity/Logspace.lean`, `CVP.lean`, and `StandardHardness.lean`, under `PredictionDepth.StandardComplexity`. `PredictionDepth/Hardness.lean` contains the generic auxiliary theorems and unary query encoding.

## Standard complexity layer

`StandardComplexity.Logspace` uses CSLib multitape Turing machines with finite control and a binary alphabet. Input is read-only, output is append-only, and work space counts visited work-tape cells. `logspace_comp` invokes a verified recomputation compiler. When the second machine requests a symbol of the intermediate result, the compiler reruns the first machine to recover it without storing the entire intermediate string.

`CVP.lean` uses concrete De Morgan circuits, input assignments, and an injective binary encoding. The imported theorem `cvp_logSpaceComplete` proves P-completeness by a polynomial-time machine tableau circuit and a logspace serializer. The standard-layer theorems use this result and proved reduction closure directly.

`StandardComplexity.SimulationWitness` requires the following data for a concrete dynamical system.

1. Map each valid CVP instance to a simulation time and encoded initial state.
2. Prove that a logspace machine generates the **complete unary-time query**.
3. Prove that the observation at the simulation time equals the circuit output.

`SimulationWitness.prediction_P_hard` derives `LogSpaceHard @Cslib.Complexity.P`. A machine proof that the target prediction language belongs to P gives `prediction_P_complete`. The theorems `time_polynomial` and `payload_length_polynomial` derive polynomial bounds on the time field and payload length from the logspace query generator.

The CVP instance type carries validity proofs. The P-hardness theorem quantifies over all source encodings, including every binary word under `encBits`. The reduction always produces a valid CVP instance at its intermediate step. The target prediction language is defined on all binary words and rejects malformed queries, so the hardness result is for a language.

The standard machine foundation comes from cslib-frontier commit `3c44ce0b`. Lean compiles the dependency sources together with project code. The parallel complexity modules connect this foundation to uniform NC and the conditional non-membership theorem. [Pinned cslib-frontier source](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d)

## Generic auxiliary layer

The `PredictionDepth.Hardness` layer can be reused for other reduction classes. Its parameterized theorems separate the following obligations.

1. `encodeQuery t x = 1^t 0 x` is a binary query with unary time. `decode_encodeQuery` and `encode_decodeQuery` prove the round-trip laws, and `encodeQuery_injective` proves unambiguity. `decoded_time_le_length` bounds the decoded time by the query length. Malformed queries are rejected.
2. `predictionProblem F observe decodeState` computes `observe ((F^[t]) (decodeState x))` on valid queries. The state decoder maps the payload into the system's state space.
3. `SimulationWitness` contains the input encoding, simulation time, polynomial bounds for both, and a proof that the observation equals the source answer for every input. `query_length_polynomial` combines the bounds for the complete unary query.
4. Given admissibility of the full query generator, `SimulationWitness.reduction` constructs a many-one reduction. Its correctness follows from the simulation semantics.
5. `Reduction.trans` composes reductions. `prediction_P_hard` transfers source hardness to prediction. A P membership proof then gives `prediction_P_complete`.
6. `prediction_not_NC` excludes the target from a chosen parallel class when the class is contained in P, closed under the chosen reductions, and different from P. It yields class exclusion under the separation hypothesis.

## Definitions and explicit hypotheses

`InP` uses Mathlib's `Turing.TM2ComputableInPolyTime` with the binary word itself as input and one Boolean bit as output. It also requires each stack alphabet to be finite, because `FinTM2` guarantees only the input stack alphabet in its structure fields. `FinTM2` supplies finite labels, finite control, and finitely many stacks. The module uses its own proved bridge for the auxiliary machine model, independent of `TM2ComputableInPolyTime.comp`.

In `TM2.Stmt` and `stepAux`, each instruction's function reads finite control and at most one stack-top symbol. Each label has finite instruction syntax and there are finitely many labels. Counting `step` therefore bounds work in the intended machine model. `stack_InP_implies_standard_P` in `Complexity/StackMachineBridge.lean` embeds the auxiliary witness in standard P using a proved TM2-to-multitape simulation.

| Auxiliary-layer parameter | Intended standard instance | Treatment in the standard layer |
| --- | --- | --- |
| `ReductionSystem.Admissible` with identity and composition | Total logspace transductions | `Complexity/Logspace.lean` supplies the concrete machines and proved closure |
| `hencode` | Logspace generation of the complete query, including unary time | The concrete simulation must supply this witness |
| `hsource : PHard S source` | P-hardness of the chosen CVP encoding | `Complexity/CVP.lean` uses the verified machine-tableau reduction |
| `ParallelClassAssumptions S NC` | Inclusion of logspace-uniform NC in P and reduction closure | `UniformNC`, `UniformReachability`, and `NCClosure` supply the definitions and proofs |

`prediction_P_complete` also explicitly requires `hP`, a finite-alphabet polynomial-time machine proof for the target language. For a fixed finite-neighborhood cellular automaton with unary time, this is usually proved by direct step-by-step simulation. The witness belongs to the concrete rule.

The reduction needs a polynomial bound on its output query length. The complete simulation trajectory's space bound comes from the analysis of the concrete system. `payload_polynomial` bounds the encoded initial state length. Locality, gate gadgets, channels, synchronization, and crossings can be used to prove `simulation_correct` and `hencode`. The transfer theorem uses the resulting semantic and reduction witnesses.

Use `StandardComplexity.SimulationWitness` for standard P-hardness and P-completeness. Its theorems use concrete logspace machines and verified CVP completeness. All system-specific obligations are visible in the Lean types via `#check`.

## References

Richard E. Ladner established logspace P-completeness of circuit value in *The Circuit Value Problem Is Log Space Complete for P*, SIGACT News 7(1), 18–20, 1975. [Author's publication list](https://homes.cs.washington.edu/~ladner/papers.html)

Greenlaw, Hoover, and Ruzzo discuss P-completeness, NC reductions, hardness transfer, and the P versus NC question in *Limits to Parallel Computation: P-Completeness Theory*, especially the chapters on reductions and circuit value. The literature provides the mathematical background, and the proof terms in this repository and its dependencies provide the machine checks. [Book](https://homes.cs.washington.edu/~ruzzo/papers/limits.pdf)
