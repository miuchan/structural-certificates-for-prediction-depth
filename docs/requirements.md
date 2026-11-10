# Formal Scope

**English** · [简体中文](../i18n/zh-CN/docs/requirements.md) · [日本語](../i18n/ja/docs/requirements.md) · [Esperanto](../i18n/eo/docs/requirements.md)

The project proves structural certificates for dynamical-system prediction depth in Lean 4, including concrete machine models, CVP P-completeness, and uniform NC closure under reductions. The table records the certificates, complexity foundations, and examples. The default entry point covers every listed module.

| Requirement | Formal evidence | Status |
| --- | --- | --- |
| Discrete evolution and observation | `Dynamics.predict` and the OR automaton on the infinite integer lattice | Implemented |
| Bounded fan-in circuits with arbitrary wiring and sharing | `BoundedCircuit`, `LayeredNetwork`, `BinaryCircuit`, and semantic translations | Implemented |
| Input lengths, fixed size budgets, family uniformity, and depth | `Families.Policy`, `Admissible`, `RealizesProfile`, `intrinsicDepth`, standard `UniformNC`, and the concrete OR and A generators | Builds, with the scope of both models documented |
| A. Semantics, operation count, and compact intermediate representations for binary repeated squaring | `FastComposition` | Implemented |
| A. Predictor construction from primitive circuits and bounds on depth, gate count, and description size | `CompiledComposition.Implementation` | Implemented |
| A. Constraints on visited representations and executed compositions | `PathComposition`, including an example that separates path conditions from global conditions | Builds with Lean 4.36 |
| A. Infinite global state spaces with finite input windows | `EncodedPathComposition` | Builds with Lean 4.36 |
| A. Concrete logspace uniformity from primitive-family generators | `Complexity/UniformComposition`, including canonical time bits, composition of generators, and polynomial size | Lean 4.36 build and transitive axiom audit pass |
| Finite-field linear system example and polylogarithmic depth | `Linear`, `LinearSize` | Implemented |
| B. Unary time encoding, simulation reduction, and conditional hardness transfer | `Hardness.SimulationWitness` | Parameterized metatheorem implemented |
| Standard logspace reductions and compositional closure | `Complexity/Logspace.lean` connects concrete finite-tape machines and a verified recomputation compiler | Builds with Lean 4.36 |
| Standard CVP P-completeness | `Complexity/CVP.lean` connects the encoding, evaluation machine, and Turing machine tableau reduction | Lean 4.36 build and axiom audit pass |
| Standard complexity version of B | `Complexity/StandardHardness.lean` uses verified CVP hardness and closure | Builds with Lean 4.36 |
| Standard uniform NC and inclusion in P | `Complexity/UniformNC.lean` | Builds with Lean 4.36 |
| Uniform NC closure under arbitrary logspace reductions | `NCClosure`, with configuration graphs, parallel reachability, streaming batches, and variable-length output selection | Lean 4.36 build and axiom audit pass |
| Conditional hardness under separation of P and NC | `SimulationWitness.prediction_not_uniformNC` with explicit `P ≠ NC` assumption | Lean 4.36 build and axiom audit pass |
| Machine-level uniformity and exact optimal depth for the concrete OR family | `UniformOROptimal.exact_uniform_prediction` | Lean 4.36 build and axiom audit pass |
| C. Depth lower bounds from essential-variable counts and finite checkable witnesses | `DependencyWitness` and the circuit and network lower bounds | Implemented |
| Exact optimal depth and linear-size upper bound for the OR automaton | `ORAutomaton.exact_prediction_depth` | Implemented |
| Propagation lower bound for geometrically constrained predictors | `Geometry.local_layers` and the OR geometric lower bound | Implemented |
| Limits of dependency counting | `dependency_method_limit` | Implemented |
| Time zero, empty inputs, single inputs, and concrete linear examples | `Examples` | Implemented |
| Nonlinear frozen-control family, logarithmic depth, and uniform NC¹ | `FrozenPascal.GuardRules`, `FrozenPascal.UniformLanguage`, `FrozenPascal.LowerBound` | Lean 4.36 build and axiom audit pass |
| Constant-depth equivalence and per-time classification for frozen controls | `bounded_prediction_depth_iff` and the varying-guard lower bound in `FrozenPascal/Classification.lean`, and the binary-weight bounds in `FrozenPascal/HomogeneousPascal.lean` | [Verification](verification.md) |
| Exact per-time homogeneous Pascal depth | `homogeneousNativeXorPrediction_depth` and `homogeneous_prediction_deMorgan_exact_depth`, with matching lower bounds for the two gate bases | [Verification](verification.md) |
| Executable rule classification and concrete uniform classification | `classify_eq_iff`, `uniform_depth_classification`, `predictionLanguage_mem_uniformNC_zero_iff` | [Verification](verification.md) |
| Essential inputs and exact per-time depth for the transported-control comparison | `TransportedControl.lean`, `essential_prediction_iff`, `exact_prediction_depth`, `constant_depth_iff` | [Verification](verification.md) |
| Costed prediction task reduction and reflected-frame instance | `PredictionReduction.compile_depth`, `compile_size`, `compile_code_logspace`, `TransportedBranching.reduction`, `prediction_uniform` | [Direction and costs](#costed-prediction-task-reductions) |
| Coefficients for branching with additive control evolution | `AdditiveBranching.lean`, `trimmedParity_eq_sum`, `iterate_data` | Iteration formula checked in Lean |
| Ordered block summary compilation | `BlockSummary.compile_eval`, `compile_depth`, `compile_size`, `compile_code_logspace` | [Certificate obligations](#ordered-block-summary-certificates) |
| Finite template checks and summary obstructions | `recognize?`, `LocalLaws.observe_foldr`, `findCollision?_sound`, `width_lower_bound` | [Recognition and failure](#recognition-and-failure) |
| Shared compiler applied to additive control and OR prediction | `AdditiveBranching.predictionFamily_uniform`, `ORAutomaton.summaryFamily_uniform` | Logspace-uniform families with linear size and logarithmic depth |
| Project-wide strict build, transitive axiom audit, and negative regression | `scripts/check.sh`, `Audit.lean`, `scripts/check_audit.py`, `.github/workflows/lean.yml` | [Verification](verification.md) |

## Ordered block summary certificates

Choose an input encoding, an observation, and an ordered block decomposition. Supply a fixed summary width, a leaf map, an identity, and an associative merge. To connect the fold to dynamics, prove that the observation reads the summary and any declared context. One route proves the empty, singleton, and concatenation equations for a block specification. Another starts with a finite scan whose correctness for the observation has already been proved and checks a local forward simulation into the summary. [Semantic obligations](../PredictionDepth/BlockSummary.lean)

The compiler takes a bank of leaf circuits, a fixed merge circuit, a context circuit on the original input, and a fixed readout circuit. Identity padding permits a power-of-two bank. At each level it merges adjacent pairs and halves the active width. For $m$ leaves, put $d=\lceil\log_2 m\rceil$ and $P=2^d$, using $d=0$ at $m=0$. The depth of the generated circuit is bounded by

```math
\max\{d_{\rm init}+1+d(d_{\rm merge}+1),\ d_{\rm context}\}+d_{\rm read}.
```

The initialization includes the depth of any preprocessing composed before the parallel leaf bank. The extra layers normalize outputs for the actual serializer. With summary width $w$, the reduction adds at most $Pw+(P-1)(w\,s_{\rm merge}+w)$ gates to initialization, context, and readout. The factor $w$ accounts for the existing one-output bank implementation. With fixed width, constant-size leaves, and at most linear preprocessing and context costs, the total size is linear. The logspace theorem uses generators for the input length, schedule, leaf bank, and context. It emits the entire circuit code, including references across layers with different widths. Hardwired time or position labels must be generated within these hypotheses. [Circuit and resource theorems](../PredictionDepth/Complexity/BlockSummary.lean) · [Variable-width serialization](../PredictionDepth/Complexity/VariableChain.lean)

The additive model uses $T$ leaves with summary $\bigl(1+c_j,x_j,\binom Tj c_j\bigr)$ over $\mathbb F_2$ and readout $x_T+QV$. Its input interleaves $T$ control/data pairs followed by the terminal data bit. The Lucas mask is generated from the time and position. The same family rejects even input lengths and belongs to logspace-uniform NC¹. The existing OR automaton instantiates the same compiler using one bit and the OR merge. Its earlier exact-depth family remains available. [Additive instance](../PredictionDepth/AdditiveBranching/Summary.lean) · [OR instance](../PredictionDepth/ORAutomaton/Summary.lean) · [Blelloch's parallel prefix method](https://www.cs.cmu.edu/afs/cs.cmu.edu/project/scandal/public/papers/CMU-CS-90-190.html)

### Recognition and failure

`recognize?` takes a supplied finite evaluator and a proposed summary map. It checks the merge laws, the initial state, each one-symbol update, and the readout. The induction then covers all word lengths. The caller connects the evaluator to the chosen prediction task and supplies the circuit and generation witnesses. The OR instance executes this check. Interpret `none` as uncovered by the supplied template. Coverage for an entire rule family requires a separate completeness theorem, as in the frozen guard classifier. [Recognizer and induction](../PredictionDepth/BlockSummary.lean) · [Executable OR example](../PredictionDepth/ORAutomaton/Summary.lean)

`findCollision?` searches supplied left blocks and right contexts. A successful result certifies that two equal summaries give different observations in the same context. In additive control at $T=2$, the control pairs $10$ and $01$ have the same frozen endpoint statistics, yet differ on the middle data coefficient. More generally, $r$ pairwise distinguishable left blocks require at least $\lceil\log_2 r\rceil$ summary bits. This bound concerns a fixed cut and independent summary interface. Arbitrary circuit wiring can bypass that interface, for example by comparing corresponding bits directly in a two-string equality test. [Collision search and width theorem](../PredictionDepth/BlockSummary.lean) · [Additive witness](../PredictionDepth/AdditiveBranching/Summary.lean)

## Costed prediction task reductions

A reduction fixes source and target windows, a time map $\tau$, an input encoder $A_T$, and an output decoder $B_T$. Its semantic obligation is $P_T=B_T\circ Q_{\tau(T)}\circ A_T$. Composing the circuits adds the encoding and decoding depth and gate costs. The time-indexed serializer uses logspace generators for the source width, unary target time, both translation circuits, and the target predictor. The complete encoder code also bounds the target input width polynomially in the unary source time. Transferring uniformity to input-length indexing requires the corresponding length decoder. [Reduction theorems](../PredictionDepth/Complexity/PredictionReduction.lean)

This direction transfers upper bounds from $Q$ to $P$. A lower bound for $P$ constrains the cost of computing $Q$ plus the translations. To transfer a lower bound from $Q$ to $P$, supply a reverse reduction with controlled costs or an independent lower-bound proof. In the reflected-frame instance the input rewire and identity output have depth and gate cost zero. The rewire duplicates a control word into an unused slot, and its logspace generator is verified. Proposition 6 of Goles et al. studies a related transfer of communication complexity under cellular-automaton simulations. [Reflected-frame instance](../PredictionDepth/TransportedBranching.lean) · [Goles et al., §4.1](https://arxiv.org/pdf/0912.1777)
