# Structural Certificates for Prediction Depth

**English** · [简体中文](i18n/zh-CN/README.md) · [日本語](i18n/ja/README.md) · [Esperanto](i18n/eo/README.md)

The research question is which verifiable structural conditions on a dynamical system yield bounds on the circuit depth of predicting an observation. A prediction problem fixes the evolution, observation, input encoding, and allowed circuits. Lean 4 checks three reusable criteria for these problems.

The current paper by Amamiya Miu classifies a family of one-sided cellular automata with frozen controls that can vary across sites. The order of hops is fixed, so a hop conjunction and a stay count suffice to summarize the paths to each endpoint. A binary no-carry test detects which path counts are odd. Evolving-control examples show which summaries survive uniform motion and which need to change when the controls themselves branch. English is the primary edition. [Related work](docs/literature.md)

| Paper language | PDF | Typst source |
| --- | --- | --- |
| English | [PDF](paper/structural-certificates.pdf) | [Source](paper/structural-certificates.typ) |
| 简体中文 | [PDF](paper/structural-certificates.zh-CN.pdf) | [Source](paper/structural-certificates.zh-CN.typ) |
| 日本語 | [PDF](paper/structural-certificates.ja.pdf) | [Source](paper/structural-certificates.ja.typ) |
| Esperanto | [PDF](paper/structural-certificates.eo.pdf) | [Source](paper/structural-certificates.eo.typ) |

## Depth classification for frozen controls

Fix a control-word width $q$ and two guards, stay and hop. The input explicitly gives the control words and data bits at sites $0,\ldots,T$. A legal input has length $n=(q+1)(T+1)$, which determines $T$. The lower bounds apply to circuits of fan-in at most two with arbitrary wiring and sharing. The upper bounds are realized by De Morgan circuits.

| Guard condition | Prediction depth |
| --- | --- |
| Hop is always off | Constant depth. At positive times, the output uses only the stay guard and data bit at the origin. |
| Hop is always on and stay is always off | Depth zero. Read the data bit at site $T$. |
| Hop varies, or hop is always on and stay varies | $\Theta(\log(T+1))$. At least $T+1$ inputs are essential, including in the AND/OR guard example. |
| Stay and hop are always on | Let $p$ be the number of ones in the binary expansion of $T$. Minimum depth is $p$ with native XOR and $2p+1$ with De Morgan gates at positive times, counting a NOT gate as one layer. Time zero needs depth zero. The verified uniform De Morgan family uses at most $3p$ layers. |

`classify` traverses the finite control alphabet by prefix. Each constancy test stops at its first counterexample and avoids allocating the full list of words. An exhaustive test can still visit $`2^q`$ words. `classify_eq_iff` proves the equivalence between the returned branch and its condition. For each fixed pair of guards, `uniform_depth_classification` gives a single logspace-uniform, polynomial-size family realizing the appropriate upper bound, including the $`3p`$ bound for homogeneous Pascal. The prediction language is in uniform NC⁰ exactly in the first two cases. [Frozen-control model and proof](docs/frozen-pascal.md)

## Structural comparison with transported controls

Fix $`u,v\in\{0,1\}`$. Each step updates the control and data tracks by $`c'_i=c_{i+u}`$ and $`d'_i=c_i\land d_{i+v}`$. The input explicitly lists both tracks at sites $`0,\ldots,T`$. At time zero the output is a data wire of depth zero. At positive times, equal velocities make the output depend on one initial control bit and one data bit, giving exact depth 1. With unequal velocities it depends on $`T`$ initial control bits and one data bit, giving exact depth $`\lceil\log_2(T+1)\rceil`$. Lean constructs a linear-size AND tree and proves a matching lower bound for fan-in-two circuits with sharing. These are per-time bounds for a single-path conjunction rule. Both tracks can move while retaining constant depth, provided they move together. [Transported-control semantics and depth](PredictionDepth/TransportedControl.lean)

With both stay and hop branches available, uniformly translating the controls allows a reflected moving frame that freezes the controls and exchanges the two guards. Lean checks the change of frame and the per-time reduction by input rewiring. For additive control evolution $`c'_i=c_i+c_{i+1}`$ and data update $`x'_i=c_i x_i+x_{i+1}`$ over $`\mathbb F_2`$, Lean verifies a replacement coefficient formula using shared Pascal parity and suffix-zero tests. [Reflected-frame reduction](PredictionDepth/TransportedBranching.lean) · [Additive-control coefficients](PredictionDepth/AdditiveBranching.lean)

## Reusable block summary certificates

The ordered summary compiler turns fixed-width leaf summaries, an associative merge with identity, and a readout into a single circuit family. Its resource bounds include preprocessing, the context circuit, and copy gates. For additive control, a three-bit summary and the final data wire give a verified linear-size, logarithmic-depth uniform predictor. The existing OR model uses the same compiler with a one-bit summary. Its finite local recognizer checks a supplied scan template and yields a proof for every word length. [Certificate obligations and limits](docs/requirements.md#ordered-block-summary-certificates) · [Additive predictor](PredictionDepth/AdditiveBranching/Summary.lean) · [OR predictor](PredictionDepth/ORAutomaton/Summary.lean)

## Formal infrastructure

The three certificates compile resource-bounded primitive circuits into a predictor (A), transfer P-hardness through a logspace simulation reduction (B), and turn essential-input counts into unconditional bounded-fan-in depth lower bounds (C). The standard complexity layer connects concrete Turing machines, completeness of the Circuit Value Problem (CVP), and closure of uniform NC under reductions. An OR automaton illustrates exact depth and geometric constraints. Binary-field matrices illustrate composition costs. [Formal scope](docs/requirements.md) · [Dependencies and machine models](docs/dependencies.md) · [Verification](docs/verification.md)

## Reproduction

The project pins Lean `v4.36.0-rc2` and locks all dependencies in `lake-manifest.json`. The standard complexity foundation comes from commit `3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d` of cslib-frontier. Its dependency graph pins the CSLib and Mathlib versions. [cslib-frontier source](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d)

```sh
lake exe cache get  # Optional dependency build cache
./scripts/check.sh
```

`scripts/check.sh` checks coverage of the default entry point, runs a strict build, audits transitive axiom dependencies, and runs a negative regression test. The audit selects declarations by their defining project module and permits only Lean's `propext`, `Classical.choice`, and `Quot.sound`. GitHub Actions runs the same script for the triggering commit. [Verification procedure](docs/verification.md)

Use Typst 0.15.1 to rebuild the English PDF from the repository root with bundled fonts.

```sh
typst compile --ignore-system-fonts --creation-timestamp 1794268800 \
  paper/structural-certificates.typ paper/structural-certificates.pdf
```

To rebuild all four editions, place the static SC and JP Regular and Bold OTFs in a font directory. The required names are `NotoSerifCJKsc-Regular.otf`, `NotoSerifCJKsc-Bold.otf`, `NotoSerifCJKjp-Regular.otf`, and `NotoSerifCJKjp-Bold.otf`. [Noto Serif CJK 2.003](https://github.com/notofonts/noto-cjk/releases/tag/Serif2.003)

```sh
./scripts/build-papers.sh /path/to/cjk-fonts
```

GitHub Actions rebuilds all four editions from the checked-out revision. Use a full commit SHA in the PDF and source links to cite the exact revision. [Paper rebuild and permalinks](docs/verification.md#paper-rebuild)

## Core theorems and code

| Result | Module and main declarations |
| --- | --- |
| Evolution, observation, and composition of local maps | `Dynamics.lean`, `predict`, `Geometry.Local.comp`, `local_layers` |
| Bounded fan-in circuits, shared DAGs, and dependency lower bounds | `Circuit.lean`, `essential_count_le_pow`, `DependencyWitness` |
| Exact semantics and operation count for repeated squaring | `FastComposition.lean`, `compile_exponent`, `compile_operations`, `fast_prediction_correct` |
| A. Compiling a predictor from concrete primitive circuits | `EncodedPathComposition.lean`, `EncodedPathImplementation.compiled_predictor_correct` and its resource bounds. `CompiledComposition.lean` covers the globally correct special case. |
| A. Concrete uniform generators and standard NC consequences | `Complexity/UniformComposition.lean`, `UniformRegisterWitness.uniform`, `depth_le_costs`, `mem_uniformNCLevel_of_cost` |
| Semantic connection between circuit representations | `CircuitInterop.lean`, `BinaryCircuit.unfoldOutput_eval` |
| Exact optimal depth for the OR automaton | `ORAutomaton.lean`. `exact_uniform_prediction` in `Complexity/UniformOROptimal.lean` also gives a concrete uniform generator. |
| Fixed input lengths, size budgets, family constraints, and depth | `Families.lean`, `Policy`, `Admissible`, `RealizesProfile`, `intrinsicDepth` |
| Concrete circuits for binary-field matrices | `Linear.lean`, `LinearSize.lean` |
| B. Parameterized simulation and reduction metatheorems | `Hardness.lean`. [Scope of the hardness results](docs/hardness.md) |
| B. Concrete machines and the standard CVP foundation | `Complexity/Logspace.lean`, `CVP.lean`, `StandardHardness.lean` |
| Standard NC closure and the conditional obstacle to parallel prediction | `Complexity/NCClosure.lean`, `uniformNC_closed_logspace`, `SimulationWitness.prediction_not_uniformNC` |
| Parallel reachability, uniform NC², and streaming generation | `Complexity/Reachability.lean`, `UniformReachability.lean`, `LogspaceBatch.lean` |
| Limit of dependency counting | `DependencyGrowth.lean`, `dependency_method_limit` |
| One-sided frozen-control rules | `iterate_data` in `FrozenPascal/Semantics.lean` and `predictionLanguage_mem_uniformNC_one` in `FrozenPascal/UniformLanguage.lean` |
| Frozen-control depth classification | `bounded_prediction_depth_iff` and `varyingGuard_prediction_depth_lower_bound` in `FrozenPascal/Classification.lean`, and `pascalSupport_card` and the binary-weight depth bounds in `FrozenPascal/HomogeneousPascal.lean` |
| Exact homogeneous Pascal depth | `homogeneousNativeXorPrediction_depth` in `FrozenPascal/HomogeneousPascal.lean` and `homogeneous_prediction_deMorgan_exact_depth` in `FrozenPascal/PascalExactDepth.lean` |
| Executable classifier and uniform depth classification | `classify_eq_iff` in `FrozenPascal/Classification.lean`, and `uniform_depth_classification` and `predictionLanguage_mem_uniformNC_zero_iff` in `FrozenPascal/UniformClassification.lean` |
| Essential inputs and exact depth for transported controls | `TransportedControl.lean`, `iterate_data_true_iff`, `essential_prediction_iff`, `exact_prediction_depth`, `constant_depth_iff` |
| Branching with transported controls | `TransportedBranching.lean`, `reverseFrame_iterate`, `prediction_correct`, `prediction_depth`, `prediction_size` |
| Coefficient formula for branching with additive control evolution | `AdditiveBranching.lean`, `trimmedParity_eq_sum`, `iterate_data` |
| Executable boundary and example checks | `Examples.lean` |

### A. Efficiently composable representations

`Realization` requires the identity representation, one-step representation, and composition operation to agree with their function semantics. `compile T` is an executable binary repeated-squaring program. Squaring reuses existing registers, and the number of composition operations is at most

```math
2\lceil\log_2(T+1)\rceil.
```

`EncodedPathImplementation` supplies a width-`L` bit encoding and concrete binary Boolean circuits for initialization, composition, and observation. Correctness of composition is required along the executed path, so unvisited representations may lie outside the width-`L` encoding. The global state space can be infinite, with a specified map from the finite input bit string into that space. The compiler proves that the output is $`O(F^T(\mathrm{input}(x)))`$ and that

```math
d_{\rm pred}\le d_{\rm init}
 +2\lceil\log_2(T+1)\rceil d_{\rm comp}+d_{\rm obs}.
```

The gate count follows the same additive bound. A separate description-size bound includes the wiring and composition syntax. Initialization costs are explicit. The encoding only needs to preserve enough information for the requested observation and may be non-injective. The stronger global `Implementation` converts to the path-based form.

The uniform variant `UniformRegisterWitness` derives a logspace generator and polynomial size for the complete predictor family from concrete logspace generators for canonical binary time and four primitive circuit families. The generator rereads indexed time bits, keeping the possibly large numerical value of $`T`$ off its work tapes. The compiler normalizes output wires to a consecutive range, charging a copy layer per stage.

```math
d_{\rm uniform}\le\eta+1+
2\lceil\log_2(T+1)\rceil(\delta+1)+\epsilon.
```

When $`\delta\ge1`$, the bound simplifies to $`\eta+1+4\lceil\log_2(T+1)\rceil\delta+\epsilon`$. Standard uniform NC membership requires the complete cost to be polylogarithmic in the **actual input length**. A logspace generator for the binary time string only handles one part of that requirement.

`Linear.implementation` encodes each binary-field element in one bit. Parallel AND layers and balanced XOR reductions implement matrix multiplication and give the bound

```math
d(T,n)\le
2\lceil\log_2(T+1)\rceil(\lceil\log_2 n\rceil+1)
 +(\lceil\log_2 n\rceil+1).
```

Both gate count and full description size have explicit polynomial bounds. When $`n\le(T+1)^k`$, the finite bound is

```math
d(T,n)\le3(k+1)(\lceil\log_2(T+1)\rceil+1)^2.
```

To apply the uniform certificate, supply concrete generators and semantic witnesses for the primitives and the initial matrix family. Linearity of each matrix alone does not supply a uniform generator for the family.

### B. Hardness from simulation

A prediction query is encoded as $`1^T0x`$. The development proves the encoding and decoding laws, injectivity, rejection of malformed queries, and a bound on the full query length. A simulation witness maps each circuit instance to an initial state and time and proves that the prediction equals the circuit value on every instance.

`Hardness` provides a reusable parameterized version. `Complexity/StandardHardness` uses concrete finite multitape Turing machines, actual logspace transducers, and standard CVP completeness, which discharge the source hardness and reduction closure premises. P-completeness also requires a proof that the specified system's prediction language belongs to P.

`NCClosure` proves closure of uniform NC under general logspace reductions, including those whose output lengths depend on the input contents. With a simulation witness and the explicit assumption $`P\ne NC`$, the prediction language lies outside uniform NC. This is a class exclusion, with no specific numerical depth rate.

### C. Lower bounds from input dependence

An input is essential if two assignments that agree off its coordinate produce different outputs. For fan-in at most `b` and depth at most `d`, the formal bounds on the number `m` of essential inputs are

```math
m\le b^d,\qquad
\lceil\log_b m\rceil\le d\quad(b\ge2).
```

`DependencyWitness` supplies a finite set of coordinates and a distinguishing pair for each. The proof covers layered DAGs with arbitrary sharing. It unfolds the circuit to prove the lower bound, where the resulting formula can be exponentially larger.

### OR automaton and geometric constraints

On the integer lattice, define $`F(x)_i=x_{i-1}\lor x_i\lor x_{i+1}`$. The development proves

```math
F^T(x)_0=\bigvee_{j=-T}^{T}x_j,
\qquad D(T)=\lceil\log_2(2T+1)\rceil.
```

The input has exactly `2*T+1` bits, and its extension outside the interval is irrelevant. The core model supplies an optimal-depth, linear-size formula. The standard layer also constructs a logspace-uniform family of optimal-depth De Morgan circuits with $`n\lceil\log_2 n\rceil`$ gates, within a fixed quadratic budget. The matching lower bound covers all shared-wiring De Morgan circuits. Both constructions have depth zero at $`T=0`$.

One update is a three-input OR, which takes a constant number of gate layers to implement with binary gates. Physical rounds and binary circuit layers are distinct units.

When each predictor layer has spatial radius at most `r`, an essential input at distance $`T`$ forces $`T\le d\,r`$. This hypothesis constrains the predictor's wiring. Circuits with unrestricted wiring satisfy the logarithmic depth bound above.

## Mathematical scope

- `Nat.clog` gives an integer ceiling logarithm and covers zero and singleton inputs. Real-logarithm asymptotics apply in the positive-parameter range.
- `intrinsicDepth` fixes input lengths, the size constant and exponent, and admissibility of the entire family. It takes the value infinity when there is no admissible family. The pointwise infimum can select different families at different times. An asymptotic algorithm claim uses `RealizesProfile` to require one family for the entire depth profile.
- The structural `BinaryCircuit.depth` is a proved depth upper bound. Optimality requires a matching lower bound.
- A, B, and C are sufficient certificates. Lean checks the constructions and semantic proofs supplied by the caller. Finding witnesses for arbitrary rules is a separate algorithmic problem.
- B requires a complete simulation witness for the concrete system. P-completeness additionally requires P membership. The class separation assumption yields exclusion from uniform NC.
- In a light cone of polynomial size, C gives at most a logarithmic counting bound. The frozen-control lower bounds concern fan-in-two circuits. NC¹ completeness would require an additional NC¹-hardness proof under an appropriate reduction.

For the additive-control example the all-hop coefficient is always one, which lets the other coefficients share a single parity factor. The next boundary is to allow the evolving control to gate the hops too and determine when the coefficient recurrence still admits a compact summary.

The axiom audit follows project theorems' transitive dependencies into the third-party complexity foundation. The definitions, theorem statements, and verification guide support review of the model and its assumptions. [Trust boundaries](docs/dependencies.md)
