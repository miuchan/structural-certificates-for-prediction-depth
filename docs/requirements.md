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
| A. Concrete logspace uniformity from primitive-family generators | `Complexity/UniformComposition`, including canonical time bits, composition of generators, and polynomial size | Lean 4.36 build and independent axiom audit pass |
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
| Executable rule classification and concrete uniform classification | `classify_eq_iff`, `uniform_depth_classification`, `predictionLanguage_mem_uniformNC_zero_iff` | [Verification](verification.md) |
| Project-wide strict build, transitive axiom audit, and negative regression | `scripts/check.sh`, `Audit.lean`, `scripts/check_audit.py`, `.github/workflows/lean.yml` | [Verification](verification.md) |
