# Dependencies, Models, and Trust Boundaries

**English** · [简体中文](../i18n/zh-CN/docs/dependencies.md) · [日本語](../i18n/ja/docs/dependencies.md) · [Esperanto](../i18n/eo/docs/dependencies.md)

The reproducible versions are pinned in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

| Dependency | Pinned version | Role |
| --- | --- | --- |
| Lean | `v4.36.0-rc2`, `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a` | Kernel checking of proof terms |
| cslib-frontier | `3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d` | Concrete complexity theory, Turing machine compilers, and circuit encodings |
| CSLib | `254e30e6d4299c51323aaeaf5f51a4763b375d4a` | Finite control, multitape Turing machines, and general computation models |
| Mathlib | `69552756cd8a2d2d48763cf7279fd814d6a1224d` | Mathematical foundations, matrices, finite sets, and natural-number logarithms |

The project imports third-party code through a pinned cslib-frontier commit and its dependency graph. CVP completeness, closure under logspace composition, and inclusion of NC in P are backed by proof terms. [cslib-frontier source](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d)

## Standard machine model

`PredictionDepth.StandardComplexity` uses multitape Turing machines with finite control, a fixed number of work tapes, and a binary alphabet. A step reads the current input and work-tape symbols, moves the heads, updates local symbols, and emits at most one symbol. The input is read-only. The output tape is append-only and the machine cannot read it.

Work space counts work-tape cells visited in the run prefix. `ComputableInLogSpace` requires halting and logarithmic work space. Polynomial time and polynomial output length are derived separately from a finite configuration bound.

The standard CVP uses circuit instances that carry a validity proof and have an injective binary encoding. Its P-hardness theorem quantifies over encoded source problems, including binary words under the identity encoding. It can therefore be used for the prediction language over all query words. Invalid prediction queries are explicitly rejected.

For uniform NC, one circuit family simultaneously satisfies correctness, size, depth, and concrete logspace generation. P is defined by actual polynomial-time machines. `NCClosure` proves closure under general logspace reductions with variable output length inside this project.

## Foundational results added in this project

- Uniform adjacency circuits for configuration graphs, a finite directed shortest-path bound, repeated squaring of Boolean relations, and squared-logarithmic depth.
- Streaming logspace batches of any polynomial length. The machine keeps the original input on its read-only tape and recomputes intermediate output symbols on demand.
- Concrete logspace generation of serial, parallel, hardwired, and streaming compositions of circuit blocks of varying sizes.
- `NL ⊆ uniform NC²`, `uniform NC ⊆ P`, closure under general logspace reductions, and exclusion of P-hard problems from uniform NC under `P ≠ NC`.

## What the checks establish

`scripts/check_imports.py` requires the default entry point to cover every project proof file. `lake build` compiles all project modules. `Audit.lean` selects declarations by their defining module, including auxiliary declarations that Lean generates in other namespaces. It checks transitive axiom dependencies and permits only `propext`, `Classical.choice`, and `Quot.sound`.

The pinned Lean toolchain and its kernel are part of the trust base. When a build imports cached Mathlib artifacts, those compiled artifacts also enter the trust base. A fresh rebuild from the pinned dependency sources with Lake's caches disabled removes reliance on the prebuilt dependency cache. The axiom audit checks logical dependencies. Assessing whether the formal definitions and assumptions express the intended prediction problem requires a separate statement review. [Build evidence and review procedure](verification.md) · [Formal scope](requirements.md)
