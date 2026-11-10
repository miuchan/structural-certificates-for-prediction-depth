# One-Sided Cellular Automata with Frozen Controls

**English** · [简体中文](../i18n/zh-CN/docs/frozen-pascal.md) · [日本語](../i18n/ja/docs/frozen-pascal.md) · [Esperanto](../i18n/eo/docs/frozen-pascal.md)

## Model and input

Fix a control-word width $`q`$ and two Boolean guards $`s,h:\{0,1\}^q\to\{0,1\}`$. Each site $`i\in\mathbb Z`$ has a control word $`a_i`$ and a data bit $`x_i\in\mathbb F_2`$. The synchronous update is

```math
a_i'=a_i,\qquad x_i'=s(a_i)x_i+h(a_i)x_{i+1}.
```

Control words are part of the initial state and can be chosen independently at each site. Once the control configuration is fixed, the data track evolves linearly. The joint rule can be non-affine. For instance, take $`s=\mathrm{AND}`$ and $`h=\mathrm{OR}`$. On the restriction $`x_{i+1}=0`$, the coefficient of $`x_i`$ still varies with $`a_i`$, whereas an affine function would have a fixed coefficient. The control track stays fixed and the data track can change.

A time-$`T`$ query supplies the initial states at sites $`0,\ldots,T`$ explicitly. The encoding lists the $`T+1`$ control words followed by their data bits. The legal lengths are $`n=(q+1)(T+1)`$, so $`T=n/(q+1)-1`$ is determined by length. A legal word is accepted when $`x_0(T)=1`$. Empty words and lengths that do not form whole cells are rejected. For fixed $`q`$, logarithmic depth in $`T+2`$ is also logarithmic in the total input length. A succinct initial state with a separate binary time field would require a different input model. [Window semantics](../PredictionDepth/FrozenPascal/Window.lean) · [Input encoding](../PredictionDepth/FrozenPascal/GuardRules.lean) · [Prediction language](../PredictionDepth/FrozenPascal/UniformLanguage.lean)

## Classification theorem

Fix $`q`$ and De Morgan guard circuits computing $`s,h`$, with depths $`d_s,d_h`$. Circuits permit arbitrary wiring and sharing of intermediate results. Let $`p=\operatorname{popcount}(T)`$ count the ones in the binary expansion of $`T`$, and let $`\ell(v)=\lceil\log_2 v\rceil`$. At each legal time, every correct Boolean circuit of fan-in at most two satisfies the lower bound in the table. For each fixed rule, one logspace-uniform, polynomial-size De Morgan family realizes the upper bound and decides the entire language, including rejection of malformed lengths. [Uniform classification theorem](../PredictionDepth/FrozenPascal/UniformClassification.lean)

| Semantic condition on the fixed rule | Depth lower bound | Uniform depth upper bound |
| --- | --- | --- |
| $`h\equiv 0`$ | $`0`$ | $`1+d_s`$ |
| $`h\equiv 1,\ s\equiv 0`$ | $`0`$ | $`0`$ |
| $`h`$ is nonconstant, or $`h\equiv 1`$ and $`s`$ is nonconstant | $`\ell(T+1)`$ | $`104(\ell(T+3)+1)+\max(d_s,d_h)`$ |
| $`h\equiv 1,\ s\equiv 1`$ | $`p`$ | $`3p`$ |

Every fixed rule therefore has a logspace-uniform NC¹ prediction language, and precisely the first two cases are in uniform NC⁰. The third case has matching logarithmic bounds at positive times. The fourth has depth at most three at $`2^r`$ and at least $`r`$ at $`2^r-1`$, so a single constant cannot bound all times. At $`T=0`$, the actual minimum is zero in all four cases because the output is the input wire $`x_0(0)`$. [Uniform NC¹](../PredictionDepth/FrozenPascal/UniformLanguage.lean) · [Uniform NC⁰ equivalence](../PredictionDepth/FrozenPascal/UniformClassification.lean)

## Coefficient formula

Expand $`x_0(T)`$ as a linear combination of the initial data bits. Let $`s_k=\sum_{i=0}^{k}s(a_i)`$ be the integer count of enabled stay positions and $`e_k=\prod_{i=0}^{k-1}h(a_i)`$ the product of the first $`k`$ hop flags, with empty product $`1`$. Then

```math
x_0(T)=\sum_{k=0}^T e_k\,\operatorname{multichoose}(s_k,T-k)\,x_k(0)
\qquad\text{in }\mathbb F_2.
```

A contributing path from site $`k`$ to the origin makes exactly $`k`$ leftward hops. It traverses the same edges in order, giving the common factor $`e_k`$. The remaining $`r=T-k`$ steps are distributed among the sites where staying is enabled, including the endpoints. The order of sites is fixed, so each allocation of stays determines one path. For $`s_k>0`$ there are $`\binom{s_k+r-1}{r}`$ paths. For $`s_k=0`$ there is one path if $`r=0`$ and none otherwise. Reducing the path count modulo $`2`$ gives the coefficient. `iterate_data` proves the coefficient recurrence and connects it to the actual iteration on the infinite lattice. [Coefficient recurrence and `iterate_data`](../PredictionDepth/FrozenPascal/Semantics.lean)

For example, let $`T=3`$, take stay flags $`(1,0,1,0)`$, and enable the first three hops. A contribution from site $`2`$ requires one stay, which may occur at site $`0`$ or $`2`$. The two paths cancel in $`\mathbb F_2`$, leaving $`x_0(3)=x_0(0)\oplus x_1(0)\oplus x_3(0)`$.

## Parallel algorithm

For a given input length, the generator already knows $`T`$. The circuit evaluates both guards at each site in parallel and then computes the following quantities in parallel for every $`0\le k\le T`$.

1. Compute $`e_k`$ with a balanced AND tree and count the first $`k+1`$ stay flags with a carry-save addition tree. Each round compresses groups of three binary rows into two at constant depth. After $`O(\log(T+2))`$ rounds, two rows remain. A final carry-propagating addition still costs only $`O(\log(T+2))`$ depth, even with a linear-depth adder in the bit width.
2. Select $`\operatorname{multichoose}(s_k,T-k)\bmod 2`$ from the count $`s_k`$. For candidate $`v>0`$, the bit is set exactly when adding $`v-1`$ and $`T-k`$ causes no binary carry. By Lucas's theorem this is equivalent to every set bit of $`T-k`$ appearing in $`v+T-k-1`$, the test used by the verified generator. For $`v=0`$, the coefficient is one exactly when $`T=k`$. The circuit tests $`s_k=v`$ for the candidates with a set coefficient.
3. Multiply the coefficient bit by $`e_k`$ and $`x_k(0)`$ and combine all terms with a balanced XOR tree. A fixed-depth De Morgan circuit implements each binary XOR.

Each stage has depth $`O(\log(T+2))`$, and using a separate subcircuit for every prefix still gives polynomial size. The coefficient formula reduces spacetime transfer coefficients to prefix counts, hop flags, and parities of combinatorial coefficients. [Counting circuits](../PredictionDepth/FrozenPascal/UniformWeight.lean) · [Lucas bit test](../PredictionDepth/FrozenPascal/CoefficientBits.lean) · [Coefficient selection and reduction](../PredictionDepth/FrozenPascal/UniformDecoder.lean)

## Lean construction and logspace uniformity

The algorithm can be organized directly for a fixed time. The Lean construction connects the same decoder to the generic path compiler, showing how to reuse the resource-bounded composition interface. Its abstract representation interprets $`u`$ as the $`u`$-fold iterate and composes by adding times. The circuit stores guard flags, data bits, and a one-hot time tag within the window. Initialization sets the tag at position $`0`$. Squaring doubles the position, and multiplication by the seed increments it. The decoder uses the tag to select one row of coefficients across possible times. The time representation and wiring implement composition and row selection. The speedup from frozen controls comes from the decoder's coefficient formula. `no_global_decoder` identifies the boundary of the tag encoding. In a window of at least two cells, there are fixed initial data for which two out-of-range times share an all-zero tag but give different outputs. [Path witness](../PredictionDepth/FrozenPascal/PathWitness.lean) · [Out-of-range separation](../PredictionDepth/FrozenPascal/Separation.lean)

The separate per-time construction `guardedPrediction` has explicit resource bounds. If $`g_s,g_h`$ are the two guard gate counts, its depth and gate count are bounded respectively by

```math
7+33\lceil\log_2(T+2)\rceil+\max(d_s,d_h),\qquad
113(T+2)^4+(T+1)(g_s+g_h).
```

The construction `uniformGuardedPrediction` has its own logspace generator. Instantiating it with `UniformWeight.basis` gives the following depth bound at legal times.

```math
104\bigl(\lceil\log_2(T+3)\rceil+1\bigr)+\max(d_s,d_h).
```

From the read-only unary input $`1^n`$, the generator checks legality and determines $`T`$. It generates the counting layers, coefficient entries, reduction trees, and tag wiring with logarithmic-width indices. The counting circuit compresses the four rows of two tree nodes into two rows to simplify uniform wiring. The coefficient parity is generated by scanning binary digits, with short indices and local computation state on work tapes. The formal proof composes the block serializers into one halting multitape transducer that emits the entire circuit code, including gate types, predecessor indices, and output indices. Its output-length bound implies polynomial family size. `predictionLanguage_mem_uniformNC_one` combines correctness, depth, size, and the generator in one circuit family. [Per-time resource bounds](../PredictionDepth/FrozenPascal/GuardRules.lean) · [Generator and depth bound](../PredictionDepth/FrozenPascal/UniformPrediction.lean) · [Space bound for coefficient bits](../PredictionDepth/FrozenPascal/CoefficientUniform.lean) · [Definition of uniform NC](../PredictionDepth/Complexity/UniformNC.lean)

## Matching depth lower bound

Suppose there are control words $`a_{\rm on},a_{\rm off}`$ with

```math
(s(a_{\rm on}),h(a_{\rm on}))=(1,1),\qquad
(s(a_{\rm off}),h(a_{\rm off}))=(0,1).
```

Put $`a_{\rm on}`$ at the origin and $`a_{\rm off}`$ at all other sites. This gives $`e_k=1`$ and $`s_k=1`$ for every $`k`$, so prediction is parity of $`T+1`$ data bits. With controls fixed, flipping any one data bit flips the result. The original prediction function therefore has at least $`T+1`$ essential inputs. The backwards cone of a depth-$`d`$ fan-in-two circuit covers at most $`2^d`$ inputs, even with arbitrary wiring and sharing. Hence

```math
d\ge \lceil\log_2(T+1)\rceil.
```

For AND/OR guards, choose $`a_{\rm on}=(1,1)`$ and $`a_{\rm off}=(1,0)`$. Together with the upper bound, this gives asymptotically optimal $`\Theta(\log(T+2))`$ depth for fan-in-two circuits as $`T`$ grows. [General lower bound and AND/OR example](../PredictionDepth/FrozenPascal/LowerBound.lean)

## Proof by regime

`classify` tests control words by prefix, stopping each constancy test at its first counterexample. An exhaustive test can still visit $`2^q`$ words. `classify_eq_iff` verifies the returned branch, and `guard_depth_cases` verifies that the four branches cover all fixed guard pairs. For example, when $`s\equiv1`$, deciding whether depth stays constant is equivalent to deciding whether the hop circuit $`h`$ is unsatisfiable. [Classifier and bounded-depth characterization](../PredictionDepth/FrozenPascal/Classification.lean)

If $`h\equiv0`$, the output at positive times is $`s(a_0)x_0(0)`$, so the stay guard and one AND gate suffice. If $`h\equiv1,s\equiv0`$, output the wire $`x_T(0)`$ at zero depth and zero gates. [Constant-depth constructions](../PredictionDepth/FrozenPascal/Classification.lean)

If $`h`$ is nonconstant, set the data bits so that only $`x_T(0)=1`$. The output is $`e_T`$, because the furthest input can reach the origin only along the all-hop path. Any two control words are connected by single-bit flips on the Boolean cube, so a nonconstant $`h`$ changes value along some edge. At each of the first $`T`$ sites, that edge witnesses an essential control bit when all other hop flags are enabled. Enabling all hops also makes $`x_T(0)`$ essential. This forces depth at least $`\lceil\log_2(T+1)\rceil`$. If $`h\equiv1`$ and $`s`$ is nonconstant, the parity restriction above gives the same bound. [Lower bound for varying guards](../PredictionDepth/FrozenPascal/Classification.lean)

The lower bound depends on fan-in. For $`s\equiv0, h(a)=a`$ with a one-bit control, prediction is $`x_T(0)\land a_0\land\cdots\land a_{T-1}`$. Binary gates require logarithmic depth. An unbounded-fan-in AND gate computes it in one layer.

If both guards are identically $`1`$, the coefficients reduce to $`\binom{T}{k}\bmod 2`$. Let $`p=\operatorname{popcount}(T)`$. The $`2^p`$ odd coefficients correspond to submasks of $`T`$, so the output is parity of those data bits. Lean proves exact depth $`p`$ with native XOR gates. With De Morgan gates and NOT counted as one layer, the optimum is zero at time zero and $`2p+1`$ at positive times. For $`r\ge2`$, the De Morgan minimum drops from $`2r+1`$ at $`T=2^r-1`$ to three at $`T=2^r`$. The separate per-time balanced XOR construction still gives the explicit gate count $`5(2^p-1)`$. [Support and native XOR depth](../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) · [Exact De Morgan depth](../PredictionDepth/FrozenPascal/PascalExactDepth.lean) · [Classical odd-coefficient count, Rowland §1](https://arxiv.org/pdf/1001.1783)

The pointwise De Morgan proof reuses circuit unfolding, Khrapchenko's parity leaf bound, and conversion to negation normal form from the pinned cslib-frontier dependency. The new lower-bound step shows that a formula attaining the full binary leaf bound computes a monotone function, which rules out depth $`2p`$ for parity when $`p>0`$. Certifying a uniform family that attains $`2p+1`$ would additionally require a new regular serializer. A two-output parity network would emit both polarities at each stage, with a layer for negated inputs and new reference and depth invariants for the two outputs. The existing single-output serializer certifies $`3p`$. [Khrapchenko (1971)](https://www.mathnet.ru/eng/mzm9639) · [Verified uniform reducer](../PredictionDepth/FrozenPascal/UniformXor.lean)

## Realizing the uniform family

`classifiedPrediction` selects the generator from the fixed rule's classification. The rule is fixed at family definition time, and the generator varies with input length. The no-hop and shift generators emit the complete codes of their specialized circuits, preserving their constant-depth and zero-gate bounds, respectively. Varying guards use the generic path circuit. The homogeneous Pascal generator scans $`k\le T`$, emits wires for odd coefficients using the submask test, and reduces only those inputs. [No-hop and shift generators](../PredictionDepth/FrozenPascal/UniformLocal.lean) · [Pascal generator](../PredictionDepth/FrozenPascal/UniformHomogeneous.lean)

The uniform Pascal reducer uses $`p`$ rounds of fixed-width parallel XOR, with three De Morgan layers per round. This permits direct streaming of the round composition and gives depth $`3p`$ and gate count $`5p2^p`$. Since $`2^p\le T+1`$, the gate count grows at most on the order of $`T\log(T+2)`$. The per-time balanced tree above uses fewer gates. The uniform classification uses the fixed-width construction. [XOR reduction and encoding](../PredictionDepth/FrozenPascal/UniformXor.lean)

## Scope and formal statement map

On an explicit $`n`$-bit input, the essential-input count can give at most the lower bound $`\ell(n)`$. For a polynomial-volume light cone in fixed dimension, counting alone thus yields at most a logarithmic bound in $`T`$. The upper bounds here cover one-sided frozen-control rules and a single output site. The prediction language includes the whole initial window, and the generator receives the input length in unary. The standard P-hardness framework uses a different query encoding with a unary time field. It requires a concrete simulation and a logspace reduction generating the full query. [Limit of dependency counting](../PredictionDepth/DependencyGrowth.lean) · [Obligations for hardness](hardness.md)

| Claim | Lean declaration |
| --- | --- |
| Synchronous update and coefficient formula on the infinite lattice | [`iterate_data`](../PredictionDepth/FrozenPascal/Semantics.lean) |
| Per-time lower bound for arbitrary correct fan-in-two predictors | [`classifiedPrediction_depth_lower_bound`](../PredictionDepth/FrozenPascal/UniformClassification.lean) |
| Equivalence for a constant depth bound across time indices | [`bounded_prediction_depth_iff`](../PredictionDepth/FrozenPascal/Classification.lean) |
| Pascal support cardinality and per-time balanced-tree resources | [`pascalSupport_card`, `homogeneousPrediction_depth`, `homogeneousPrediction_size`](../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) |
| Exact Pascal depth with native XOR and with De Morgan gates | [`homogeneousNativeXorPrediction_depth`](../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) · [`homogeneous_prediction_deMorgan_exact_depth`, `homogeneous_prediction_deMorgan_depth_lower_bound`](../PredictionDepth/FrozenPascal/PascalExactDepth.lean) |
| Correctness, logspace uniformity, and branch bounds in the same family | [`uniform_depth_classification`](../PredictionDepth/FrozenPascal/UniformClassification.lean) |
| Uniform NC⁰ equivalence over all input lengths | [`predictionLanguage_mem_uniformNC_zero_iff`](../PredictionDepth/FrozenPascal/UniformClassification.lean) |

## Related work

Moore's *Physica D* paper divides time intervals to compute transfer coefficients for non-autonomous additive cellular automata, where coefficients can vary across space and time. Lemma 1 in §3 of the preprint gives ACC¹ circuits with unbounded-fan-in modular sums. Using binary gates gives $`O(\log^2 T)`$ depth. Theorem 1 applies the method to quasidirect products, in which another track controls those coefficients. For homogeneous additive rules, the paper already describes how to generate Pascal rows in logspace and obtain uniform ACC⁰ with unbounded-fan-in modular sums. Glaisher established the odd-coefficient count, and Rowland reviews its relationship to Lucas's theorem. [Journal article](https://doi.org/10.1016/S0167-2789(97)80003-6) · [Preprint §3](https://arxiv.org/pdf/patt-sol/9701008) · [Rowland §1](https://arxiv.org/pdf/1001.1783)

With fixed controls, data evolution is an upper bidiagonal operator with diagonal entries $`s(a_i)`$ and superdiagonal entries $`h(a_i)`$. Higham's Theorem 6.1 gives a product and divided-difference formula for functions of upper bidiagonal matrices over the complex numbers. For a power, the divided difference is a complete homogeneous symmetric polynomial. Evaluating its diagonal variables at $`0`$ or $`1`$ counts monomials of total degree $`T-k`$ supported on the enabled stay sites, giving the same multichoose coefficient. The path argument proves the specialization directly over $`\mathbb F_2`$ and supplies the formula for resource analysis and the uniform construction. [Higham, Theorem 6.1](https://doi.org/10.13001/ela.2024.8297)

This project connects the one-sided, spatially varying and temporally fixed specialization to a machine-defined uniform NC¹ upper bound and a four-regime depth classification. The $`O(\log T)`$ depth bound is for frozen controls and can be compared with Moore's divide-and-conquer guarantee for more general coefficients. Priority for the exact rule-family classification and uniform upper bound remains undetermined. [Detailed comparison](literature.md)

## Evolving controls

For a control track translated by one site at each step, the reflected moving frame makes the guards stationary and exchanges stay and hop. The finite-window predictor reverses data and rewires controls with an offset of one site. Lean verifies the reduction, its circuit costs, and its serializer. For additive control evolution, the endpoint's two frozen statistics can agree while the transfer coefficient differs. Lean checks the coefficient formula using a shared Pascal parity and a suffix-zero test. A three-bit ordered summary implements both through the reusable compiler, giving a linear-size, logarithmic-depth uniform predictor. Lean also checks the parity restriction that forces depth at least $\lceil\log_2(T+1)\rceil$ for fan-in-two Boolean circuits. [Reflected-frame reduction](../PredictionDepth/TransportedBranching.lean) · [Additive-control coefficient formula](../PredictionDepth/AdditiveBranching.lean) · [Verified uniform predictor](../PredictionDepth/AdditiveBranching/Summary.lean) · [Verified lower bound](../PredictionDepth/AdditiveBranching/LowerBound.lean)
