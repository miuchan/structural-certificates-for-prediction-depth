#let title = "Structural Certificates for Prediction Depth"
#let author = "Amamiya Miu"
#set document(title: title, author: author)
#set page(
  paper: "a4",
  margin: (x: 24mm, top: 22mm, bottom: 22mm),
  numbering: "1",
  number-align: center,
)
#set text(font: "Libertinus Serif", size: 11pt, lang: "en")
#set par(justify: true, leading: 0.6em)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")
#show heading.where(level: 1): set block(above: 1.2em, below: 0.65em)
#show heading.where(level: 2): set block(above: 1em, below: 0.5em)
#show bibliography: set text(size: 10pt)

#let theorem(name, body) = figure(
  kind: "theorem",
  supplement: [Theorem],
  numbering: "1",
  caption: [],
  block(width: 100%, above: 0.85em, below: 0.85em, breakable: false)[
    #set align(left)
    *Theorem #context counter(figure.where(kind: "theorem")).display("1") (#name).*
    #emph(body)
  ],
)
#show figure.where(kind: "theorem"): it => it.body
#let qed = [#h(1fr) $square$]

#align(center, block(above: 0pt, below: 1.4em)[
  #text(size: 23pt, weight: "bold", title)
  #v(0.2em)
  #text(size: 13pt)[Frozen and transported control in one-sided cellular automata]
  #v(0.6em)
  #text(size: 12pt, author)
])

#pad(x: 8mm)[
#set text(size: 10.5pt)
*Abstract.* We classify the prediction depth of one-sided cellular automata whose
frozen control words gate a stay/hop data update over $bb(F)_2$.
The input is the explicit initial cone and the output is the data bit at its
apex. For each fixed rule, a single logspace-uniform family of polynomial-size
De Morgan circuits realizes the classified depth upper bound. The variable-guard
regime has depth $Theta(log(T+1))$, and homogeneous Pascal prediction has depth
within a factor of three of the number of ones in the binary expansion of $T$.
We also analyze a moving-control model in which a single data path accumulates
Boolean guards. At positive times, equal control and data velocities give depth
one, whereas unequal velocities give exact depth $ceil(log_2(T+1))$.
The finite statements follow from Lean 4 proofs of the dynamics, circuit
correctness, and the fan-in lower bounds.

*Keywords.* Cellular automata, circuit depth, logspace uniformity, Lean 4.
]

= Introduction

Algebraic structure can make a cellular automaton's future state accessible
to much shallower circuits than layer-by-layer simulation @moore.
We ask which fixed guards in a one-sided, two-track automaton admit
constant-depth prediction and how depth depends on the observation time.

For frozen controls, path counting gives a uniform logarithmic-depth
construction and input restrictions give lower bounds. The resulting four
regimes include a homogeneous rule whose depth can drop between consecutive
times (@frozen-classification). For transported controls, relative velocity
determines the number of distinct initial controls encountered along the data
path. A balanced conjunction attains the resulting lower bound
(@transport-depth). Both classifications are formalized in Lean 4.

= Preliminaries

A local rule on configurations over $bb(Z)$ is iterated $T$ times. We ask for
one data bit, at site zero. Each model in the main results has a one-sided
radius-one update, so its initial window consists of sites $0, dots, T$.
For the frozen model the input contains $q(T+1)$ control bits followed by
$T+1$ data bits. The control width $q$ and the two guard circuits are fixed
independently of $T$. The legal word lengths are $n=(q+1)(T+1)$ and determine
$T$ uniquely. The language consists of the legal words whose predicted bit is
one, with all other lengths rejected.

Our upper bounds use Boolean AND and OR gates of fan-in two, NOT gates, and
constants. An input wire has depth zero. Gates can share outputs and connect
arbitrary sites. The per-time lower bounds apply to any Boolean gates of
fan-in at most two in this wiring model. For a fixed rule, write $D(T)$ for
the minimum De Morgan circuit depth on the legal window at time $T$ and
write $ell(m)=ceil(log_2 m)$ for $m >= 1$. Uniform circuit families are indexed
by input length. A deterministic logspace transducer receives the length in
unary and writes the complete circuit code, including its gates, wiring,
and output. We use logspace uniformity throughout the statements about $"NC"$.

A coordinate is _essential_ if two assignments that differ only at that
coordinate give different outputs.

#block(breakable: false)[
*Essential-input bound.* A depth-$d$ circuit of fan-in at most $b$ has
at most $b^d$ essential coordinates. For $b >= 2$, a function with $m >= 1$
essential coordinates therefore requires depth at least $ceil(log_b m)$.

_Proof._ Only input wires in the backwards cone of the output can affect
it. At depth zero the cone has at most one input. At the next depth a gate
has at most $b$ predecessor cones, so induction bounds the number of input
wires by $b^d$. In a shared circuit, counting a repeated predecessor more
than once only increases the bound. #qed
]

= Frozen-control automata
== The iterate formula

Let $a_i in {0,1}^q$ be a control word, $x_i in bb(F)_2$ an initial data bit, and
$s,h : {0,1}^q -> {0,1}$ the stay and hop guards. The synchronous update is
$
  a'_i = a_i, quad
  x'_i = s(a_i) x_i + h(a_i) x_(i+1),
$ <frozen-rule>
where the data arithmetic is in $bb(F)_2$. A backwards path ending at site
$k$ has $k$ hops and $T-k$ stays. Put
$
  e_k = product_(j=0)^(k-1) h(a_j), quad
  w_k = sum_(j=0)^k s(a_j),
$
where the second sum is in the natural numbers. For natural $w,r$, write
$M(w,r)$ for the number of weak compositions of $r$ into $w$ parts.
For $w>0$, it is $binom(w+r-1,r)$, and $M(0,r)$ is one at $r=0$ and
zero otherwise.

#theorem("Iterate formula")[
  For every initial configuration and time $T$, the data bit at site zero is
  $
    x_0(T) = sum_(k=0)^T e_k (M(w_k,T-k) mod 2) x_k.
  $ <frozen-sum>
  The same identity holds at any site after translating the indices.
]<frozen-iterate>

_Proof._ Expanding the local recurrence once per step expresses the
output as a sum over backwards paths. Each hop must be enabled,
contributing the factor $e_k$. A path visits the
sites $0$ through $k$ in order. The number of stays allocated to each enabled
site determines the path, including possible stays after the last hop.
There are $M(w_k,T-k)$ such allocations. Their contributions add in
$bb(F)_2$, giving @frozen-sum. The Lean proof establishes the corresponding
coefficient recurrence by induction on the iterate of @frozen-rule.
The formula involves only the initial window. #qed

== Depth classification

Write $p(T)$ for the number of ones in the binary expansion of $T$, and
$d_s,d_h$ for the depths of the fixed guard circuits. A guard varies if it
takes both Boolean values. All the bounds below are finite, including
$T=0$.

#figure(
  table(
    columns: (1.65fr, 0.75fr, 1.55fr),
    align: (left, left, left),
    inset: (x: 7pt, y: 5pt),
    stroke: none,
    table.hline(stroke: 0.7pt),
    table.header([*Guard condition*], [*Lower bound*], [*Uniform upper bound*]),
    table.hline(stroke: 0.4pt),
    [$h equiv 0$], [$0$], [$1+d_s$],
    [$h equiv 1$, $s equiv 0$], [$0$], [$0$],
    [$h$ varies, or $h equiv 1$ and $s$ varies],
      [$ell(T+1)$], [$104(ell(T+3)+1)+max(d_s,d_h)$],
    [$s equiv h equiv 1$], [$p(T)$], [$3p(T)$],
    table.hline(stroke: 0.7pt),
  ),
  caption: [Depth bounds at legal lengths for fixed frozen guards.],
  kind: table,
) <regimes>

#theorem("Uniform classification")[
  For each fixed pair of guard circuits there is one logspace-uniform,
  polynomial-size De Morgan family that decides the whole language and
  achieves the appropriate upper bound in @regimes at every legal length.
  It has depth $O(log(n+2))$ at all lengths. The lower column bounds $D(T)$
  and holds even for arbitrary fan-in-two Boolean gates. The language is
  in logspace-uniform $"NC"^0$ exactly when $h equiv 0$, or when
  $h equiv 1$ and $s equiv 0$.
]<frozen-classification>

== Proof of the uniform classification

_Local and shift cases._ For $h equiv 0$ and $T>0$, the answer is $s(a_0)x_0$ by idempotence.
The pure shift case returns $x_T$. At $T=0$ every rule returns $x_0$.

_Varying guards._ When $h$ varies, set all data bits except $x_T$ to zero. The surviving
term in @frozen-sum is $x_T product_(j=0)^(T-1) h(a_j)$, regardless of
$s$. A nonconstant Boolean guard has an essential bit, as seen along a
single-bit path between two words with different guard values. Each of
the first $T$ control words contributes one essential bit on this
restriction, and $x_T$ contributes one more. When $h equiv 1$ and $s$
varies, fix $s(a_0)=1$ and $s(a_i)=0$ at sites $1$ through $T$. Then
$w_k=1$ for every $k$ and @frozen-sum is parity of all $T+1$ data bits.
Both cases give the same lower bound by essential coordinates.

For the upper bound, evaluate the guards in parallel and compute the prefix
weights $w_k$ and products $e_k$ from @frozen-iterate. The weight circuit
uses balanced carry-save reduction followed by binary addition. For $w_k>0$,
the parity of $M(w_k,T-k)$ tests whether every set bit of $T-k$ is set in
$w_k+T-k-1$. At $w_k=0$ use the zero-part convention. The uniform construction
uses a logspace-generated table of these coefficients, selected by the
computed prefix weights. A balanced parity reduction combines the data
contributions. The depth bound in @regimes accounts for the guard, arithmetic,
selection, and reduction stages.

_Homogeneous Pascal rule._ For $s equiv h equiv 1$, the coefficients are $binom(T,k) mod 2$.
Over $bb(F)_2$, the identity
$
  (1+z)^T = product_(j : "bit"_j(T)=1) (1+z^(2^j))
$
shows that precisely the binary submasks of $T$ occur. Their $2^(p(T))$
data bits are essential. The logarithmic lower bound is therefore $p(T)$.
A balanced XOR tree reduces those leaves in $p(T)$ rounds. Each XOR can
be implemented with at most three De Morgan layers. The uniform generator
scans $k=0, dots, T$, emits the submask wires, and serializes a regular XOR
reducer with $5 p(T) 2^(p(T))$ gates.

_A single uniform family._ The guard circuits and the selected branch are
fixed. The logspace transducer writes that branch's predictor at legal
lengths and a rejecting circuit at other lengths. Its polynomial-length
output bounds the number of gates. The local and shift branches have a
constant bound. In the varying branch the lower bound grows with $T$.
For the homogeneous branch it grows along the times $T=2^r-1$.
This proves the constant-depth characterization. #qed

At $T=2^r-1$ the homogeneous rule needs at least $r$ layers, while at the
next time $T=2^r$ it has a circuit of depth at most three. For $r>3$ this
gives a strict drop in minimum depth. The accompanying classifier
tests constancy of the guards by traversing control words by prefix.
A constancy test stops at its first counterexample and can visit
$2^q$ words in the worst case.

= Transported controls

We now give the control track its own dynamics. Fix velocities
$u,v in {0,1}$ and a Boolean control and data track $(c_i,d_i)$.
Define the synchronous rule
$
  c'_i=c_(i+u), quad d'_i=c_i and d_(i+v).
$ <transport-rule>
#block(breakable: false)[
The window has $2(T+1)$ bits. With a single backwards data path, the data
at site $i$ and time $T$ equals
$
  d_(i+v T) and
  and.big_(k=0)^(T-1) c_(i+k v+(T-1-k)u),
$ <transport-iterate>
where the right-hand side uses initial bits and the conjunction is empty
at $T=0$.
]

#theorem("Exact depth under transport")[
  Depth is zero at $T=0$. For $T>0$, it is exactly one if $u=v$ and
  exactly $ell(T+1)$ if $u != v$. The formal upper-bound construction
  uses a padded AND tree with at most $2m$ binary AND gates for $m$ essential inputs.
  The lower bound applies to all fan-in-two Boolean circuits predicting the data bit.
]<transport-depth>

_Proof._ At the $k$-th step of the backwards path we read control at site
$i+k v$ and time $T-1-k$. The initial site of that control bit is
$i+k v+(T-1-k)u$, which proves @transport-iterate. At $T=0$ the answer is
the input wire $d_i$. At positive times with equal velocities all control
indices coincide, leaving a conjunction of one control bit and one data
bit. For unequal velocities
the initial control indices are $i, dots, i+T-1$ in forward or reverse
order. Every distinct factor is essential, since flipping it with all other
factors set to one changes the output. Thus there are two essential
coordinates in the equal case and $T+1$ in the unequal case.
For $m$ factors, a balanced AND tree of height $ell(m)$ attains the
essential-input lower bound. Padding to the next power of two uses
$2^(ell(m))-1 <= 2m$ binary gates. #qed

The pair $(u,v)=(0,0)$ is the frozen no-hop case with stay guard $c_i$.
Changing only $u$ to one gives logarithmic depth although the data never
hops. For $(u,v)=(1,1)$ the data and control both move, yet their equal
velocity gives constant depth. For this single-path rule, the relevant
count is the number of distinct initial controls encountered in the
moving frame of the data path. The time-dependent framework in @moore
accommodates this rule. Its single path makes the exact depth accessible.

= Related work

*Pascal parity and fast prediction.* The odd-entry count $2^(p(T))$ is
classical. Rowland attributes the binary count to Glaisher and derives it
from Lucas's theorem @rowland. The fast cellular-automaton prediction work
in @moore already uses the Pascal coefficients for homogeneous additive
rules. Its modular-sum gates can have unbounded fan-in. The Pascal claim
here is a per-time bounded-fan-in lower bound and a matching profile up
to a constant factor with a verified uniform De Morgan generator.

*Dependent linear tracks and the coefficient formula.* Moore's general
divide-and-conquer method for time- and space-dependent linear stages gives
an $O(log^2(T+2))$ bounded-fan-in prediction bound in the stated setting
@moore. Freezing the controls and using the one-sided stay/hop stencil
lets us use prefix statistics and reach $O(log(T+2))$ in this specialization.
The coefficient in @frozen-sum also has a classical matrix analogue.
The one-step data map is upper bidiagonal on the relevant finite window.
Higham's divided-difference formula for functions of such matrices gives
the product of intervening off-diagonal entries times a divided difference
in the diagonal entries @higham. For the monomial $z^T$ this divided
difference is a complete homogeneous polynomial of degree $T-k$.
On zero-one diagonal entries it counts the same weak compositions.
The polynomial identity can be specialized to integer zero-one entries
before reducing modulo two, with no division in $bb(F)_2$.

*Mechanization and the meaning of frozen.* Silváši and Tomášek formalized
bounded grids and computable cellular automata in Lean @silvasi. Their
work supplies precedent for machine-checked cellular automata. The
present artifact checks a rule-family depth classification and the
actual circuit generator. The freezing model of Ollinger and Theyssier
imposes a monotone order on each whole cell state @ollinger. In @frozen-rule
only the control word is fixed, and the data at a site can cycle.
The comparison identifies antecedents for the main ingredients.
Priority for the exact four-way classification and for the transport
specialization remains undetermined.

= Discussion

#block(breakable: false)[
The frozen classification applies to an explicitly supplied cone and a
fixed finite guard pair. Its logarithmic depth is measured against $n$,
which grows linearly with $T$. Giving a succinct initial state and a
binary time query defines a different problem. Uniformity is established
for the frozen family. The transport result concerns optimal depth at
each window length. The circuit model permits arbitrary wiring.
With unbounded fan-in, the transported-control AND
can be evaluated in one layer, and the counting argument no longer gives
its logarithmic depth. Conversely, if each circuit layer has spatial
wiring radius at most $r$, an essential coordinate at distance $T$
forces $T <= d r$. This additional hypothesis is used for the repository's
geometric lower bound in the OR automaton. For unrestricted wiring and
fan-in two, that separate example has exact depth $ell(2T+1)$.
]

*Composition certificate.* For an evolution $F$, a bit-string decoder
$I$ into its state space, and an observation $O$, suppose finite-register
Boolean circuits implement initialization, composition along the executed
path, and observation. If their depths are $eta, delta, epsilon$,
repeated squaring produces $O(F^T(I(x)))$ from $x$ with depth at most
$eta + 2 ell(T+1) delta + epsilon$. A separate uniform compiler requires
logspace generators for the primitives and charges copying during
normalization. Its depth bound is $eta + 1 + 2 ell(T+1)(delta+1) + epsilon$,
with $delta$ bounding both composition primitives. Membership in $"NC"$
requires a polylogarithmic bound in the actual input length.

*Simulation certificate.* For a specified system, a logspace transducer
from circuit value instances to complete queries $1^T 0 x$, together with
an observation-equality proof, makes its prediction language P-hard
under logspace many-one reductions @ladner. A polynomial-time decider
for the target yields P-completeness. Assuming $"P" != "logspace-uniform NC"$,
a verified hardness witness excludes the target from that parallel class.
This conclusion gives no specific numerical depth rate. Rule 110 is a
separate concrete P-completeness result in the literature @neary.

= Conclusion

The frozen-control classification separates fixed rules with constant-depth
prediction from rules whose depth grows at least along a subsequence. Within
the growing regimes, the homogeneous rule's profile follows the set bits of
the observation time. The transported model isolates a different mechanism.
Distinct initial control sites accumulate along the data path only when the
velocities differ. Both classifications follow by identifying the relevant
inputs and constructing circuits that combine them with the required depth.

#heading(numbering: none)[Artifact availability]

The Lean development, Typst source, and build instructions are available
in the #link("https://github.com/miuchan/structural-certificates-for-prediction-depth")[project repository].
The Lean toolchain and dependencies are pinned by `lean-toolchain` and
`lake-manifest.json`. Run #box[`./scripts/check.sh`] at the repository root
to check entry-point coverage, build with warnings treated as errors, audit
transitive axiom dependencies, and run the audit regression test.
@lean-map lists the statements corresponding to the main results.

#counter(heading).update(0)
#set heading(numbering: "A.1")
#pagebreak(weak: true)
#heading(supplement: [Appendix])[Lean correspondence] <lean-map>

The paths below are relative to `PredictionDepth/`. The names identify
the machine-checked statements underlying the main claims.

#table(
  columns: (1fr, 2.55fr),
  inset: (x: 7pt, y: 5pt),
  align: left,
  stroke: none,
  table.hline(stroke: 0.7pt),
  table.header([*Result*], [*Lean module and declaration*]),
  table.hline(stroke: 0.4pt),
  [Frozen iterate],
  [`FrozenPascal/Semantics.lean` #linebreak() `iterate_data`],
  [Uniform classification],
  [`FrozenPascal/UniformClassification.lean` #linebreak()
   `uniform_depth_classification` #linebreak() `predictionLanguage_mem_uniformNC_zero_iff`],
  [Pascal support],
  [`FrozenPascal/HomogeneousPascal.lean` #linebreak() `pascalSupport_card`],
  [Moving controls],
  [`TransportedControl.lean` #linebreak()
   `iterate_data_true_iff`, `essential_prediction_iff` #linebreak()
   `exact_prediction_depth`, `constant_depth_iff`],
  [Composition criterion],
  [`EncodedPathComposition.lean` #linebreak()
   `EncodedPathImplementation.predictor_depth_le` #linebreak()
   `Complexity/UniformComposition.lean` #linebreak()
   `UniformRegisterWitness.depth_le_costs`],
  [Simulation criterion],
  [`Complexity/StandardHardness.lean` #linebreak()
   `SimulationWitness.prediction_P_complete` #linebreak()
   `Complexity/NCClosure.lean` #linebreak()
   `SimulationWitness.prediction_not_uniformNC`],
  table.hline(stroke: 0.7pt),
)

#bibliography("references.bib", style: "ieee", title: [References])
