#set document(title: "Structural Certificates for Prediction Depth")
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
#show link: set text(fill: rgb("#224d70"))
#show bibliography: set text(size: 10pt)

#let theorem(title, body) = block(
  width: 100%, inset: (x: 10pt, y: 8pt), radius: 2pt,
  fill: rgb("#f1f5f8"), stroke: (left: 1.5pt + rgb("#224d70")),
)[
  *#title.* #body
]
#align(center)[
  #text(size: 23pt, weight: "bold")[Structural Certificates for Prediction Depth]
  #v(0.35em)
  #text(size: 13pt)[Frozen and transported control in one-sided cellular automata]
  #v(0.7em)
  Research note with Lean 4 proofs
]
#v(0.6em)

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

= Prediction problem and circuit model

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

A coordinate is *essential* if two assignments that differ only at that
coordinate give different outputs. The backwards cone of a depth-$d$
output with fan-in at most $b$ contains at most $b^d$ input coordinates.
This follows by induction on depth, since a gate has at most $b$ predecessor
cones. It remains valid in a shared circuit because counting a repeated
predecessor more than once can only increase the bound. Thus $m$ essential
coordinates force $d >= ceil(log_b m)$ when $b >= 2$ and $m >= 1$.

= Frozen controls
== The iterate of the local rule

Let $a_i in {0,1}^q$ be a control word, $x_i in bb(F)_2$ a data bit, and
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

#theorem("Theorem 1 (iterate formula)")[
  For every initial configuration and time $T$, the data bit at site zero is
  $
    x_0(T) = sum_(k=0)^T e_k (M(w_k,T-k) mod 2) x_k.
  $ <frozen-sum>
  The same identity holds at any site after translating the indices.
]
Each hop must be enabled, contributing the factor $e_k$. A path visits the
sites $0$ through $k$ in order. The number of stays allocated to each enabled
site determines the path, including possible stays after the last hop.
The Lean proof in `iterate_data` derives the recurrence for these
coefficients and inducts on the actual local iterate @frozen-rule.
This also establishes independence from the initial configuration outside
the window.

For evaluation in parallel, evaluate the guards at every site and compute
all prefix weights $w_k$ and products $e_k$. The weight circuit combines
carry-save pairs along a balanced tree and completes the binary sum at the
end. For $w_k>0$, the parity test for $M(w_k,T-k)$ checks whether every set
bit of $T-k$ is also set in $w_k+T-k-1$. The $w_k=0$ branch uses the
explicit zero-part convention. In the uniform construction the test uses
a logspace-generated table of coefficients indexed by the possible prefix
weights, together with equality and selection circuits. A balanced parity
reduction combines the data contributions. The balanced arithmetic and
selection stages give logarithmic depth. The logspace generator writes a
polynomial-length code and the number of gates is bounded by its length.

== Depth classification

Write $p(T)$ for the number of ones in the binary expansion of $T$, and
$d_s,d_h$ for the depths of the fixed guard circuits. A guard varies if it
takes both Boolean values. All the bounds below are finite, including
$T=0$.

#figure(
  table(
    columns: (1.65fr, 0.75fr, 1.55fr),
    align: (left, left, left),
    inset: (x: 7pt, y: 6pt),
    stroke: (x: none, y: 0.4pt + rgb("#aab9c4")),
    fill: (x, y) => if y == 0 { rgb("#e6eef4") } else { none },
    table.header([*Guard condition*], [*Lower bound*], [*Uniform upper bound*]),
    [$h equiv 0$], [$0$], [$1+d_s$],
    [$h equiv 1$, $s equiv 0$], [$0$], [$0$],
    [$h$ varies, or $h equiv 1$ and $s$ varies],
      [$ell(T+1)$], [$104(ell(T+3)+1)+max(d_s,d_h)$],
    [$s equiv h equiv 1$], [$p(T)$], [$3p(T)$],
  ),
  caption: [Depth bounds at legal lengths for fixed frozen guards.],
  kind: table,
) <regimes>

#theorem("Theorem 2 (uniform classification)")[
  For each fixed pair of guard circuits there is one logspace-uniform,
  polynomial-size De Morgan family that decides the whole language and
  achieves the appropriate upper bound in @regimes at every legal length.
  It has depth $O(log(n+2))$ at all lengths. The lower column bounds $D(T)$
  and holds even for arbitrary fan-in-two Boolean gates. The language is
  in logspace-uniform $"NC"^0$ exactly when $h equiv 0$, or when
  $h equiv 1$ and $s equiv 0$.
]

For $h equiv 0$ and $T>0$, the answer is $s(a_0)x_0$ by idempotence.
The pure shift case returns $x_T$. At $T=0$ every rule returns $x_0$.

When $h$ varies, set all data bits except $x_T$ to zero. The surviving
term in @frozen-sum is $x_T product_(j=0)^(T-1) h(a_j)$, regardless of
$s$. A nonconstant Boolean guard has an essential bit, as seen along a
single-bit path between two words with different guard values. Each of
the first $T$ control words contributes one essential bit on this
restriction, and $x_T$ contributes one more. When $h equiv 1$ and $s$
varies, fix $s(a_0)=1$ and $s(a_i)=0$ at sites $1$ through $T$. Then
$w_k=1$ for every $k$ and @frozen-sum is parity of all $T+1$ data bits.
Both cases give the same lower bound by essential coordinates.

For $s equiv h equiv 1$, the coefficients are $binom(T,k) mod 2$.
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
The depth is at most three when $T=2^r$ and at least $r$ when $T=2^r-1$.
In particular the depth drops from at least $r$ to at most three across
these consecutive times for $r>3$.

The executable classifier checks constancy of the guards on their finite
alphabet. It visits control words by prefix and can stop a constancy test
on its first counterexample, without allocating the alphabet as a list.
An exhaustive test can still require $2^q$ words. For uniform prediction
the guard circuits and the selected branch are fixed, and the transducer
is uniform in the window length. At legal lengths its output is the
selected predictor; at malformed lengths it writes a rejecting circuit.
The theorem packages semantics, generation, size, and depth for that
same family.

= Transported controls

The next model gives the control track its own dynamics. Fix velocities
$u,v in {0,1}$ and a Boolean control and data track $(c_i,d_i)$.
Define the synchronous rule
$
  c'_i=c_(i+u), quad d'_i=c_i and d_(i+v).
$ <transport-rule>
The window has $2(T+1)$ bits. With a single backwards data path, the data
at time $T$ equals
$
  d_(i+v T) and
  and.big_(k=0)^(T-1) c_(i+k v+(T-1-k)u),
$ <transport-iterate>
where the conjunction is empty at $T=0$. At the $k$-th path step we read
control at site $i+k v$ and time $T-1-k$. The control has shifted by
$(T-1-k)u$ initial sites, which yields @transport-iterate.

#theorem("Theorem 3 (exact depth under transport)")[
  Depth is zero at $T=0$. For $T>0$, it is exactly one if $u=v$ and
  exactly $ell(T+1)$ if $u != v$. The formal upper-bound construction
  uses a padded AND tree with at most $2m$ binary AND gates for $m$ essential inputs.
  The lower bound applies to all fan-in-two Boolean circuits predicting the data bit.
]

For equal velocities all control indices coincide and idempotence leaves
two essential inputs, one control and one data bit. For unequal velocities
the initial control indices are $i, dots, i+T-1$ in forward or reverse
order. Together with the terminal data bit they are $T+1$ essential
coordinates. A balanced AND tree attains the depth bound for each legal
window. This theorem is a per-time statement about circuits on those windows.

The pair $(u,v)=(0,0)$ is the frozen no-hop case with stay guard $c_i$.
Changing only $u$ to one gives logarithmic depth although the data never
hops. For $(u,v)=(1,1)$ the data and control both move, yet their equal
velocity gives constant depth. For this single-path rule, the relevant
count is the number of distinct initial controls encountered in the
moving frame of the data path. The time-dependent framework in @moore
accommodates this rule. Its single path makes the exact depth accessible.

= Relation to earlier work

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

= Scope of the certificates

The frozen classification applies to an explicitly supplied cone and a
fixed finite guard pair. Its logarithmic depth is measured against $n$,
which grows linearly with $T$. Giving a succinct initial state and a
binary time query defines a different problem. The theorem also assumes
arbitrary wiring. With unbounded fan-in, the transported-control AND
can be evaluated in one layer, and the counting argument no longer gives
its logarithmic depth. Conversely, if each circuit layer has spatial
wiring radius at most $r$, an essential coordinate at distance $T$
forces $T <= d r$. This additional hypothesis is used for the repository's
geometric lower bound in the OR automaton. For unrestricted wiring and
fan-in two, that separate example has exact depth $ell(2T+1)$.

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

= Lean statement map and reproduction

The paths below are relative to `PredictionDepth/`. The names identify
the machine-checked statements underlying the main claims.

#table(
  columns: (1fr, 2.55fr),
  inset: (x: 7pt, y: 5pt),
  align: left,
  stroke: (x: none, y: 0.4pt + rgb("#aab9c4")),
  table.header([*Result*], [*Lean module and declaration*]),
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
)

The Lean toolchain and dependencies are pinned by `lean-toolchain` and
`lake-manifest.json`. Run `./scripts/check.sh` at the repository root.
The script checks entry-point coverage, builds with warnings treated
as errors, audits transitive axiom dependencies of project declarations,
and checks that the audit rejects an unapproved transitive axiom.

#bibliography("references.bib", style: "ieee")
