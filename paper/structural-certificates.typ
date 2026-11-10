#let title-line-1 = "Prediction Depth of"
#let title-line-2 = "Controlled Cellular Automata"
#let title = title-line-1 + " " + title-line-2
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
  #text(size: 21pt, weight: "bold")[#title-line-1 #linebreak() #title-line-2]
  #v(0.2em)
  #text(size: 13pt)[A Lean-Verified Classification for One-Sided Rules]
  #v(0.6em)
  #text(size: 12pt, author)
])

#pad(x: 8mm)[
#set text(size: 10.5pt)
*Abstract.* We classify the prediction depth of one-sided cellular automata whose
frozen control words gate a stay/hop data update over $bb(F)_2$.
The input is the explicit initial window and the output is the predicted data
bit at its apex. An executable classifier selects a branch for each fixed rule.
A single logspace-uniform, polynomial-size De Morgan family for that rule
realizes the selected depth bound at every time. Prediction is in
logspace-uniform $"NC"^0$ exactly when the hop guard is identically zero, or
when it is identically one and the stay guard is identically zero. When the
hop guard is nonconstant, or is identically one and the stay guard is
nonconstant, depth is $Theta(log(T+1))$. The homogeneous Pascal rule has
depth between the number of set bits of $T$ and three times that number.
As a structural comparison, a separate one-path model with transported
control has positive-time depth one at equal velocities and exactly
$ceil(log_2(T+1))$ at unequal velocities. Lean 4 verifies the classification,
the connection from dynamics to finite prediction, and the circuit bounds
and generators for the frozen rules.

*Keywords.* Cellular automata, circuit depth, logspace uniformity, Lean 4.
]

= Introduction

Algebraic structure can make a cellular automaton's future state accessible
to much shallower circuits than layer-by-layer simulation @moore.
We ask which fixed guards in a one-sided, two-track automaton admit
constant-depth prediction and how depth depends on the observation time.

Our main result is the four-way classification of frozen rules
(@frozen-classification). A finite guard test selects the branch, and
each branch pairs pointwise lower bounds with a single actual generator
that meets its upper bound at every time. The homogeneous branch has a
nonmonotone depth profile governed by the set bits of the observation time.
The main construction turns path counts into parallel prefix statistics
and uses those statistics to select coefficients in logarithmic depth
(@uniform-construction). We also solve a separate one-path rule with
transported control as a structural comparison (@transport-depth).
There, relative velocity determines how many distinct initial controls
the path encounters.

= Preliminaries

A local rule on configurations over $bb(Z)$ is iterated $T$ times. We ask for
one data bit, at site zero. Each model in the main results has a one-sided
radius-one update, so its initial window consists of sites $0, dots, T$.
For the frozen model the input contains $q(T+1)$ control bits followed by
$T+1$ data bits. The control width $q$ and the two guard circuits are fixed
independently of $T$. The legal word lengths are $n=(q+1)(T+1)$ and determine
$T$ uniquely. The prediction language $L_(s,h)$ consists of the legal words whose predicted bit is
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
  and holds even for arbitrary fan-in-two Boolean gates. Constant-depth membership is
  characterized by
  $
    L_(s,h) in "logspace-uniform " "NC"^0
    quad <=> quad h equiv 0 or (h equiv 1 and s equiv 0).
  $
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

The upper bound in this branch is given by the construction in
@uniform-construction.

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
Lean proves that its return value is equivalent to the branch condition.
A constancy test stops at its first counterexample and can visit
$2^q$ words in the worst case.

== Uniform prediction circuit <uniform-construction>

Put $m=T+1$. After evaluating the two guards at all sites in parallel,
the circuit keeps the resulting guard bits and the data track in a
register alongside an $m$-bit one-hot time tag $tau$. Starting with
$u=0$, the binary digits of $T$ direct a sequence of index doublings and
optional increments $u -> 2u$, $u -> u+1$. Each operation just routes
the tag wires, with zero fill. The guard and data tracks pass through.
At the end only $tau_T$ is one.

*Parallel prefixes.* For each $k$, count the $k+1$ stay bits to obtain
$w_k$ and take the conjunction of the first $k$ hop bits to obtain $e_k$.
All prefixes are computed independently and in parallel. A counter on
$a$ bits uses $b=ell(a+1)$ bits per word and pads to $P=2^b$ pairs of words.
Each initial pair represents an input bit or zero. A three-word
compressor emits the bitwise XOR as its sum word and the bitwise majority
shifted left by one as its carry word. These two words preserve the sum
modulo $2^b$ without propagating carries across bit positions. Two such
compressors suffice to merge two pairs into one. After $b$ merge rounds only the
root pair contributes. The final addition applies a compressor with
third input zero $b$ times, clearing one more low carry bit per step.
Since $a<2^b$, the result is the exact count. The depth is $O(b)$ because
there is only one carry-propagating addition on each path.

*Coefficient selection.* At circuit generation time, enumerate the triples
$(u,k,j)$ with $0 <= u,k < m$ and $0 <= j <= k+1$. Let $C_(u,k,j)$ be
zero for $u<k$, and $M(j,u-k) mod 2$ otherwise. For $u>=k$, the $j=0$
case is one exactly when $u=k$. For $j>0$, Lucas's theorem tests whether the
set bits of $u-k$ are a subset of those of $j+u-k-1$ @rowland. The generator can scan
these two integers bit by bit. Each table row with coefficient one
tests $w_k=j$ by conjoining matching bit literals, then gates the test
with $tau_u$. A zero row emits a constant. Exactly one candidate pair
$(u,j)$ can pass the two tests. Thus the XOR of all the rows for a site
is $C_(T,k,w_k)$, the coefficient in @frozen-sum. The circuit reduces
first over $j$ and then over $u$, ANDs each result with $e_k$ and $x_k$,
and takes the XOR over $k$. In this construction each XOR reduction
reads the low bit of a carry-save counter.

#figure(
  table(
    columns: (2.1fr, 1fr, 1.15fr),
    inset: (x: 6pt, y: 4pt),
    align: left,
    stroke: none,
    table.hline(stroke: 0.7pt),
    table.header([*Stage*], [*Parallel instances*], [*Depth bound*]),
    table.hline(stroke: 0.4pt),
    [Guard evaluation], [$2m$], [$max(d_s,d_h)$],
    [Register initialization and time tag], [One register], [$6B$],
    [Stay counts and hop conjunctions], [$m$ of each], [$22B$ and $5B$],
    [Coefficient row tests], [$m^2(m+3)/2$], [$5B$],
    [Parity over $j$, then over $u$], [$m^2$, then $m$], [$23B$ each],
    [Gate by hop prefix and data, then final parity], [$m$, then one], [$2+23B$],
    table.hline(stroke: 0.7pt),
  ),
  caption: [Resources for the generated frozen predictor, with $B=ell(T+3)+1$.
    The two prefix computations run in parallel.],
  kind: table,
) <uniform-resources>

*Size and generation.* The table has $m sum_(k=0)^(m-1) (k+2)$ rows,
each with $O(log^2(m+1))$ gates for the regular conjunction layout.
A padded counter has $O(a+1)$ blocks of
$O(log(a+2))$ lanes in each of $O(log(a+2))$ rounds, with at most
$O(log(a+2))$ gates per lane even when a compressor is repeated for each
output. There are $O(m^2)$ counters including the parity banks, with at
most $m+1$ inputs each. The guard copies, tag routing and
conjunctions fit within the resulting $O(m^3 log^3(m+1))$ gate bound.
The depth is $O(log(m+1))$
because only a fixed number of logarithmic-depth stages are composed.
@depth-budget gives the constants in @regimes.

The serializer counts the unary length $n$, checks that it is a positive multiple of $q+1$,
and obtains $m$ and $T$ at legal lengths. It enumerates table entries by
$(k,u,j)$ and scans their bit positions. The register is indexed in four
blocks of width $m$, for the time, stay, hop and data tracks. Within a
counter round, block $e$ uses blocks $2e$ and $2e+1$ from the preceding
round, with zero padding outside the bank. A gate record is determined
by the round, block, bit lane and position in its local template. To
serialize parallel blocks, the generator counts preceding gates and adds
the resulting offset to internal references. In serial composition, it
resolves an input reference by regenerating the corresponding predecessor
output index. For a chain of width $W$, the generator appends identity
gates $y and y$ so the outputs of each stage have consecutive indices.
With $N$ primary inputs and $G$ preceding gates, a local wire number $a$
then becomes $N+G-W+a$. This lets the generator count through the rounds
without a stack. The nesting of the bank serializers has fixed depth.
The loop indices, offsets and references are all polynomially bounded in
$n$, so a fixed number of counters and arithmetic temporaries suffice
using $O(log(n+2))$ bits of workspace. The gate and output lists are streamed.

= Transported controls as a structural comparison

In this separate model the control track has its own dynamics and the data follows one path. Fix velocities
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
bit. In general, the initial control index is $i+(T-1)u+k(v-u)$.
For unequal velocities the indices are $i, dots, i+T-1$ in forward or reverse
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
The contribution here is the combination of an executable rule classifier,
pointwise depth bounds and a verified uniform generator for the full frozen
rule family. The exact four-way classification and the one-path transport
specialization have undetermined priority in the literature.

= Mechanization and scope

The window interface separates infinite dynamics from finite inputs.
`rawSample` reads the window from a configuration, and `decodeRaw` extends
an arbitrary legal window to an infinite configuration. Lean proves that
sampling this extension recovers the supplied bits. Correctness on sampled
configurations therefore gives correctness on every legal input. Lifting
from time to input length selects that same predictor at legal lengths and
a rejecting circuit at the others.

The uniformity proof generates the code of the circuit used for the depth
bound, including the variable-length lists of gates and output references.
The reusable code combinators verify reference bounds and relocation for
parallel banks and serial composition. These obligations allow a generator
to recover individual references by recomputation in logarithmic space.
The classification theorem uses the selected circuit family as one witness
for correctness, size, uniformity and the per-time bound. The transport
theorem establishes optimal depth separately at each window length.

Each frozen control word selects one of four local data maps
$0$, $x_i$, $x_(i+1)$ and $x_i+x_(i+1)$. Once the controls are fixed,
the data dynamics is one-sided and linear. The input is an explicit window
with length linear in $T$, and the circuit can wire across arbitrary sites.
The accompanying development also formalizes composition and simulation
criteria for other models. Their application requires a separate
implementation or reduction witness.

= Conclusion

The exact $"NC"^0$ criterion and the Pascal profile describe distinct
ways that frozen prediction depth depends on time. For varying guards,
prefix counts make the path coefficients accessible in logarithmic
depth, which lets the same uniform family attain the upper bound at
each legal length. The transported rule exhibits another mechanism.
Relative motion changes depth by changing how many initial control
bits a single data path reads.

#heading(numbering: none)[Artifact availability]

The formal results refer to this #link("https://github.com/miuchan/structural-certificates-for-prediction-depth/tree/08e9aa3dfad7132226849b39386005397469d656")[fixed Lean source revision].
The Typst source and build instructions are in the #link("https://github.com/miuchan/structural-certificates-for-prediction-depth")[project repository].
Use the full commit SHA associated with the PDF to select the source snapshot.
The repository documents the pinned Typst and font inputs for rebuilding
all four editions. GitHub Actions verifies that all four PDFs rebuild from the checked-out commit. Run #box[`./scripts/check.sh`] for the strict Lean build
and axiom audit. @lean-map lists the declarations behind the main results.

#counter(heading).update(0)
#set heading(numbering: "A.1")
#pagebreak(weak: true)
#heading(supplement: [Appendix])[Depth budget] <depth-budget>

The normalized counter tree costs at most $2+14b$ layers, including
initialization and copying in each merge round. The finishing addition costs
at most $1+8b$. Together they cost at most $22(b+1)$.
The counts therefore cost at most $22B$, and taking the low bit of
a counter for parity is bounded by $23B$ including the empty case.
The depth proof charges $5B$ for a row test, from the literal comparisons,
conjunction and time tag. The hop conjunction, bounded by $5B$, runs
alongside the lookup. The decoder budget is
$22B+5B+3 dot 23B+2=96B+2 <= 98B$.
Register initialization costs at most two layers with normalization.
There are at most $2 ell(T+1)$ subsequent register stages of at most two
layers each, also counting normalization. This gives at most $6B$ for
the register path and a total of $104B+max(d_s,d_h)$ including guards.

#heading(supplement: [Appendix])[Lean correspondence] <lean-map>

The paths below are relative to `PredictionDepth/`.

#table(
  columns: (1fr, 2.55fr),
  inset: (x: 7pt, y: 5pt),
  align: left,
  stroke: none,
  table.hline(stroke: 0.7pt),
  table.header([*Result*], [*Lean module and declaration*]),
  table.hline(stroke: 0.4pt),
  [Frozen iterate], [`FrozenPascal/Semantics.lean` #linebreak() `iterate_data`],
  [Window interface], [`FrozenPascal/GuardRules.lean` #linebreak() `rawSample_decodeRaw`],
  [Executable classifier], [`FrozenPascal/Classification.lean` #linebreak() `classify`, `classify_eq_iff`],
  [Uniform classification], [`FrozenPascal/UniformClassification.lean` #linebreak()
    `uniform_depth_classification` #linebreak() `predictionLanguage_mem_uniformNC_zero_iff`],
  [Uniform predictor], [`FrozenPascal/UniformPrediction.lean` #linebreak()
    `uniformGuardedPrediction_code_logspace` #linebreak() `uniformGuardedPrediction_depth`],
  [Code composition], [`Complexity/CodeLogspace.lean` #linebreak() `compCode_logspace`],
  [Pascal support], [`FrozenPascal/HomogeneousPascal.lean` #linebreak() `pascalSupport_card`],
  [Transported control], [`TransportedControl.lean` #linebreak()
    `iterate_data_true_iff`, `essential_prediction_iff` #linebreak()
    `exact_prediction_depth`, `constant_depth_iff`],
  table.hline(stroke: 0.7pt),
)

#bibliography("references.bib", style: "ieee", title: [References])
