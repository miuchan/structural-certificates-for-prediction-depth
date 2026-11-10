#import "transported-control-figure.typ": transported-control-figure

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
nonconstant, depth is $Theta(log(T+1))$. For the homogeneous Pascal rule
at $T>0$, the minimum depth is $2p(T)+1$ with De Morgan gates, where
$p(T)$ counts the set bits of $T$. The verified uniform generator uses
depth at most $3p(T)$.
As a structural comparison, a separate one-path model with transported
control has positive-time depth one at equal velocities and exactly
$ceil(log_2(T+1))$ at unequal velocities. Lean 4 verifies the classification,
the connection from dynamics to finite prediction, the Pascal optimum,
and the uniform generators for the frozen rules.

*Keywords.* Cellular automata, circuit depth, logspace uniformity, Lean 4.
]

= Introduction

Which verifiable conditions on an evolution rule $F$ and an observation $O$
bound the circuit depth of $O(F^T(x))$ for a specified input encoding and
circuit model? Algebraic structure can make cellular automaton prediction
much shallower than layer-by-layer simulation @moore. Here we ask which
fixed guards in a one-sided, two-track automaton admit constant-depth
prediction and how depth depends on the observation time.

Our main result is the four-way classification of frozen rules
(@frozen-classification). A finite guard test selects the branch, and
one logspace generator for the chosen branch achieves the stated upper
bound at every time. The main construction uses the forced order of hops
to summarize all paths to an endpoint by two prefix statistics. A binary
no-carry test then detects which coefficients survive cancellation
(@uniform-construction). The homogeneous branch has a nonmonotone depth
profile governed by the set bits of the observation time. A separate
one-path rule shows how relative velocity changes the number of distinct
initial controls read (@transport-depth).

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
constants. An input wire has depth zero and a NOT gate costs one layer.
Gates can share outputs and connect arbitrary sites. The lower bounds in
the classification apply to any Boolean gates of fan-in at most two.
For a fixed rule, write $D(T)$ for
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
      [$ell(T+1)$], [$O(log(T+2))$],
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

The accompanying classifier tests constancy of the guards by traversing
control words by prefix.
Lean proves that its return value is equivalent to the branch condition.
A constancy test stops at its first counterexample and can visit
$2^q$ words in the worst case.

== Exact depth in the Pascal case <pascal-exact>

Write $p=p(T)$ and $N=2^p$. The Pascal output is parity of $N$ inputs.
With XOR available as a single binary gate, a balanced tree attains
the lower bound $p$. With De Morgan gates the exact depth is zero at
$T=0$ and $2p+1$ at $T>0$.

_Proof._ For the upper bound, give every leaf both its bit and its
negation. A node with child parities $a,b$ computes $a xor b$ and its
complement in two layers from $a,not a,b,not b$. For example, the
positive output is $(a and not b) or (not a and b)$ and the negative
output is $(a and b) or (not a and not b)$. The $p$ internal levels
therefore add $2p$ layers to the one layer of leaf negations.

For the lower bound, set irrelevant inputs to constants and unfold the
circuit into a formula of the same or smaller depth. Push negations to
the leaves and simplify constants. Khrapchenko's parity bound requires
at least $N^2$ literal leaves @khrapchenko. Pushing negations preserves
leaf count and simplifying constants can only decrease it. A formula
of depth at most $2p$ has at most $2^(2p)=N^2$ leaves, with equality only
for a full binary tree with all leaves at depth $2p$. That tree has only
AND and OR gates and hence computes a monotone function. Parity of
$N>=2$ inputs is nonmonotone. Thus depth at most $2p$ is impossible.
#qed

Lean verifies both per-time optima. The De Morgan profile drops from
$2r+1$ at $T=2^r-1$ to three at $T=2^r$, for $r>=2$. The uniform
classification uses the separate $3p$ generator in @regimes.

== Uniform prediction circuit <uniform-construction>

Let $B(a)$ be the set of one-bit positions in the binary expansion of
$a$. For $w>0$, Lucas's theorem says that $M(w,r)$ is odd exactly when
$B(r) subset.eq B(w+r-1)$ @rowland. Equivalently, adding $r$ and $w-1$
produces no carry. Indeed, if the bits of $r$ are contained in those of
the sum, subtracting $r$ clears those bits without a borrow. The
remaining bits are those of $w-1$. Including the case $w=0$, the
coefficient test is
$
  M(w,r) mod 2 = 1 quad <=> quad
  (w=0 and r=0) or (w>0 and B(r) inter B(w-1) = emptyset).
$ <no-carry>

The hop prefix $e_k$ decides whether a path can reach $k$. Once the hops
are enabled, the stay count $w_k$ suffices because the enabled sites can
each absorb any number of stays. For example, with two enabled stay
sites and one stay to allocate, both possible paths cancel. In
@no-carry this is the shared low bit of $r=1$ and $w_k-1=1$.

*From the test to a circuit.* Evaluate the guards in parallel. Compute
each $e_k$ by a balanced AND tree and each $w_k$ by a carry-save counter.
Each merge round compresses two pairs of words into one pair at constant
depth, and the final addition propagates carries across only
$O(log(T+2))$ bits. For each $k$ the generator knows $r=T-k$. It checks
@no-carry for each candidate count $j=0,dots,k+1$ by a binary scan, and
the circuit tests equality to $w_k$ for the candidates that pass.
At most one count matches. Gate the selected bit by $e_k x_k$, then
take parity over the sites. This uses a fixed number of logarithmic-depth
stages and polynomial size, even with a separate counter for every prefix.

*The verified generator.* Lean verifies a shared decoder that can handle
any time $u$ within the window. It generates the table for all such $u$
using the Lucas bit test, and selects the rows for $T$ with a one-hot tag.
The tag implements the composition interface by routing wires according
to the binary digits of $T$. Each parity bank reads the low bit of a
carry-save counter. A logspace transducer emits the complete gate and
output lists of this circuit, using recomputation to resolve references.
The explicit depth bound is $104(ell(T+3)+1)+max(d_s,d_h)$.
@depth-budget describes the layout and the resource accounting.

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

#transported-control-figure(
  caption: [Initial control site $j(k)$ at backward step $k$ for $i=0$ and $T=4$.
    Both paths end at the initial data bit $d_4$.],
  alt: "Left, at equal velocities, all four steps read initial control 3. Right, at unequal velocities, the steps read initial controls 0, 1, 2, and 3 in order.",
  supplement: [Figure],
) <transport-controls-figure>

@transport-controls-figure keeps the data path fixed and varies only $u$.
The pair $(u,v)=(0,0)$ is the frozen no-hop case with stay guard $c_i$.
Changing only $u$ to one gives logarithmic depth although the data never
hops. For $(u,v)=(1,1)$ the data and control both move, yet their equal
velocity gives constant depth. For this single-path rule, the relevant
count is the number of distinct initial controls encountered in the
moving frame of the data path. The time-dependent framework in @moore
accommodates this rule. For finite Boolean monomial systems, the link
between iterate support and fixed-length dependency walks is classical
@boolean-monomial. On the finite prediction window, the two shifts make
that support explicit.

= Evolving controls with branching <branching-boundary>

*Uniform transport.* Allow both terms in @frozen-rule and transport the
entire control track by $a_i(t+1)=a_(i+1)(t)$. In the reflected moving
frame $y_j(t)=x_(-j-t)(t)$, substitution gives
$
  y_j(t+1)=h(a_(-j-1)(0)) y_j(t)+s(a_(-j-1)(0)) y_(j+1)(t).
$
The guards are now frozen and exchanged. The observation $x_0(T)$ is
$y_(-T)(T)$, whose data window is the reversal of the original one.
The frozen control window is $a_(T-1)(0),dots,a_0(0)$ followed by a
padding word. At the last virtual site no stay can occur, so the padding
is irrelevant. The two prefix statistics still work in this frame,
with the roles of stay and hop exchanged. Lean verifies the coordinate
change and the per-time circuit reduction, including the input rewiring.

*Additive control evolution.* Now let the control be one bit and evolve
it by $c_i(t+1)=c_i(t)+c_(i+1)(t)$, with data update
$x_i(t+1)=c_i(t)x_i(t)+x_(i+1)(t)$. Both updates use $bb(F)_2$.
At $T=2$, the coefficient of $x_1(0)$ at the origin is
$(c_0(0)+c_1(0))+c_1(0)=c_0(0)$. The initial pairs $(1,0)$ and $(0,1)$
have the same stay count and hop flag for this endpoint, but yield
different coefficients. A stay can now read different guard values
at the same site. Counting how many sites allow a stay at time zero
loses the order information needed for cancellation.

This rule still has a short coefficient description. Put
$Q_T(i)=c_i(T)+c_(i+T)(0)$, the Pascal parity of the initial controls
with its rightmost term removed. For $0 <= k < T$, put
$
  P_(T,k)(i)=product_(j=k+1)^(T-1)(1+c_(i+j)(0)).
$
Then the coefficient of $x_(i+k)(0)$ in $x_i(T)$ is
$P_(T,k)(i) Q_T(i)$ for $k<T$, and one for $k=T$. Thus a single
parity is shared across endpoints, and a suffix-zero test selects
which endpoints receive it.

_Proof._ Write $b_(T,k)(i)$ for the coefficient and take it to be zero
outside the window. The update gives
$
  b_(T+1,k)(i)=c_i(T)b_(T,k)(i)+b_(T,k-1)(i+1).
$
Since a bit squares to itself,
$c_i(T)Q_T(i)=(1+c_(i+T)(0))c_i(T)$. For $k<T$, the stay term
therefore has suffix factor $P_(T+1,k)(i)$, as does the shifted term
because $P_(T,k-1)(i+1)=P_(T+1,k)(i)$ for $k>0$.
For $k=0$ the shifted term is absent, but $Q_T(i+1)$ already
vanishes whenever $P_(T+1,0)(i)=1$: the suffix then zeros every
initial control in that parity. After factoring out the suffix
the sum is $c_i(T)+Q_T(i+1)=Q_(T+1)(i)$.
For $k=T$ the stay term is $c_i(T)$ and the shifted term is
$Q_T(i+1)$, giving the same sum with empty suffix. This also holds
at $T=0$ since $Q_0(i+1)=0$. The all-hop term is always one. #qed

A block of consecutive sites has summary $(Z,V)$, where $Z$ tests
whether its controls are all zero and $V$ is the parity of its data
bits with only zero controls to their right within the block. A single
site has summary $(1+c_j(0),x_j(0))$. Concatenating blocks combines
their summaries by
$
  (Z_L,V_L),(Z_R,V_R) |-> (Z_L Z_R,V_L Z_R+V_R).
$
A balanced tree computes $V$ on the first $T$ sites, with empty
summary $(1,0)$. The prediction is $x_T(0)+Q_T(0)V$.
A second tree computes $Q_T(0)$ on the submask wires. The two trees
use $O(T+1)$ gates in total and have depth $O(log(T+2))$.
Their regular layouts can be streamed in logspace.

At positive times the essential inputs are exactly the first $T$
control bits and all $T+1$ data bits. Setting all but $x_0(0)$ to zero
on the data track gives $x_0(0)c_0(0) product_(j=1)^(T-1)(1+c_j(0))$,
which witnesses the control bits. Setting $c_0(0)=1$ and
$c_1(0)=dots=c_(T-1)(0)=0$ gives parity of the data bits. This yields
the depth lower bound $ell(2T+1)$. Lean verifies the coefficient formula
for the actual coupled iterate. The circuit bounds follow from the
argument above.

= Related work

*Pascal parity and fast prediction.* The odd-entry count $2^(p(T))$ is
classical. Rowland attributes the binary count to Glaisher and derives it
from Lucas's theorem @rowland. Moore uses Pascal coefficients to predict
homogeneous additive rules, obtaining logarithmic depth with binary
gates and logspace-uniform $"ACC"^0$ with unbounded modular sums @moore.
Robison gives a serial
method for computing an individual coefficient from one initial seed
@robison. The per-time optimum in @pascal-exact follows from classical
parity complexity. The verified uniform family realizes the Pascal
profile within a constant factor.

*Dependent linear tracks and the coefficient formula.* In @moore,
Lemma 1 composes spacetime transfer coefficients by dividing the time
interval. Theorem 1 applies that algorithm to quasidirect products.
Examples 1 and 3 cover binary data tracks controlled by another track
and triangular linear tracks such as our additive-control example.
With balanced XOR trees for the modular sums,
the general method gives an $O(log^2(T+2))$ bound for our binary tracks.
Time invariance and the one-sided stencil reduce the frozen coefficients
to prefix statistics. In §3, Salo studies the sitewise choice between
identity and right-neighbor XOR on a finite ring @salo.
That example uses the local maps of $s equiv 1$, $h(a)=a$ and concerns
surjectivity and periodicity. Here the control word is part of the input
and the output is one finite-window prediction bit.

Parallel prefix circuits are classical @ladner-fischer. Balanced
products, carry-save counting, and coefficient tests give the frozen
predictor's $O(log(T+2))$ bound. The coefficient in @frozen-sum also
has a classical matrix analogue.
The one-step data map is upper bidiagonal on the relevant finite window.
Higham's Theorem 6.1 for functions of such matrices gives
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
The contribution here is the executable four-way classification,
the matching logarithmic bounds for varying guards, and the proof that
one logspace generator per rule achieves the stated upper bounds across
all lengths. The comparisons above leave priority for this combination open.

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

The accompanying Lean development formalizes three sufficient criteria for
prediction problems. A compiles resource-bounded composition circuits into
a predictor. B transfers P-hardness from circuit evaluation given a
logspace simulation witness. Exclusion from uniform $"NC"$ via B assumes
$"P" != "NC"$ and is a complexity-class statement. C gives an unconditional
depth lower bound from essential inputs. At fixed
fan-in, dimension, radius, and bit width, a polynomial-volume light cone
limits the *counting bound* from C to $O(log(T+2))$. Actual prediction
depth can exceed this bound. Lean checks supplied witnesses. Finding
witnesses for arbitrary rules is a separate problem. In the frozen family,
the executable classifier selects the depth branch by testing guard
constancy on a fixed finite alphabet.

= Conclusion

For frozen controls, guard constancy decides the constant-depth cases,
and prefix statistics give a uniform logarithmic-depth predictor for
varying guards. The Pascal depth is governed by the set bits of the
observation time. With branching, uniform transport preserves the frozen
summary after a change of frame, while additive control evolution needs
a different summary even with all hops enabled. In the latter example,
the induction closes because the all-hop coefficient is fixed and the
control evolves by Pascal convolution. It remains to determine when a
comparable coefficient recurrence closes if the evolving control also
gates the hops.

#heading(numbering: none)[Artifact availability]

The Lean and Typst sources and the build instructions are in the
#link("https://github.com/miuchan/structural-certificates-for-prediction-depth")[project repository].
Use the repository snapshot accompanying this PDF for the declarations
listed in @lean-map.
The repository documents the pinned Typst and font inputs for rebuilding
all four editions. Run #box[`./scripts/check.sh`] for the strict Lean build,
transitive axiom audit, and negative regression. The repository's
verification guide separates build evidence from review of the model
assumptions. @lean-map lists the declarations behind the main results.

#counter(heading).update(0)
#set heading(numbering: "A.1")
#heading(supplement: [Appendix])[Generator layout and depth budget] <depth-budget>

Put $m=T+1$ and $B=ell(T+3)+1$. The register stores the time tag $tau$,
the stay and hop flags, and the data in four blocks of width $m$. The
tag starts at index zero. Reading the binary digits of $T$ from most
significant to least, each stage doubles the index and increments it
when the digit is one. These operations route wires with zero fill.

At site $k$, the decoder enumerates $0 <= u < m$ and $0 <= j <= k+1$.
For a row with $u>=k$ and odd $M(j,u-k)$ it emits the test
$(w_k=j) and tau_u$. All other rows are zero. Parity over $j$, then
$u$, selects the coefficient. The decoder multiplies by the hop prefix
and data and takes parity over $k$.

The normalized counter tree costs at most $2+14b$ layers, including
initialization and copying in each merge round, for a counter of word
width $b=ell(a+1)$ on $a$ bits. The finishing addition costs at most
$1+8b$. Together they cost at most $22(b+1)$.
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

The table has $m^2(m+3)/2$ rows and there are $O(m^2)$ counters of at most
$m+1$ input bits. The regular layouts give $O(m^3 log^3(m+1))$ gates for
fixed guards. A gate record is indexed by its stage, block, bit lane and
position in a local template. For parallel banks the serializer counts
earlier blocks to obtain a wire offset. In a chain of width $W$, identity
gates $y and y$ give the stage outputs consecutive indices. After $G$
gates on $N$ primary inputs, output slot $a$ of that stage is wire
$N+G-W+a$. This lets the serializer recompute references with counters
of logarithmic width and fixed nesting depth. It streams the gate and
output lists from the unary length.

#block(breakable: false)[
#set text(size: 9.5pt)
#heading(supplement: [Appendix])[Lean correspondence] <lean-map>

The paths below are relative to `PredictionDepth/`.

#table(
  columns: (1fr, 2.55fr),
  inset: (x: 7pt, y: 3pt),
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
  [Pascal support and XOR depth], [`FrozenPascal/HomogeneousPascal.lean` #linebreak()
    `pascalSupport_card` #linebreak() `homogeneousNativeXorPrediction_depth`],
  [Exact Pascal De Morgan depth], [`FrozenPascal/PascalExactDepth.lean` #linebreak()
    `homogeneous_prediction_deMorgan_exact_depth`],
  [Transported control], [`TransportedControl.lean` #linebreak()
    `iterate_data_true_iff`, `essential_prediction_iff` #linebreak()
    `exact_prediction_depth`, `constant_depth_iff`],
  [Branching under transport], [`TransportedBranching.lean` #linebreak()
    `reverseFrame_iterate`, `prediction_correct` #linebreak()
    `prediction_depth`, `prediction_size`],
  [Additive-control coefficients], [`AdditiveBranching.lean` #linebreak()
    `trimmedParity_eq_sum`, `iterate_data`],
  table.hline(stroke: 0.7pt),
)

]

#block(breakable: false)[
  #bibliography("references.bib", style: "ieee", title: [References])
]
