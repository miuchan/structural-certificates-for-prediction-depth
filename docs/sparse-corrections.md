# Sparse Corrections as Certificates for Fast Prediction

[Formal scope](requirements.md) · [Related work](literature.md) · [Verification](verification.md)

**Status:** The sparse phase is complete against the three criteria in §1.1. Lean verifies the enumeration and repair compilers and their logspace generators. Section 11 records the original design, and §16 maps its implementation items to evidence.

**Scope:** Exact prediction for fixed deterministic local Boolean dynamics on explicit finite dependency regions, with circuit size, depth, and logspace uniformity accounted for.

**Original specification baseline:** [4f5442c7f412ff39b818e6f0443fcf0b4a2aeb9b](https://github.com/miuchan/structural-certificates-for-prediction-depth/tree/4f5442c7f412ff39b818e6f0443fcf0b4a2aeb9b).

## 1. Purpose and main results

A trajectory can be complicated as a Boolean computation while differing from a tractable reference evolution at only a few space-time coordinates. This document gives a sufficient certificate for predicting such a trajectory in shallow depth.

The certificate has three components:

1. A uniform shallow circuit family reconstructing the entire relevant trajectory of a linear reference system under arbitrary additive forcing.
2. A restriction on the support of the discrepancy between the actual trajectory and that reference system.
3. A verifier checking every actual local update in the complete dependency region.

The algorithm enumerates candidate corrections, reconstructs all candidate trajectories in parallel, checks their local consistency, and selects the observation of a valid trajectory. Determinism makes a complete consistency check sufficient.

There are two different support restrictions.

| Support information | Number of candidates | Depth bound | Polynomial-size, logarithmic-depth regime |
| --- | --- | --- | --- |
| At most k nonzero correction bits, at unknown locations | At most (M + 1)^k | O(D_ref + log(V + 1) + k log(M + 1)) | Every fixed k, when D_ref = O(log(V + 1)) |
| Corrections supported on a known set of K possible bit locations | 2^K | O(D_ref + log(V + 1) + K) | K = O(log n), with a uniform schedule and shallow reference response |

Here:

- n is the actual initial-input length;
- M is the number of possible correction-bit locations;
- V is the number of state bits in the complete finite dependency region;
- D_ref is the depth of the supplied forced-response circuit;
- the reference circuit has size polynomial in V;
- V is polynomially bounded in n.

The resulting circuits compute two bits: whether the support condition holds, and the requested observation gated by that condition. Consequently, the construction both recognizes its applicability and predicts correctly on the accepted inputs.

The first regime does not require the correction locations to be known in advance. The second regime permits more possible locations because their addresses are already supplied by a uniform structural description.

The intended contribution is a precise certificate, its resource accounting, and useful dynamical applications. Parallel enumeration of short certificates and decomposition around a tractable background have substantial precedents; Section 14 records the relevant comparisons.

### 1.1 Completion criteria

1. **Certificate.** Fix the deterministic local rule, linear reference, radius, track count, and observed track. Use explicit initial words of length $n=q(2RT+1)$. Assume a logspace-uniform full forced-response circuit of size $S_{\rm ref}$ and depth $D_{\rm ref}$ with the complete cone layout and local checks. For $N$ indexed correction candidates the compiler returns $(A,A\land g_T)$, where $A$ tests membership of the actual residual in the candidate family. It uses $O(N(S_{\rm ref}+V+1))$ gates and depth $D_{\rm ref}+O(\log(V+1)+\log(N+1))$. The two enumeration regimes and the repair bounds follow from the same response and verifier. The length wrapper rejects illegal lengths. [Compiler](../PredictionDepth/SparseCorrections/Compiler.lean) · [Uniform certificate](../PredictionDepth/SparseCorrections/Certificate.lean) · [Repair bounds](../PredictionDepth/SparseCorrections/RepairUniform.lean)
2. **System-level application.** For the fixed reversible three-track rule, every legal window with at most two occupied bits has residual weight at most two. The fixed-budget certificate therefore gives exact prediction on the entire promised class. [Application](#104-all-two-particle-initial-windows)
3. **Boundary.** The certificate gives sufficient upper bounds. OR has a quadratic residual on an explicit family of inputs while its unrestricted prediction has logarithmic depth. A separate fan-in-two lower bound gives the optimal depth order on the two-particle promise. [Counterexample and lower bound](#132-limits-of-the-statement)

## 2. Model and input encoding

### 2.1 Fixed local dynamics

Fix:

- a positive integer q, the number of Boolean tracks per site;
- a common radius R >= 1;
- a deterministic local rule F on configurations in (F_2^q)^Z;
- a linear local reference rule L on the same configuration space;
- a fixed observed track a_* at site zero.

Both F and L have radius at most R. The choice R >= 1 is a convenient over-approximation even when either rule has radius zero.

The same finite local map f is used at every site, so

$$
(Fx)_i=f(x_{i-R},\ldots,x_{i+R}).
$$

The linear reference is specified by fixed q-by-q matrices A_delta over F_2:

$$
(Lx)_i=\sum_{\delta=-R}^{R}A_\delta x_{i+\delta}.
$$

Thus position-dependent rule tables are not hidden in the uniformity assumptions.

The rule, the number of tracks, the radius, and the observed track are fixed throughout each circuit family. They are not additional variable-length inputs. Local evaluation of F therefore has a fixed-size Boolean circuit of fixed depth d_F.

The prediction time is T >= 0. The observation is

$$
g_T(u) = [F^T(x)]_{0,a_*},
$$

where x is any infinite extension of the supplied initial window u. Locality will make the choice of extension irrelevant.

### 2.2 Complete common dependency region

For each 0 <= t <= T, define the spatial window

$$
W_t = \{-R(T-t),\ldots,R(T-t)\}
$$

and the bit-index set

$$
B_t = W_t \times \{0,\ldots,q-1\}.
$$

The initial input is u in F_2^{B_0}. Its length is

$$
n_T = |B_0| = q(2RT+1).
$$

Every predecessor needed to evaluate F or L at a site in W_{t+1} lies in W_t. This is the common-cone closure property.

Let

$$
\mathcal V_T = \bigsqcup_{t=0}^{T}\{t\}\times B_t,
\qquad
V_T = |\mathcal V_T| = q(T+1)(RT+1).
$$

A correction bit belongs to the output of an update. Define

$$
\mathcal E_T =
\bigsqcup_{t=0}^{T-1}\{t\}\times B_{t+1},
\qquad
M_T = |\mathcal E_T| = q\bigl(RT(T-1)+T\bigr).
$$

An event (t,i,a) means a correction to track a at site i in the update from time t to time t+1. It does not mean a correction to the state before that update.

For fixed q and R,

$$
V_T = O(n_T^2),
\qquad
\log(V_T+1) = O(\log(n_T+1)).
$$

The input length determines T on legal lengths. A logspace generator checks whether n has the form q(2RT+1), recovers T, and emits a rejecting circuit at other lengths. All bit strings of a legal length encode valid Boolean initial states.

A different encoding, such as binary time plus a succinct initial state, requires a separate complexity statement.

### 2.3 Finite transitions

Restrict the two local rules to the shrinking windows:

$$
F_t : \mathbb F_2^{B_t}\longrightarrow\mathbb F_2^{B_{t+1}},
\qquad
L_t : \mathbb F_2^{B_t}\longrightarrow\mathbb F_2^{B_{t+1}}.
$$

Each L_t is linear. The maps are generally rectangular: their input and output dimensions differ.

For an initial input u, define the actual finite trajectory by

$$
x_0=u,\qquad x_{t+1}=F_t(x_t).
$$

Induction using common-cone closure proves that x_t is the restriction of F^t(x) to B_t for every infinite extension x of u. In particular, x_T(0,a_*) is the desired observation.

This finite formulation avoids imposing an artificial boundary condition inside a region that could influence the observation.

### 2.4 Circuit model

Use Boolean circuits with fan-in at most two, arbitrary wiring, and sharing. The upper bounds can be implemented over binary AND, binary OR, and unary NOT. XOR is an abbreviation implemented by a fixed constant-size, constant-depth gadget.

Constant zero and one sources are permitted. Their translation into the repository's serialized gate representation is included in the initialization and normalization overhead. This convention also defines the rejecting circuit at input length zero and the values of empty reductions.

Depth counts gates on a longest input-output path. A projection has depth zero. All resource bounds include local-rule evaluation, equality tests, balanced reductions, input and output normalization, and serialization overhead.

The upper bounds are not claims of optimal depth. They also do not measure time on a physically local wiring architecture.

For asymptotic displays, logarithms are base two. Use log(m+1) or max(1,m) where needed to include empty structures. The Lean implementation should use integer ceiling logarithms and explicit zero cases.

## 3. Corrections and admissible inputs

### 3.1 Actual correction vector

For the actual trajectory, define

$$
e_t^F(u)=x_{t+1}+L_t x_t
       =F_t(x_t)+L_t x_t.
$$

Addition is over F_2, so it is bitwise XOR.

Concatenate these vectors into

$$
e^F_T(u)\in\mathbb F_2^{\mathcal E_T}.
$$

Its support and weight are

$$
\operatorname{supp}(e^F_T(u))
=\{v\in\mathcal E_T:e^F_T(u)_v=1\},
$$

$$
w_T^F(u)=|\operatorname{supp}(e^F_T(u))|.
$$

The first admissibility predicate is

$$
\operatorname{Sparse}_{T,k}(u)
\quad\Longleftrightarrow\quad
w_T^F(u)\le k.
$$

The locations may depend on u. No oracle locating them is assumed.

### 3.2 Known candidate locations

Let J_T be a specified subset of E_T, with cardinality K_T. Define

$$
\operatorname{Supported}_{T,J}(u)
\quad\Longleftrightarrow\quad
\operatorname{supp}(e^F_T(u))\subseteq J_T.
$$

For the initial uniform theorem, J_T is independent of the contents of u and has a logspace-computable indexed listing. The list contains distinct valid event addresses.

An input-dependent list supplied as extra input is a possible extension. Its encoding, validity checks, address selection, and generation costs must then be included. It is not covered implicitly by the input-independent theorem.

### 3.3 Interpretation of the parameter

The parameter counts actual nonzero residual bits relative to a fixed reference, on the particular trajectory and horizon being queried.

It does not count:

- the nonlinear gates in a space-time circuit;
- all locations at which the rule could act nonlinearly on some other input;
- the number of cells whose states change;
- the number of changes per cell;
- the number of initially occupied cells.

The reference L is fixed independently of the input. Choosing an arbitrary input-specific reference without paying to describe and construct it is outside the model.

For q tracks, counting nonzero correction vectors per site-update is another valid convention. A bound of k such events implies at most qk nonzero correction bits. The exact enumeration count for vector events includes their nonzero values:

$$
\sum_{j\le k}\binom{M_{\rm site}}j(2^q-1)^j.
$$

This document consistently uses correction-bit locations, so a nonzero correction value is always one.

## 4. Uniform forced linear response

### 4.1 Required interface

For any initial window u and arbitrary correction vector e, define the forced reference trajectory by

$$
y_0=u,\qquad y_{t+1}=L_t y_t+e_t.
$$

A forced-response family supplies a Boolean circuit

$$
\mathcal R_T:
\mathbb F_2^{B_0}\times\mathbb F_2^{\mathcal E_T}
\longrightarrow
\mathbb F_2^{\mathcal V_T}
$$

which outputs every y_t in the dependency region.

The interface obligations are:

| Obligation | Required evidence |
| --- | --- |
| Semantics | Every output layer satisfies the forced recurrence and the initial layer equals u |
| Size | A bound S_ref(T) polynomial in V_T for the NC consequences |
| Depth | A proved bound D_ref(T) |
| Coordinates | Explicit input, event, and trajectory-output orderings |
| Uniformity | A deterministic O(log(n_T+1))-space transducer emitting the complete circuit and its wiring |
| Bounds | Logspace-computable polynomial output-size and layout bounds suitable for the serializer |

The main NC^1 corollaries assume

$$
D_{\rm ref}(T)=O(\log(V_T+1)),
\qquad
S_{\rm ref}(T)\le(V_T+1)^c
$$

for a fixed c.

Linearity alone is not this witness. A semantic matrix-power formula without a circuit construction and generator does not establish the uniform hypothesis.

### 4.2 Propagators and the reconstruction formula

For 0 <= s <= t <= T, define

$$
P_{s,t}=
\begin{cases}
I,&s=t,\\
L_{t-1}\cdots L_s,&s<t.
\end{cases}
$$

Thus P_{s,t} maps the state space on B_s to the state space on B_t, and

$$
P_{r,t}=P_{s,t}P_{r,s}
\qquad(r\le s\le t).
$$

The forced recurrence has the solution

$$
y_t
=
P_{0,t}u+
\sum_{s=0}^{t-1}P_{s+1,t}e_s.
\tag{1}
$$

**Proof.** The t=0 case is y_0=u. Applying L_t to the formula for y_t and adding e_t gives the formula for y_{t+1}, using linearity and propagator composition. Induction proves (1). The recurrence also determines a unique trajectory. QED.

Writing L^t is justified only after identifying these finite propagators with restrictions of powers of a global homogeneous operator. The rectangular formulation is the primary finite theorem.

### 4.3 Constructing the interface from interval responses

One sufficient implementation route supplies uniform circuits for all P_{s,t} with compatible bounds, not only for a single final observation.

For each t, compute P_{0,t}u and all P_{s+1,t}e_s in parallel, then use balanced XOR trees to sum the contributions. Do this for every t simultaneously.

There are O((T+1)^2) source-target time pairs and polynomially many output coordinates. Consequently:

- polynomial-size interval-response families yield a polynomial-size full-response family;
- the summation adds O(log(T+2)) depth;
- the full generator must emit the interval circuits, their input substitutions, and their cross-block wiring in logspace.

In particular, interval-response depth O(log(T+2)) suffices for full-response depth O(log(T+2)).

The reference family must reconstruct all states needed by the verifier. A circuit for the final observation alone is insufficient without this additional construction.

## 5. Reconstruction and complete verification

### 5.1 Candidate trajectories

For a candidate correction vector e, let

$$
Y_T(u,e)=\mathcal R_T(u,e).
$$

Equivalently, define it by the forced recurrence; the response witness proves equality with the circuit output.

When e is the characteristic vector of a set E, write Y_T(u,E).

### 5.2 Verifier

Define

$$
\operatorname{Valid}_T(u,e)
=
\bigwedge_{t=0}^{T-1}
\bigwedge_{b\in B_{t+1}}
\left[
Y_T(u,e)_{t+1,b}
=
F_t\bigl(Y_T(u,e)_t\bigr)_b
\right].
\tag{2}
$$

The initial layer already equals u by the response contract.

The verifier covers every update-output bit in the complete common cone, including coordinates whose proposed correction is zero. Checking only guessed event locations would allow unaccounted discrepancies elsewhere and would invalidate the construction.

Because q and R are fixed, each local condition has constant size and depth after its candidate inputs have been computed. All conditions are evaluated in parallel. Their final conjunction is a balanced tree.

### 5.3 Soundness, completeness, and uniqueness

**Lemma 1, completeness.**

$$
Y_T(u,e^F_T(u))=(x_0,\ldots,x_T)
$$

and Valid_T(u,e^F_T(u)) is true.

**Proof.** By definition of the actual residual,

$$
x_{t+1}=L_t x_t+e_t^F(u).
$$

The actual trajectory therefore satisfies the forced recurrence with the same initial state. Uniqueness of that recurrence proves reconstruction; every actual local update then passes (2). QED.

**Lemma 2, soundness.**

If Valid_T(u,e) is true, then Y_T(u,e) is the actual finite trajectory.

**Proof.** Both trajectories start at u. If their layers agree at time t, all verified local equations imply that their layers agree at time t+1. Induction covers the whole cone. QED.

**Lemma 3, uniqueness of the correction vector.**

$$
\operatorname{Valid}_T(u,e)
\quad\Longleftrightarrow\quad
e=e^F_T(u).
\tag{3}
$$

**Proof.** Completeness gives one direction. For the other, soundness gives the actual trajectory, and the forced recurrence gives

$$
e_t=Y_{t+1}+L_tY_t=e_t^F(u).
$$

Thus every correction bit agrees. QED.

A canonical enumeration contains exactly one valid candidate when the actual correction vector is included. An implementation with repeated encodings remains correct because all valid encodings reconstruct the same trajectory and observation.

## 6. General enumeration compiler

Let C_T be a nonempty finite family of correction vectors, independent of the input contents. Write N_T=|C_T|.

For each e in C_T, instantiate one copy of the response circuit with the correction inputs fixed to e. Compute its validity bit and its candidate observation.

Define the two outputs

$$
A_T(u)=
\bigvee_{e\in C_T}\operatorname{Valid}_T(u,e),
$$

$$
\operatorname{out}_T(u)=
\bigvee_{e\in C_T}
\left(
\operatorname{Valid}_T(u,e)
\land
[Y_T(u,e)_T]_{0,a_*}
\right).
\tag{4}
$$

The symbol N_T counts candidates; out_T denotes the output bit.

### Theorem 1: certified prediction

For every initial input u,

$$
A_T(u)=1
\quad\Longleftrightarrow\quad
e^F_T(u)\in C_T,
$$

and

$$
\operatorname{out}_T(u)
=
A_T(u)\land g_T(u).
\tag{5}
$$

**Proof.** Equation (3) identifies the valid candidates exactly. If none exists, both outputs are zero. If a valid candidate exists, its reconstructed trajectory is the actual one, so its candidate observation is g_T(u). All valid copies agree. Equation (4) proves (5). QED.

The acceptance bit distinguishes an inadmissible input from an admissible input whose observation is zero. This distinction is part of the public specification.

### Circuit resources

There is a constant C depending on the fixed local rule and gate conventions such that

$$
S_{\rm total}(T)
\le
C N_T\bigl(S_{\rm ref}(T)+V_T+1\bigr),
\tag{6}
$$

$$
D_{\rm total}(T)
\le
D_{\rm ref}(T)+d_F+
O\bigl(\log(M_T+1)+\log(N_T+1)+1\bigr).
\tag{7}
$$

These are convenient bounds, not optimized gate counts.

For each candidate:

1. Constant substitution into the response family costs at most linear initialization and normalization overhead.
2. All local F checks add O(V_T) gates and fixed local depth.
3. Combining the checks adds O(log(M_T+1)) depth.
4. Gating the candidate observation adds constant depth.

The two final OR trees add O(N_T) gates and O(log(N_T+1)) depth. The entire construction remains deterministic. Enumeration is realized by parallel circuit copies, not by a sequential search.

Circuit descriptions include gate addresses and wiring. For a gate bound $G$ and $w=\lfloor\log_2(n+G)\rfloor+1$ using Lean’s zero convention, the checked two-output encoding has length at most
$$
2n+1+2G(8w+23)+1+2(2w+1).
$$
This counts the unary input-arity header, operation fields, list framing, and both output addresses. Substitute the actual compiler gate bound for $G$ to obtain the explicit description bound. [Encoding proof](../PredictionDepth/SparseCorrections/Description.lean)

For T=0, M_T=0 and there is only the empty correction vector. The verifier is the empty conjunction, A_T=1, and the prediction is the selected initial wire. No asymptotic logarithm is needed to define this case.

## 7. Unknown correction positions

Take

$$
C_{T,k}
=
\{e\in\mathbb F_2^{\mathcal E_T}:|\operatorname{supp}(e)|\le k\}.
$$

Its cardinality is

$$
N_{T,k}
=
\sum_{j=0}^{\min(k,M_T)}\binom{M_T}{j}
\le(M_T+1)^k,
\tag{8}
$$

with the convention (M_T+1)^0=1.

One proof of the bound encodes a sorted support of size at most k by a length-k tuple of event identifiers padded with a distinguished zero symbol.

### Theorem 2: sparse corrections at unknown locations

For every T and k, the enumeration compiler computes

$$
A_{T,k}(u)=
[\operatorname{Sparse}_{T,k}(u)]
$$

and

$$
\operatorname{out}_{T,k}(u)=
[\operatorname{Sparse}_{T,k}(u)]\land g_T(u).
$$

It has size

$$
O\left(
N_{T,k}(S_{\rm ref}(T)+V_T+1)
\right)
$$

and depth

$$
D_{\rm ref}(T)+d_F+
O\left(
\log(V_T+1)+k\log(M_T+1)
\right).
\tag{9}
$$

**Proof.** Use C_{T,k} in Theorem 1 and substitute (8) into the resource bounds. QED.

### Corollary: every fixed sparse slice is in uniform NC^1

Suppose the forced-response family is logspace-uniform, has polynomial size, and has logarithmic depth. For each fixed natural number k, both applicability and gated prediction are computable by a logspace-uniform polynomial-size O(log(n_T+1))-depth family.

The quantifier order is:

> For every fixed F, L, response witness, and fixed k, there exists one uniform circuit family handling all horizons and all initial inputs.

The polynomial exponent may depend on k. The construction does not establish a bound of the form f(k)n^c with c independent of k.

If k is allowed to grow as O(log n) while its locations remain unknown, this enumeration generally has n^{O(log n)} size. That is a different resource regime and does not yield the stated NC^1 consequence.

## 8. Known candidate locations

Let J_T have K_T distinct event-bit locations. Enumerate all 2^{K_T} assignments on J_T and extend each assignment by zero outside J_T.

### Theorem 3: corrections on a supplied uniform support

The compiler computes

$$
A_{T,J}(u)=
[\operatorname{Supported}_{T,J}(u)]
$$

and

$$
\operatorname{out}_{T,J}(u)
=
[\operatorname{Supported}_{T,J}(u)]\land g_T(u),
$$

with size

$$
O\left(
2^{K_T}(S_{\rm ref}(T)+V_T+1)
\right)
$$

and depth

$$
D_{\rm ref}(T)+d_F+
O\bigl(\log(V_T+1)+K_T\bigr).
\tag{10}
$$

**Proof.** The candidate family contains exactly the vectors supported in J_T. Apply Theorem 1 and use log(2^{K_T})=K_T. QED.

### Corollary: logarithmically many possible locations

Assume:

- the reference response satisfies the shallow uniform hypothesis;
- J_T and K_T have logspace-computable indexed descriptions;
- K_T <= c log_2(n_T+2) for a fixed constant c.

Then both outputs belong to logspace-uniform NC^1.

The support condition is checked by the full verifier. The positions are candidates, not a promise that every listed position actually produces a correction.

Knowing the positions of K possible corrections is different from only knowing that there are K actual corrections. The first permits 2^K assignments; the second also requires encoding their addresses.

## 9. Uniformity obligations

Semantic correctness and circuit existence are separate from uniform NC membership. The implementation should discharge the following obligations explicitly.

### 9.1 Indexing and finite geometry

Supply logspace routines for:

- recognizing legal input lengths and recovering T;
- enumerating the bit coordinates of each layer;
- converting an event identifier to its update time, site, and track;
- finding the predecessor addresses for each local F check;
- locating the observed output;
- calculating polynomial layout and gate-count bounds.

The formulas in Section 2 make these tasks elementary for fixed q and R, but their connection to the serialized circuit must still be proved.

### 9.2 Candidate generation

For fixed k, enumerate canonical sorted supports or padded k-tuples. Storing k event identifiers uses O(k log(M_T+1)) = O(log(n_T+1)) workspace. Invalid or repeated encodings may be skipped or assigned a permanently false validity bit.

For known J_T with K_T=O(log n), a K_T-bit assignment counter uses O(log n) workspace. Site addresses can be regenerated from the indexed schedule instead of storing the entire list.

These arguments justify uniformity in the specified regimes. They do not assert O(log n)-space generation for arbitrary variable k or arbitrary variable K.

### 9.3 Reference circuits and composition

The generator must emit a complete response circuit for each candidate with the correct constant inputs. It must also emit local checks, balancing trees, normalization gates, and the final two outputs.

Hardwired response coefficients are permitted only when their generation is included in the witness. Alternatively, the generator may emit circuits computing those coefficients and charge their depth and size.

A nonuniform existence proof for the response family does not establish a uniform prediction theorem.

### 9.4 Applicability language and promise prediction

For fixed k, define the total language

$$
\mathcal L_k
=
\{u:\operatorname{Sparse}_{T,k}(u)\land g_T(u)=1\},
$$

with rejection at illegal lengths.

The construction proves this language is in uniform NC^1 and separately decides Sparse_{T,k}. On the promise Sparse_{T,k}, its value output is exact prediction.

An application claiming an upper bound for all its allowed initial inputs must prove that those inputs satisfy the support condition. If only a subclass satisfies it, the theorem applies to that subclass.

## 10. Concrete reference families and examples

### 10.1 Pascal reference

For a single Boolean track, take

$$
(Lx)_i=x_i+x_{i+1}.
$$

The homogeneous response has coefficients

$$
(L^\tau x)_i
=
\sum_{j=0}^{\tau}
\left(\binom{\tau}{j}\bmod2\right)x_{i+j}.
$$

A coefficient is one exactly when every set bit of j is also a set bit of tau. This supplies a simple logspace coefficient generator; balanced XOR trees give shallow response circuits. The repository already formalizes the corresponding homogeneous Pascal semantics and support structure in [FrozenPascal/HomogeneousPascal.lean](../PredictionDepth/FrozenPascal/HomogeneousPascal.lean).

For arbitrary forcing, compute the initial response and every impulse contribution in parallel, then sum them as in (1). This yields a polynomial-size O(log(T+2))-depth full-response family. `Pascal.circuit_correct` checks every output for arbitrary forcing, and `Pascal.circuit_code_logspace` verifies generation of the complete circuit. The construction uses the indexed Lucas coefficients and the common cone layout. [Full Pascal response](../PredictionDepth/SparseCorrections/PascalResponse.lean)

A useful verification rule is

$$
(Fx)_i=x_i\lor x_{i+1}
      =x_i+x_{i+1}+x_ix_{i+1}.
$$

Its correction relative to Pascal is x_ix_{i+1}. Its independent closed form,

$$
(F^T x)_0=\bigvee_{j=0}^{T}x_j,
$$

provides a direct check of the candidate compiler on accepted inputs. The unrestricted OR predictor is itself a shallow parallel algorithm. `Pascal.orPredictor_correct` compares the gated output of the sparse compiler with this independent disjunction for every horizon and input. [OR certificate](../PredictionDepth/SparseCorrections/PascalOR.lean)

### 10.2 A reversible three-track collision rule

Use three tracks (a,b,c). At each site, apply a local permutation C which cycles the three states of Hamming weight two:

$$
110\longmapsto101\longmapsto011\longmapsto110,
$$

and fixes 000, 001, 010, 100, and 111.

Then stream a one site to the right, b one site to the left, and leave c stationary. If z_i=C(a_i,b_i,c_i), define

$$
F(a,b,c)_i=(z^a_{i-1},z^b_{i+1},z^c_i).
$$

Choose free streaming as the reference:

$$
L(a,b,c)_i=(a_{i-1},b_{i+1},c_i).
$$

This is a fixed radius-one system. The following properties follow directly from the definition:

- C is a permutation, and streaming is invertible, so the global F is reversible.
- C preserves local Hamming weight, and streaming preserves the total particle count for finite-support configurations.
- C fixes the three basis vectors but changes 110, so C is not linear.
- Each nontrivial collision changes exactly two bits relative to the local identity. Streaming relocates those two discrepancies without changing their total count.

The correction count inside a target cone may be smaller than the global count because some resulting corrections lie outside that cone.

An unforced interval response of L is just a rewire. A full forced response is a parity of the initial bit and the forcing bits along a characteristic:

$$
a_i(t)=a_{i-t}(0)+
\sum_{s=0}^{t-1}e^a_{s,\,i-(t-1-s)},
$$

$$
b_i(t)=b_{i+t}(0)+
\sum_{s=0}^{t-1}e^b_{s,\,i+(t-1-s)},
$$

$$
c_i(t)=c_i(0)+\sum_{s=0}^{t-1}e^c_{s,i}.
$$

Each output has at most T+1 terms. The complete forced response therefore has depth O(log(T+2)), polynomial size, and elementary uniform wiring. Its depth is not zero merely because unforced streaming is a rewire.

### 10.3 An explicit family with two causally linked collisions

For any integer ell >= 1, initialize

$$
a_0(0)=1,\qquad c_0(0)=1,\qquad c_{-\ell}(0)=1,
$$

and set all other bits to zero. Query a_0 at T=2ell.

| Time before update | Relevant state | Consequence |
| --- | --- | --- |
| 0 | Site 0 is 101 | Collision 101 -> 011 sends a b-particle left and keeps c at 0 |
| ell | Site -ell is 011 | Collision 011 -> 110 creates a right-moving a-particle, removes c at -ell, and sends b onward to the left |
| 2ell | The returning a-particle reaches site 0 | The observation is a_0(2ell)=1 |

Between these times, the particles stream without other collisions. The next possible collision at site zero starts at time 2ell, after the queried state has been reached.

There are exactly two nontrivial collisions during updates 0 through 2ell-1 and exactly four global nonzero correction bits. Hence the complete target cone contains at most four correction bits, and Theorem 2 with k=4 applies.

With the update-time convention of Section 2, the four global corrections are

$$
e^a_{0,1}=1,\quad e^b_{0,-1}=1,\quad
e^a_{\ell,-\ell+1}=1,\quad e^c_{\ell,-\ell}=1.
$$

The last correction lies outside the target cone: at state time ell+1 its position is -ell, while the remaining cone radius is ell-1. Thus the target cone actually contains three correction bits; the bound of four is a convenient global upper bound.

Removing either stationary particle makes the queried returning a-particle absent. The two interactions therefore have a causal role in the observation.

This family witnesses nonempty, interacting admissible trajectories at arbitrarily large horizons. It does not establish a lower bound for unrestricted prediction of this collision rule. The certificate applies to every input of this fixed rule satisfying the residual budget, not only to this explicitly solvable family.

### 10.4 All two-particle initial windows

Use the same fixed collision and streaming rules as in §10.2. For every horizon $T$, consider **all** length-$3(2T+1)$ initial words with at most two occupied track bits. The particles can occupy arbitrary sites and tracks in the initial window. Extend the word by zero outside the window.

**Budget theorem.** Every word in this class has at most two nonzero residual bits in the complete dependency cone.

**Proof.** The global particle count is conserved. If a first nontrivial collision occurs, both particles must be at its site because a collision requires local weight two. The permutation leaves them on distinct tracks. These tracks have distinct velocities in $\{-1,0,1\}$, so after streaming they lie at different sites. Under subsequent free streaming their positions are $i+r v_1$ and $i+r v_2$ for $r\ge1$, which are unequal. Induction on $r$ therefore gives free streaming forever after the collision. The one collision changes two bits before streaming, which permutes their addresses. All other updates have zero global residual. By cone closure, each cone residual equals the corresponding global residual for the chosen extension. Restricting to the cone can only discard residual bits. [Lean budget theorem](../PredictionDepth/SparseCorrections/CollisionProperties.lean) · [Cone restriction](../PredictionDepth/SparseCorrections/Semantics.lean)

With $k=2$, the existing certificate accepts every word in the class and returns the actual $a$ bit at the origin. The streaming response uses $O(V(T+1))$ gates and logarithmic depth. Two bit-repair rounds plus the final check give a logspace-uniform predictor of size $O((T+1)^3)$ and depth $O(\log(T+2))$, since $V=3(T+1)^2$. The applicability bit continues to test the residual budget on every legal word. [Two-round correctness](../PredictionDepth/SparseCorrections/RepairExamples.lean) · [Fixed-round uniformity](../PredictionDepth/SparseCorrections/RepairUniform.lean)

## 11. Lean formalization plan

### 11.1 Module responsibilities

The table records the original proposed module split. The implemented paths and declaration names are listed in Section 16.

| Proposed module | Responsibility |
| --- | --- |
| `PredictionDepth/SparseCorrections/Semantics.lean` | Finite layers, local transitions, actual trajectory, residual support, admissibility |
| `PredictionDepth/SparseCorrections/Reconstruction.lean` | Propagators, forced recurrence, reconstruction formula, uniqueness |
| `PredictionDepth/SparseCorrections/Verification.lean` | Complete local verifier, soundness, completeness, unique valid correction |
| `PredictionDepth/SparseCorrections/Compiler.lean` | General candidate-family compiler and size/depth bounds |
| `PredictionDepth/SparseCorrections/Uniform.lean` | Candidate enumeration, serializers, legal lengths, uniform NC^1 corollaries |
| `PredictionDepth/SparseCorrections/Examples.lean` | Pascal response, OR fixture, streaming response, collision rule and explicit family |
| `PredictionDepth/SparseCorrections.lean` | Public entry point for the completed modules |

Use the existing circuit and family infrastructure through narrow interfaces. In particular, separate semantic trajectories from Boolean encodings, circuit implementations, and complete logspace generators.

A future generalization to arbitrary finite acyclic dependency graphs is plausible. The first implementation can use finite time layers and explicit address maps; it need not begin with a new graph library.

### 11.2 Suggested theorem targets

| Proposed theorem name | Intended statement |
| --- | --- |
| `finiteTrajectory_eq_restrict_iterate` | Common-cone evolution agrees with the infinite local system |
| `forcedTrajectory_eq_propagator_sum` | Equation (1) |
| `reconstruct_actualResidual` | Actual corrections reconstruct the actual trajectory |
| `valid_iff_eq_actualResidual` | Equation (3) |
| `compile_accept_iff` | Acceptance characterizes membership in the candidate family |
| `compile_value_eq` | Gated prediction identity (5) |
| `compile_size_le` | General size bound (6) |
| `compile_depth_le` | General depth bound (7) |
| `sparseCandidates_card_le` | Bound (8), including k=0 and M=0 |
| `sparsePrediction_mem_uniformNC_one` | Fixed-k unknown-support consequence |
| `scheduledPrediction_mem_uniformNC_one` | Uniform logarithmic candidate-support consequence |

A forced-response witness should package semantic correctness, size and depth bounds, indexed wiring, and its generator. Avoid hiding any of these obligations in an unconstrained coefficient oracle.

The final constants should follow the actual serializer and gate basis. The asymptotic bounds above do not prescribe unverified exact gate counts.

### 11.3 Implementation milestones

1. Prove the finite semantics and reconstruction identity without circuit code.
2. Prove the complete verifier theorem and uniqueness of the valid residual.
3. Compile an arbitrary finite candidate family with an acceptance bit and a gated value bit.
4. Instantiate fixed-k unknown-position enumeration and prove resource bounds.
5. Implement the full forced Pascal or streaming response and its uniform generator.
6. Complete the standard uniform NC^1 theorem for legal input lengths.
7. Add the known-position version with logarithmic support size.
8. Formalize the collision example and its two-collision initial-state family.
9. Add the new import closure, public entry point, and axiom-audit entries using the repository's existing verification workflow.

The first complete result is the fixed-k theorem with a concrete uniform response instance. Further parameterizations should preserve that statement and its proofs.

## 12. Verification and completion criteria

### 12.1 Required proof obligations

The implementation is complete only when it has proved:

- common-cone closure for both actual and reference dynamics;
- agreement with infinite-system prediction;
- reconstruction for arbitrary correction vectors;
- local-verifier soundness and completeness over the entire cone;
- acceptance equivalence and gated-value semantics on every input;
- support enumeration coverage and cardinality bounds;
- circuit depth and size bounds for the actual gate basis;
- complete logspace generation in the claimed polynomial-size regimes;
- the concrete background-response witness;
- the advertised properties and residual bound of each example.

These are proof obligations, not hypotheses that may be replaced by finite experiments.

### 12.2 Targeted executable checks

Executable checks should compare independent descriptions and address boundary risks:

| Check | Coverage |
| --- | --- |
| Direct iteration versus reconstruction from the actual residual | The collision fixture compares every response coordinate with direct iteration for reflector separations 1, 2, and 3. It checks every local equality and the apex at all three distances. [Collision fixture](../PredictionDepth/SparseCorrections/CollisionExamples.lean) |
| An omitted correction at an unguessed coordinate | At separation 1, the fixture zeros a required last-layer bit and checks that precisely that update fails. [Collision fixture](../PredictionDepth/SparseCorrections/CollisionExamples.lean) |
| Direct OR versus compiler output | The one-step fixture checks both lanes on every three-bit input. The all-horizon theorem compares the gate output with direct disjunction. [Finite fixture](../PredictionDepth/SparseCorrections/CompilerExamples.lean) · [All-horizon theorem](../PredictionDepth/SparseCorrections/PascalOR.lean) |
| Zero budget, zero horizon, empty schedule, and full small support | The OR and empty-horizon checks cover the empty cases. A two-address fixture checks absence from the enumeration at budget one and coverage at budget two. [Boundary fixtures](../PredictionDepth/SparseCorrections/CompilerExamples.lean) |
| Rejection versus an accepted zero | The exhaustive zero-budget OR fixture checks the two outputs separately. [OR fixture](../PredictionDepth/SparseCorrections/CompilerExamples.lean) |
| Serialized versus typed evaluation | The OR fixture compares both compiled output wires. The separation-one collision fixture compares every serialized response output with its typed counterpart. [OR fixture](../PredictionDepth/SparseCorrections/CompilerExamples.lean) · [Collision fixture](../PredictionDepth/SparseCorrections/CollisionExamples.lean) |

Run the repository's documented build and audit gates once the corresponding modules exist. Finite checks supplement, rather than establish, the general theorems.

## 13. Scope, limits, and further questions

### 13.1 What the result establishes

The certificate gives exact predictions and upper bounds on circuit resources under a sufficient structural condition. It recognizes that condition in the same resource regime. Optimal depth requires a separate argument.

No prior procedure for finding the actual sparse support is required in the fixed-k theorem. Enumeration and complete verification perform that task implicitly.

The bounds depend on the reference response, the number of candidates, and the size of the verification region. They apply even when successive correction events causally affect one another.

### 13.2 Limits of the statement

- Arbitrary nonlinear systems need not satisfy the residual budget.
- A sparse initial condition does not by itself bound later corrections.
- A small number of corrections per time step may still give a growing total count.
- Bounded changes at each cell do not imply a constant total residual count in the target cone.
- A shallow unforced final observation does not by itself provide the required full forced-response interface.
- Unknown logarithmically many positions do not yield polynomial size by the stated enumeration.
- A compact symbolic expression does not guarantee a shallow uniform circuit unless its operations and coefficient generation are costed.
- The construction uses exact Boolean states. Analog precision, stochastic noise, and distributional approximation require additional definitions.
- The bit-residual measure depends on the chosen reference and encoding. Invertible sitewise linear changes of a fixed-width state can change its weight by a constant factor, so an invariance claim must state the allowed encoding transformations.

#### Dense residuals with shallow prediction

Take the OR rule and Pascal reference from §10.1. The all-one initial window stays all one throughout the cone under OR. On each predecessor pair Pascal outputs $1\oplus1=0$, so every correction bit is one and the residual weight is $M=T^2$. For every input of the same system, however, the observation is the OR of the $T+1$ initial sites $0,\ldots,T$. A balanced OR tree has depth $\lceil\log_2(T+1)\rceil$. Each of those $T+1$ inputs is essential by comparison with the all-zero word, which gives the same lower bound for fan-in two. A fixed residual budget can thus reject inputs of a system whose unrestricted observation has exact logarithmic depth. [Residual weight and OR semantics](../PredictionDepth/SparseCorrections/PascalOR.lean) · [Balanced OR family](../PredictionDepth/Complexity/UniformOROptimal.lean)

#### Separate lower bound on the two-particle promise

Fix $T\ge1$. For each integer $z\in[-T,-1]$, put a $c$ particle at $z$ and a $b$ particle at $y=T+2z$, with all other bits zero. Both positions are in the initial window. The left-moving $b$ reaches $c$ at time $\tau=y-z=T+z\in[0,T-1]$. The collision $011\mapsto110$ sends an $a$ particle right from $z$, so at time $T$ its position is $z+(T-\tau)=0$. Removing either initial particle gives observation zero. These pairs witness $T$ distinct essential $c$ wires and $T$ distinct essential $b$ wires, with both words of every pair in the promise. The word with only an $a$ particle at $-T$ and the empty word witness one more essential wire.

A fan-in-two output of depth $d$ can depend on at most $2^d$ input wires even with sharing. Thus every circuit correct on the promised class has depth at least $\lceil\log_2(2T+1)\rceil$. With §10.4, this gives optimal depth order $\Theta(\log(T+1))$ for the two-particle promise. At $T=0$, the observation is an input projection. [Essential-input bound](../PredictionDepth/Circuit.lean)

### 13.3 Further research outside the completion criteria

The following questions concern stronger results or different models.

1. Find additional initial-state classes whose residual budget follows from geometry or dynamics.
2. Identify systems for which this certificate proves prediction bounds beyond an already available unrestricted predictor.
3. Improve depth as the unknown support grows. Chronological repair replaces the enumeration exponent with a factor of $k+1$ in size and depth. For a logarithmic, logspace-computable budget it gives the paper’s uniform NC² upper bound. Obtaining comparable size with logarithmic depth for such budgets remains open in this project.
4. Characterize when candidate positions can be generated shallowly from the input, with that generation included in the circuit.
5. Extend the response interface to other fixed finite fields, bounded-width state spaces, or selected affine backgrounds.
6. Determine when a smaller verified dependency region preserves soundness and materially reduces the resource bound.

These research questions are outside the three completion criteria in §1.1.

## 14. Related work and contribution boundaries

### 14.1 Algebraic fast prediction

Moore's work on non-autonomous additive cellular automata and quasidirect products gives fast parallel prediction, including a specific defect-dynamics example [1]. Its general time-dependent additive construction has O(log^2 T) depth with binary gates.

The present certificate assumes an explicitly shallow forced-response family and bounds the support of the discrepancy along the trajectory under consideration. The generic NC^1 consequence requires the stronger O(log T) response hypothesis. Defects defined as domain boundaries in a particular automaton are not automatically the residual bits defined here.

### 14.2 Short certificates and backdoors

Williams, Gomes, and Selman distinguish exploiting a small backdoor from locating one [2]. Their framework provides a useful conceptual comparison for the difference between enumerating assignments on K known positions and enumerating k unknown addresses.

Here each candidate must admit a shallow reconstruction and a shallow complete verifier. The elementary enumeration principle is not itself a novelty claim. No identification with a particular SAT backdoor definition is assumed.

### 14.3 Static nonlinear gates and trajectory residuals

Boyar, Find, and Peralta study low-depth circuits by separating and optimizing linear components around nonlinear operations [3].

Their static circuit measures differ from the present semantic parameter. A trajectory with k nonzero residual bits may arise from a rule whose unfolded circuit contains many nonlinear gates. The present argument does not assert that the all-input prediction function has multiplicative complexity k.

### 14.4 Freezing and bounded-change dynamics

Ollinger and Theyssier study freezing, bounded-change, and convergent automata and show that prediction complexity depends on the class and dimension [4]. Goles and coauthors obtain parallel algorithms for freezing networks under bounds on alphabet size, degree, and treewidth [5].

Those restrictions concern different features from the total discrepancy with a shallow linear background. The reference trajectory here may change at every time step. The sparse condition applies to its deviation from the actual trajectory.

### 14.5 Intended research contribution

The contribution sought is a compositional prediction certificate with:

- a precisely typed uniform forced-response interface;
- an input-dependent residual support condition;
- verification of the complete finite dependency region;
- separate accounting for unknown and supplied support;
- applicability recognition as well as conditional prediction;
- a machine-checked construction and informative fixed-rule examples.

Novelty should be assessed at the level of these exact hypotheses, resource bounds, uniformity guarantees, and applications. The references below establish relevant antecedents; they are not a claim of an exhaustive novelty search.

## 15. References

1. **Cristopher Moore.** [Predicting nonlinear cellular automata quickly by decomposing them into linear ones](https://doi.org/10.1016/S0167-2789(97)80003-6). *Physica D*, 111, 27–41, 1998. [Accessible preprint](https://arxiv.org/pdf/patt-sol/9701008). The preprint PDF also lists Timofey Pnin; the journal attribution follows the existing repository bibliography. Relevant material includes the non-autonomous additive construction and the defect-dynamics example.

2. **Ryan Williams, Carla P. Gomes, and Bart Selman.** [Backdoors To Typical Case Complexity](https://ijcai.org/proceedings/2003/167). *IJCAI*, 2003. [Author-hosted PDF](https://www.cs.cornell.edu/selman/papers/pdf/03.ijcai.backdoors.pdf).

3. **Joan Boyar, Magnus Gausdal Find, and René Peralta.** [Small Low-Depth Circuits for Cryptographic Applications](https://doi.org/10.1007/s12095-018-0296-3). *Cryptography and Communications*, 11, 109–127, 2019; published online in 2018. [NIST-hosted manuscript](https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=924490).

4. **Nicolas Ollinger and Guillaume Theyssier.** [Freezing, Bounded-Change and Convergent Cellular Automata](https://doi.org/10.46298/dmtcs.5734). *Discrete Mathematics & Theoretical Computer Science*, 24(1), 2022. [Preprint](https://arxiv.org/abs/1908.06751).

5. **Eric Goles, Pedro Montealegre, Martín Ríos-Wilson, and Guillaume Theyssier.** [On the parameterized complexity of freezing dynamics](https://doi.org/10.1016/j.aam.2024.102706). *Advances in Applied Mathematics*, 157, 102706, 2024. [Author-linked preprint](https://arxiv.org/pdf/2005.11758), under the earlier title *On the impact of treewidth in the computational complexity of freezing dynamics*. Version-specific theorem numbers should be checked before citing them.

## 16. Status checklist

The completed items below cover the specification’s enumeration compiler. The chronological repair extension and the general homogeneous response theorem are recorded separately below.

- [x] Finite common-cone semantics and input-length decoder. `Cone.finiteTrajectory_eq_restrict_iterate` and `legalLength_iff_exists`. [Semantics](../PredictionDepth/SparseCorrections/Semantics.lean) · [Length](../PredictionDepth/SparseCorrections/Length.lean)
- [x] Residual and bit-count convention. `actualResidual`, `support`, and `Sparse`. [Semantics](../PredictionDepth/SparseCorrections/Semantics.lean)
- [x] Rectangular propagators and reconstruction. `forcedTrajectory_eq_propagator_sum` and `reconstruct_actualResidual`. [Reconstruction](../PredictionDepth/SparseCorrections/Reconstruction.lean) · [Semantics](../PredictionDepth/SparseCorrections/Semantics.lean)
- [x] Uniform full forced-response witness. Both streaming and Pascal have checked circuit semantics, gate bounds, and complete code generators. [Streaming](../PredictionDepth/SparseCorrections/StreamingCircuit.lean) · [Pascal](../PredictionDepth/SparseCorrections/PascalResponse.lean)
- [x] Complete verifier and unique valid residual. `valid_iff_eq_actualResidual`. [Semantics](../PredictionDepth/SparseCorrections/Semantics.lean)
- [x] General two-output compiler. `compile_semantics` proves applicability and gated observation. [Compiler](../PredictionDepth/SparseCorrections/Compiler.lean)
- [x] Gate count, depth, and serialized description length. `compile_size`, `compile_depth`, and `compile_description_length_le` charge the actual representation, including framing and wire addresses. [Compiler](../PredictionDepth/SparseCorrections/Compiler.lean) · [Description](../PredictionDepth/SparseCorrections/Description.lean)
- [x] Fixed unknown budget and uniform NC¹. `sparseCandidates_card_le` and `Correct.unknown_mem_uniformNC_one`. [Candidates](../PredictionDepth/SparseCorrections/Candidates.lean) · [Certificate](../PredictionDepth/SparseCorrections/Certificate.lean)
- [x] Logarithmic schedule and uniform NC¹. `scheduledCandidates_card` and `Correct.scheduled_mem_uniformNC_one`. [Candidates](../PredictionDepth/SparseCorrections/Candidates.lean) · [Certificate](../PredictionDepth/SparseCorrections/Certificate.lean)
- [x] Concrete responses through the public interface. `Collision.layoutCorrect` and `Pascal.orLayoutCorrect`. [Collision certificate](../PredictionDepth/SparseCorrections/CollisionCertificate.lean) · [OR certificate](../PredictionDepth/SparseCorrections/PascalOR.lean)
- [x] Independent OR fixture and all-horizon comparison. `ORFixture.oneCorrection` and `Pascal.orPredictor_correct`. [Finite fixture](../PredictionDepth/SparseCorrections/CompilerExamples.lean) · [OR certificate](../PredictionDepth/SparseCorrections/PascalOR.lean)
- [x] Reversible collision and two-collision family. `step_reversible`, `exampleResidual_card`, and `example_accepts_and_predicts`. [Collision](../PredictionDepth/SparseCorrections/Collision.lean) · [Ablations and conservation](../PredictionDepth/SparseCorrections/CollisionProperties.lean) · [Prediction theorem](../PredictionDepth/SparseCorrections/CollisionCertificate.lean)
- [x] Public entry point, strict build, import coverage, and transitive axiom audit. [Lean entry point](../PredictionDepth/SparseCorrections.lean) · [Verification](verification.md)
- [x] Focused comparison with additive decomposition, backdoors, parallel prefixes, and automatic coefficient extraction. [Related work](literature.md#sparse-corrections-and-forced-response)

### Results beyond the original milestones

- Chronological repair has checked correctness, gate count, depth, and exact circuit serialization. The same construction gives logspace-uniform NC¹ for fixed budgets and NC² for logspace-computable logarithmic budgets. The reversible collision example requires exactly three bit rounds or two layer rounds. [Repair circuit](../PredictionDepth/SparseCorrections/RepairCircuit.lean) · [Serializer](../PredictionDepth/SparseCorrections/RepairCode.lean) · [Uniform bounds](../PredictionDepth/SparseCorrections/RepairUniform.lean) · [Collision repair](../PredictionDepth/SparseCorrections/RepairExamples.lean)
- The general multitrack section-operator construction is proved in the paper. The Lean witnesses above give full response for the two backgrounds used in the examples. [Paper](../paper/structural-certificates.pdf)

The open questions in Section 13.3 concern stronger bounds and different settings.
