# Phase IV independent adversarial audit: global closure and minimality

## Scope and verdict

This audit read `sigma-phase-iv-reconstruction-theorem.md` and `sigma-phase-iv-minimal-primitives.md` as proposed statements, before consulting the local core, probability, operator and realization audits for their precise interfaces. It did not infer correctness from an earlier intended architecture or from agreement among reviewers. No outward search or root-report editing was performed.

**Verdict: the global reconstruction and relative irredundancy theorems pass with their retained signatures and explicit deletion universe.** One literal registry defect was found: F1 initially required an invertible formal series without specifying its constant coefficient. That formulation was false. The coordinator has now inserted **`Q(0)=1`**, resolving the defect. The claim that injectivity was a “decidable” predicate of arbitrary real placement parameters has also been replaced by the justified claim that it is a well-defined predicate.

The initial verdict concerned the mathematical statements and their composition, because the graph had not yet been generated. The subsequent concrete graph audit in section 7 now verifies the finite SCC and its quotient independently. The local audit files supply the complete local proofs; this global review does not claim a second independent proof of every local theorem or additional Lean coverage.

## 1. A genuine counterexample to the original F1 wording

In the standard terminology, a unit of `Q[[u]]` has any nonzero constant coefficient. Suppose only

`[u^n] Q(u)^(n+1) = 1` for every integer `n >= 1`.

For each nonzero rational `c`, start with `q_0=c`. At degree `n`, the equation has the form

`(n+1)c^n q_n + P_n(q_0,...,q_(n-1)) = 1`.

The displayed coefficient is nonzero, so recursive division constructs a unique entire formal series for every such `c`. In particular,

`q_1=1/(2c)`,

`q_2=1/(3c^2)-1/(4c^3)`.

Thus `c=2` gives a unit beginning `2+u/4+5u^2/96+...` satisfying every stated tower condition, but it is not the Todd series. This is an all-order formal counterexample by induction, not a finite coefficient diagnostic.

**Exact repair, now present:** require `Q(0)=1`, or include the degree-zero tower equation. With `q_0=1`, the same recursion is triangular with leading coefficient `n+1`; it proves uniqueness. The local residue proof supplies existence for the Todd series. This repair is also consistent with the actual Lean series theorem, which explicitly assumes constant coefficient one. Calibration cannot be omitted from a compressed registry merely because a linked proof retained it.

## 2. The closure theorem is valid only as a typed identification theorem

For precision, fix a signature `m` recording the coordinate, domain, admissible category and normalization of a presentation. Write `X_A[m]` for the candidates satisfying that presentation's complete identifying clause, and `X_S[m]` for the corresponding calibrated intrinsic object. The correct interface is

`enc_A : X_S[m] -> X_A[m]`,

`dec_A : X_A[m] -> X_S[m]`,

with both round trips equal to the identity, or to the identity on the declared isomorphism classes. Composition then proves Theorem B directly. It does not require additional independent shape parameters.

This typing resolves the apparent changes of category among measures, marked analytic functions and formal series: the maps recover the respective presentation in its own candidate category. In a measure category equality is equality of measures; a continuous density representative is selected only after the theorem has identified the measure. A formal node initially reconstructs a formal germ. Identification of a supplied global candidate retains the connected real-analytic continuation class. A canonical analytic representative is a construction when no arbitrary global candidate has been supplied.

Marks such as `y` in the characteristic series, EGF versus PGF conventions, the Borel scale and the rational-tree coordinate remain fixed in the signature. Their variation is not an additional intrinsic Sigma shape coordinate. If one instead forgets those marks and allows them to vary on the same node, the displayed round-trip theorem has changed and requires a separate proof.

The bare spectrum correctly remains outside the intrinsic identification component. Let

`p_alpha(t)=t^(alpha-1)e^(-t)/Gamma(alpha)` and

`A_alpha=-[t d^2/dt^2+(alpha-t)d/dt]`

in its Laguerre realization. The cases `alpha=2` and `alpha=3` have the same simple integer spectrum. Mapping their normalized Laguerre bases mode by mode gives an intertwining unitary that also fixes the constant vector. Both satisfy the fixed J identity with the same Gamma(2) mixing measure. Nevertheless, their stationary multiplication-coordinate distributions have means two and three, respectively. No unitary preserving the constant vector and intertwining the multiplication coordinates can identify these marked packages.

Consequently the fixed J inverse identifies its **unknown mixing measure**, exactly as the O5 node now says. It does not recover the stationary law of an arbitrary source realization. The exclusion of construction-only edges from the identification SCC is necessary, and it repairs the earlier forget-and-select cycle.

For canonical templates, the defensible equivalence is fibrewise: fix `C`, or retain `C` in the output package, and identify objects satisfying the template's exact conditions. It is not an inverse from an evaluated output to a forgotten arbitrary context. In particular, evaluation of a Thom correction on one finite base does not recover the universal series tail or the original integral bundle class. The current universal-line clause and finite-base exclusion preserve this distinction.

## 3. Placement and its two independent parameters pass

Set `t=mu r+a`. The placed formula simplifies to

`sigma_P(r)=log(mu/(1+a))+log(mu r+a)-mu r`.

It follows directly that

`sigma_P'=mu/t-mu`, `sigma_P''=-mu^2/t^2`, and `q=sqrt(-sigma_P'')=mu/t`.

Therefore

`q-sigma_P'=mu`,

`1-rq=a/t>0`,

`q/(1-rq)=mu/a=gamma`.

These prove the stated inverse at every point of the marked analytic domain. They also show why the marked `r` coordinate is part of the inverse problem. Forgetting its affine scale changes the problem.

The normalized density is

`exp(sigma_P(r))=mu e^a/(1+a) * t e^(-t)`.

Changing variables gives mass one for `r>=0`, since `integral_a^infinity t e^(-t)dt=(1+a)e^(-a)`. On the whole domain `r>-a/mu`, its mass is `e^a/(1+a)`. Both normalization statements in Theorem C are correct.

The deletion witnesses for `mu` and `a` pass: holding the other coordinate and all intrinsic data fixed produces different analytic boundaries and derivatives. Thus neither coordinate is determined by the intrinsic component. These are two independently varying scalar coordinates in this declared family, not an assertion about the shortest encoding in an arbitrary language. Injectivity of `n -> sigma_P(n)` is fixed once `P` is fixed, so it cannot be an independently varying root block. No effective decision procedure for completely arbitrary real inputs follows from this observation.

## 4. The relative shape-certificate witness passes

The intrinsic object is explicitly definable in the fixed foundations. Consequently the phrase “one intrinsic certificate” is a statement about a sufficient and irredundant identifying clause in a declared deletion problem. It is not a lower bound of one free numerical datum or a denial that a fixed formula can be written without receiving an external function input.

The proposed relaxed shape class is large enough for its witness. For

`g=(t-1)^4 e^(-t)` and `h=(t-1)^4 e^(-2t)`,

both perturbations are analytic, bounded and linearly independent, and their values and first three derivatives vanish at one. Define

`M(epsilon,delta)=integral exp(-1-I-epsilon g-delta h)dt`.

Boundedness permits differentiation under the integral near zero. Its derivative in `delta` is strictly negative at zero. The implicit-function theorem therefore produces small `delta(epsilon)` preserving mass one. Boundedness of `t^2g''` and `t^2h''` makes

`J_epsilon''=t^(-2)+epsilon g''+delta(epsilon)h''`

strictly positive for sufficiently small coefficients. The anchors, unit curvature, minimum location and endpoint divergence persist. Linear independence excludes equality with `I` for nonzero `epsilon`. Thus the example preserves more than the minimum stated relaxed hypotheses while changing the shape.

The exclusion of every alternative complete intrinsic certificate is essential. For example, if the remaining input includes a linked normalized Gamma stationary law whose marked restriction is required to equal `exp(-1-J)dt`, then this remaining packet already forces `J=I`. Deleting the separately named certificate would be redundant. The draft explicitly excludes that situation in its certificate-deletion test. This qualification must remain attached to D1; it cannot be replaced by an unrestricted assertion about holding every possible linked external observation fixed.

## 5. External irredundancy passes in the explicit product universe

The independent-expansion convention is doing real mathematical work. Its simple abstract version is this: let the external selection sets be `Z_j`, and let the target include `tau_j(z_j)`. If `tau_j` takes different values on two admissible elements of `Z_j`, and no retained bridge ties that coordinate to another block, then changing only `z_j` proves that deletion of that block prevents target identification. This is exactly a blockwise product theorem. It is not a claim that all local admissibility predicates are free coordinates.

The supplied witness table realizes this argument:

- The two Gamma stationary-coordinate laws retain all the spectral and J data but have different marked coordinate laws.
- Uniform and fixed directions retain the same Gamma radius and ambient four-dimensional space but give different vector laws. The fixed-direction law is deliberately outside the isotropic template; it tests arbitrary angular designation, not the isotropic uniqueness theorem.
- The Gamma subordinator and `X_r=rT` retain the same time-one law. Their time-`r` Laplace transforms are `(1+s)^(-2r)` and `(1+rs)^(-2)`, respectively, so the process distinction is explicit. Only the former belongs to the specified convolution/increment template.
- Paths and stars sampled with the same Borel total size differ as rooted trees at size three. The iid-GW clause is what excludes this arbitrary-shape freedom.
- A spectral matrix perturbation vanishing at rank one preserves the scalar seed but violates scalar-block recursion. Hence it tests the extension rule, rather than contradicting the exact matrix template.
- A nontrivial torsion complex line on `RP^2` has the same rational Chern character as the trivial line but a different integral class. The universal scalar series supplies neither a selected base nor the missing integral argument.
- Prime permutations preserve the abstract multiplicative monoid while changing its numerical labels. This is a marked-target distinction, not a claim that the resulting unmarked monoids are nonisomorphic.
- Independent spatial sorts of dimensions two and three, and squared versus fourth-power norm observables on a fixed space, retain the complete scalar model while changing the designated target. The auxiliary Gaussian realization does not identify this independently selected spatial sort.

Coordinates, categories and designations are therefore correctly distinguished. A category restricts admissibility; a coordinate mark determines how a supplied object is represented; a designation chooses the particular requested object. A packet may contain dependent data of several kinds, and the theorem appropriately treats it as one typed block rather than separating an object from the type required to name it.

The conjunction of orthogonal additivity, nonnegativity and dimension at least two identifies `c||x||^2` in the supplied inner-product space. The radial cancellation equation then restricts the already supplied dimension to one or three, and `D>=2` selects three. Neither fact adds a scalar-to-spatial identification arrow.

## 6. The zero-set boundary survives the global audit

For `k>1`, the stated density

`f_k(t)=(k-1)k^k t/(t+k)^(k+1)`

has mass one and is positive and real analytic on the positive ray. Differentiating `(t-n)/(t+k)^(k+n+1)` yields

`-(k+n)(t-n-1)/(t+k)^(k+n+2)`.

This independently checks the all-order induction. Every derivative zero set is exactly `{n}`, with the same signs and simple zeros as `p`, while the tail is algebraic. Thus Z4 is a counterexample to equality of the entire sequence of zero sets, not merely to finitely many observed zeros. It does not refute any complete identifying clause retained in `E_S`.

## Final audit disposition

The normalized F1 statement, marked intrinsic equivalences, placed reconstruction, fibrewise canonical identification, and relative product-universe minimality survive this adversarial review. The discarded spectral-to-stationary converse remains false, and the fixed J recipe does not repair it. The proof of intrinsic-certificate necessity is relative to deletion of all equivalent identifying clauses; the proof of external necessity is relative to the declared independent expansions and marked targets. The later concrete graph audit below completes the finite-graph verification.

## 7. Follow-up: the concrete generated graph

The follow-up read both `work/build_phase_iv_graph.py` and the generated JSON. It inspected every intrinsic clause, every positive edge and its required inputs, and the negative edges against their countermodel categories. It did not accept the generator's `intrinsic_member` flags or asserted check results as a verification of maximality.

The independent [checker](global-graph-checks.py), run as `python3 outputs/phase-iv-audit/global-graph-checks.py`, records its output and the exact graph SHA-256 in [global-graph-checks.json](global-graph-checks.json). It independently builds the directed identification graph, including one-way identification arrows and the spectral equivalences, computes SCCs, reconstructs the quotient and checks context availability in both directions of each identification. Construction, transport, forgetful, negative and unprovided-context edges do not manufacture an identifying inverse.

**Concrete structural verdict: PASS.** After adding the explicit P9 identifying dependency described below, the checked graph has 105 nodes and 118 edges. Its nontrivial unconditional identification SCCs have:

- 46 intrinsic nodes, exactly the declared `E_S`;
- 5 spectral nodes: `SPEC`, `HEAT`, `ZETA`, `ZETA_INT`, `FULL_DET`;
- 2 operator nodes: `LAGUERRE`, `KERNEL`, in their retained operator context.

The quotient is exactly the independent structural projection. Every surviving quotient edge retains its original source and target and their complete datum signatures; in particular, collapsing intrinsic presentations does not erase whether an outgoing theorem used the density, potential or formal germ. All references and proof-record paths resolve. There are no conditional edges with an empty `required_nodes` list, and no missing context in either direction of a positive identification edge.

### Concrete defects found and their repairs

1. **The initial JOINT node did not prescribe the observed values.** Every normalized strict-branch potential has its own deficit law and level involution, including the non-Sigma `J_epsilon` from the shape-deletion witness. Merely possessing such a linked pair therefore does not identify Sigma. The node now requires that the candidate's two observations equal the canonical law of `I(T)` under `p` and the canonical I-level involution, and that both observations concern the same `J`. The `INVOL` datum now specifies that canonical involution. This was a substantive identifying-clause repair.
2. **Context-indexed aliases lost context in their metadata.** `KERNEL` and `LOW2` now retain `OP_CONTEXT`; `MATRIX_GEOM` retains `SPD_CONTEXT`. The full marked kernel/operator equivalence therefore stays in the same operator fibre. The scalar spectral trace remains a deliberate forgetful output.
3. **Three conditional edges had only prose inputs.** An individual tilt now requires `TILT_MARK`; the Hessian/Bregman potential inverse requires `MATRIX_ANCHORS`; the Wishart/likelihood construction requires `SAMPLING_CONTEXT`, which includes the supplied experiment. These are no longer hyperedges that a node-only consumer could incorrectly fire without their variable inputs.
4. **Intrinsic consequences included unspecified placed variants.** The derivative hierarchy is now on intrinsic `t>0`; zero sets are the intrinsic `{n}`; the finite jet is at intrinsic `t=1`; integer samples are those of `H(n)`. Placed variants explicitly require placement. Thus an unconditional arrow from `S` no longer appears to select an arbitrary external point or placement.
5. **The smooth-extension counteredge originally started at a germ node retaining analytic admissibility.** The graph now first forgets that class to `GERM_ONLY`, then states the failed inverse for arbitrary smooth extensions. This preserves the valid analytic identity theorem and gives the countermodel its actual larger candidate class.
6. **Derived external conclusions needed their argument identities retained.** Gysin data retain the selected topology and map; the radius conclusion retains its spatial context; the residual and dimensional conclusions retain the same radial-operator context. In particular, the cancellation predicate and dimension lower bound concern the same dimension symbol and supplied operator throughout their join.
7. **A fibre's related outputs were briefly listed as identifying aliases.** Wishart statistics and evaluated Gysin corrections have only forward construction edges. They are now explicitly classified as related consequences whose reconstruction status is their displayed edge status, not as additional identifying members of the intrinsic fibre. A finite-base Gysin evaluation still cannot recover a universal scalar tail.

### All edge families after repair

The 45 direct intrinsic equivalences now have complete normalized clauses, including the corrected F1 constant coefficient and prescribed JOINT observations. Each of the seven main canonical templates uses the source together with its context. Its reverse retains that context. The duplicated context-to-template construction arrows have `S` as a simultaneous input; they do not assert that an isolated context identifies the scalar shape.

The local operator probes identify the differential expression only in the supplied conservative second-order class, with the normalized Pearson realization retained. The full marked kernels retain that same realization. The spectral equivalences instead concern the nonnegative self-adjoint unitary class and the actual finite trace or marked determinant category. The fixed J edge remains a construction into the mixing-law output. No composition of these edges is incorrectly promoted into an inverse on an arbitrary stationary coordinate realization.

The Lévy inverse requires both the convolution category and the zero-drift condition in the weaker inverse problem where only the Lévy measure was supplied. The complete semigroup's time-one law already fixes drift zero, as the theorem text states. The marked tilt inverse, the joined deficit/involution inverse, and the calibrated matrix-geometry inverse retain their respective mark, linked observation and affine anchors. Sampling, topological and arithmetic arrows retain the selected experiment, map/bundle or numerical code and labels. The spatial arrows start at a designated external space or radial operator, not at the scalar component.

The counterexample arrows are interpreted in their declared larger candidate classes: arbitrary stationary-coordinate realizations for spectral forgetting, arbitrary normalized linked potentials for partial deficit observations, arbitrary smooth/global functions for finite or discrete data, and independent external expansions for spatial/topological/arithmetic selection. A counterexample in a larger class does not deny identification after the canonical template's conditions have been retained.

The independently computed conditional fibres add the following nodes to `E_S`:

| Retained additional inputs | Additional identification members |
|---|---|
| `PLACEMENT` | `SIGMA` |
| `OP_CONTEXT` | `LAGUERRE`, `KERNEL`, `LOW2` |
| `CONV_CONTEXT` | `SEMIGROUP` |
| `CONV_CONTEXT`, `NO_DRIFT` | `SEMIGROUP`, `LEVY` |
| `SPD_CONTEXT` | `SPD` |
| `SPD_CONTEXT`, `MATRIX_ANCHORS` | `SPD`, `MATRIX_GEOM` |
| `GAUSS_CONTEXT` | `GAUSSIAN` |
| `GW_CONTEXT` | `GW` |
| `TOP_CONTEXT` | `THOM` |
| `TILT_MARK` | `TILT` |
| the canonical `INVOL`, with the joint linkage retained | `DEFICIT` |
| `SELFDECOMP_LINK`, linking a candidate to one residual entry | `SELFDECOMP` |

These computations preserve simultaneous inputs. They do not treat a required context as automatically supplied merely because some unrelated canonical construction could produce an object of a similar name.

### Exact meaning of graph maximality

The verified maximality is maximality in the finite **retained identification-edge relation**. It does not say that every mathematically possible inverse omitted from the graph is false. A forward-only canonical output can contain substantial identifying information, and absence of its inverse edge is not itself a countermodel.

For example, suppose a probability law has Laplace transform `L`, a marked `0<c<1`, and the exact linked self-decomposition equation

`L(lambda)=L(c lambda) ((1+c lambda)/(1+lambda))^2`.

Iteration yields

`L(lambda)=L(c^n lambda) ((1+c^n lambda)/(1+lambda))^2`.

Since every probability Laplace transform on the nonnegative ray is continuous at zero with value one, the limit forces `L(lambda)=(1+lambda)^(-2)`. Thus an exact linked residual already determines the Gamma law. This is stronger information than generic self-decomposability. A graph node representing only a canonical residual output, without the candidate-law linkage, must be read accordingly. In either case, limiting graph maximality to retained proof edges is essential; it does not require adding a new phase or asserting an unknown inverse.

### Independent checks of P7 and O7

The complete entropy clause in the proof-record preamble passes independently. For every admissible density `f`, the two fixed constraints give

`integral f log p = E_f(log t-t) = -1-gamma_E`.

Integrating `z log z-z+1>=0` against `pdt`, with `z=f/p`, gives nonnegative relative entropy. Therefore differential entropy is at most `1+gamma_E`. The density `p` attains it, and the strict scalar equality condition forces `f=p` almost everywhere. The stipulated density/entropy convention and finite absolute constraint integrals make this calculation well typed. Neither unconstrained entropy maximization nor the two moments alone is being called identifying.

The complete marked Laguerre-orthogonality clause also passes independently. Mass fixes moment zero. Since `L_n^(1)` has nonzero leading coefficient `(-1)^n/n!`, its zero integral determines moment `n` from all smaller moments. The Gamma measure satisfies these equations: Rodrigues' formula reduces each integral for `n>=1` to an integral of an nth derivative of `e^(-t)t^(n+1)`, whose boundary term vanishes at both ends. Induction therefore gives all moments `(n+1)!`. The positive-measure moment uniqueness theorem then identifies the measure, including its support. Positivity, mass, all-polynomial integrability and the actual polynomial coefficients are retained throughout.

**Completed graph disposition:** the concrete identifying SCC, conditional inputs, context preservation and quotient now pass. The stated mathematical boundary remains the boundary of this audited identification architecture, with graph maximality confined to its retained edges and candidate signatures.

## 8. P9: exact linked self-decomposition identifies the candidate law

This theorem was identified during the concrete graph audit, by examining whether a construction-only residual output could support an additional identifying inverse. The proof below is independent of the existing probability audit's forward construction. Its status is **conditional equivalence**: the residual law must be linked to the candidate whose reconstruction is claimed.

**Exact theorem.** Fix `0<c<1`. Let `rho_c` be the probability law on the nonnegative ray with Laplace transform

`R_c(lambda)=((1+c lambda)/(1+lambda))^2`, `lambda>=0`.

Let `mu` be an arbitrary Borel probability on the entire real line. Then

`mu = (D_c mu) * rho_c`

if and only if `mu=Gamma(2,1)`. Here `D_c` denotes multiplication of the random variable by `c`, and convolution means that the scaled copy and residual are independent. Equivalently, `X` has the same law as `cX'+Y_c`, where `X'` has the same law as `X`, `Y_c` has law `rho_c`, and `X'` and `Y_c` are independent. No support, moment, density, smoothness or zero-atom assumption is needed for the candidate. The real-line strengthening was suggested by the coordinator after the initial half-line proof and was independently checked here through characteristic functions.

**Existence of the residual.** A variable with law `c delta_0+(1-c)Exp(1)` has Laplace transform

`c+(1-c)/(1+lambda)=(1+c lambda)/(1+lambda)`.

The sum of two independent such variables therefore has the displayed `R_c`. It has atom `c^2` at zero. This is also an elementary explicit realization of the residual, requiring no Lévy representation theorem.

**Uniqueness on the real line.** The residual construction gives its characteristic function directly:

`phi_rho(xi)=(c+(1-c)/(1-i xi))^2=((1-i c xi)/(1-i xi))^2`.

Let `phi` be the characteristic function of `mu`. Independence and the actual convolution linkage give

`phi(xi)=phi(c xi) ((1-i c xi)/(1-i xi))^2`.

Induction, with telescopic cancellation, yields

`phi(xi)=phi(c^n xi) ((1-i c^n xi)/(1-i xi))^2`.

The denominators are nonzero for real `xi`. Every probability characteristic function is continuous at zero by bounded convergence, so `phi(c^n xi)->phi(0)=1`. Taking the limit proves `phi(xi)=(1-i xi)^(-2)`, the characteristic function of Gamma(2,1). Characteristic-function uniqueness identifies `mu` on the entire real line. Its positive support, absence of a zero atom, density and mean two are all conclusions. This argument does not assume that the candidate has any finite exponential moment or that its Laplace transform exists.

**Converse.** For `phi(xi)=(1-i xi)^(-2)`, direct multiplication gives `phi(c xi)phi_rho(xi)=phi(xi)`. Independent copies realize the convolution, and characteristic-function uniqueness gives the asserted equality of laws. This proves both directions on the real probability class.

**The linkage is essential for the designated candidate.** Keep `c`, the entire residual law `rho_c`, and all canonical scalar constructions fixed. Without the equation linking `rho_c` to the candidate, designate either `Gamma(2,1)` or `Gamma(3,1)` as the law of `X`; construct an independent copy and the same independent residual in both models. All retained residual observations agree, but the candidate laws differ. The Gamma(2) selection is a valid construction from the residual formula, but it is not an identification of an arbitrary independently named `X`. The same countermodel works even if the complete family of residual laws is supplied but none is linked to that candidate.

**The endpoint `c=1` is nonidentifying.** Here `R_1=1`, so `rho_1=delta_0`. Every probability satisfies `mu=(D_1 mu)*delta_0`. In particular both Gamma shapes two and three satisfy the complete linked equation, with the same residual and the same value of `c`. The contraction condition excluding this endpoint is therefore essential.

The lower bound `c>0` is not sharp for uniqueness: `c=0` gives `mu=rho_0=Gamma(2,1)` immediately. The theorem extends to `0<=c<1`; the conventional open interval expresses a nontrivial self-decomposition. For `c>1` the displayed function cannot be a probability Laplace transform, since its limit at infinity is `c^2>1`. Thus one must not advertise both strict inequalities as independently necessary identifying conditions.

Finally, in this specified residual family an individual complete residual law determines its scale from `rho_c({0})=c^2`. The scale mark is useful for the presentation and for constructing a selected residual from `S`, but it is not an extra independent inverse datum once that full residual law and its family membership are supplied. A whole `c`-indexed residual family can be constructed unconditionally from `S`; constructing a selected individual member additionally needs the choice of `c`.

**Final synchronization verified.** The generated graph now uses the entire indexed residual family for the unconditional forward construction and one linked entry for the real-line characteristic-function inverse. The final independent structural run passes on 105 nodes, 118 edges and 46 intrinsic members, with no unresolved proof paths or context errors. Its graph SHA-256 is `ed2f859918668863f3d6cf16744acb351aedcd80c840c44581a4ab34136e89d0`. No graph-audit correction remains pending for this version.
