# Phase IV: minimal primitives, typed inputs and irredundancy

## D0. What “minimal” means here

The candidate universe is the finite Phase IV identification registry and its externally instantiated realization targets. A reconstruction must recover the supplied target, with its declared marks, rather than replace it by a different canonical object. Mathematical foundations (real numbers, measure theory, matrices and formal power series) are fixed background infrastructure. A context is not thereby a free numerical parameter.

There are three different minimality questions.

1. **Intrinsic presentation:** how many independent intrinsic certificates are needed? One complete certificate; any other member of \(E_S\) is redundant. Even the triple \((H,I,p)\) stores the same information three times.
2. **Placed-family parameters:** how many independently variable scalar coordinates remain after imposing Sigma? Exactly \((\mu,a)\in(0,\infty)\times(0,1)\).
3. **External identification:** what arguments and identifying conditions are required to recover a selected realization, rather than the canonical family-valued recipe? Those depend on the requested target and are typed below.

These questions cannot be merged into a claim that all local theorem hypotheses are independent coordinates. Nor is there an encoding-invariant absolute minimum: an arbitrary code can package several data into one, and Sigma itself is explicitly definable in the fixed analytic foundations.

## D1. The relative irredundancy theorem

Fix the following target convention. The output includes the calibrated intrinsic shape, a placed Sigma on its marked \(r\) coordinate, and any requested **externally selected** realization packets. A packet contains its own type and the data naming an object in that type: for example a supplied base and bundle, or a supplied inner-product space and designated observable. A packet is not unpacked into ill-typed independent coordinates such as “a bundle but no base.” Canonical recipes such as spectral assembly are fixed, not arbitrary function parameters.

For testing deletion of the intrinsic certificate, relax the intrinsic candidate to a real analytic strictly convex \(J\) on \((0,\infty)\), with the usual affine anchors and \(\int e^{-1-J}=1\); do not keep a different complete Sigma clause after deleting the certificate. In particular, do not retain a linked external realization whose marked scalar restriction already identifies \(I\): that would be another complete certificate. For testing external packets, take the product of independent admissible expansions of the same scalar model: no unlisted bridge equation connects an external sort to the scalar component.

**Theorem D1; \(\Rightarrow\), with the identifying equivalences of IV-A–IV-E retained.** In this explicitly stated deletion universe the root decomposition
\[
 \text{one intrinsic shape certificate};\qquad \mu;\qquad a;\qquad
 \text{the requested external selection packets}
\]
is irredundant **block by block** whenever the packet's target distinguishes the alternatives in the witness table below. Removing a listed block admits two candidates agreeing on every remaining block and disagreeing on the named target. Conversely all canonical scalar shapes and all their complete presentations are reconstructed from that one certificate, and no independent amplitude, curvature scale, probability shape, formal-series coefficient or canonical-lift potential remains.

This is a relative theorem about the stated targets. A packet selecting an external object is omitted when the target is merely the canonical construction as a recipe. No theorem claims that the entire row of local side conditions is a mutually independent Cartesian product, or that one can remove an admissibility predicate while holding its determining data fixed.

### Explicit deletion witnesses

| Deleted block | Remaining data held fixed | Two admissible choices and the target they separate |
|---|---|---|
| Intrinsic shape certificate | Placement, coordinates, foundations and all external selections; no alternative complete intrinsic certificate | \(I\) and \(J_\epsilon=I+\epsilon g+\delta(\epsilon)h\) below; they preserve anchors, convexity and probability normalization but change the shape |
| \(\mu\) | \(S\), \(a=1/2\), all external packets | \(\mu=1\) and \(\mu=2\); closure locations and placed derivatives differ |
| \(a\) | \(S\), \(\mu=1\), all external packets | \(a=1/3\) and \(a=2/3\); analytic boundary and closure location differ |
| External coordinate/mark packet, when that coordinate is the target | Intrinsic formula, all unrelated packets | Relabel a coordinate by a nontrivial bijection, or conjugate projective generators; abstract structures remain isomorphic, but the marked functions differ. An abstract metric also admits \(t\mapsto1/t\), losing its orientation |
| Selected stationary-coordinate realization | Entire integer spectral package, distinguished constant vector, fixed J mixing law, all unrelated packets | \((L^2(p_2dt),A_2,1,M_t)\) and \((L^2(p_3dt),A_3,1,M_t)\). An intertwining unitary preserves \(1\) and the spectrum but not the multiplication-coordinate law |
| Selected angular realization | Ambient \(\mathbb R^4\), radial \(T\sim p\), other packets | \(Z=\sqrt{2T}U\) with uniform independent angle, and \(Z=\sqrt{2T}e_1\); same radius, different vector laws |
| Selected process category/identification packet | Time-one law \(p\), scalar component, other packets | The Gamma subordinator and \(X_r=rT\); the latter has dependent increments and different time marginals. The probability-convolution template identifies the former uniquely |
| Selected random-tree convention/independence packet | Borel total-size law, scalar component, other packets | Sample a Borel size and choose a path, or choose a star. They differ on sizes at least three. In the iid-GW template the Poisson tree is uniquely determined instead |
| Selected matrix-lift rule, if an arbitrary extension is the target | Rank-one \(I\), matrix spaces, scalar component | Canonical \(\Phi_n\) and \(\Phi_n+\epsilon\sum_{i<j}(\lambda_i-\lambda_j)^2\) for \(n\ge2\), with rank one unchanged; both are spectral but only the first satisfies the required block rule. A basis-dependent off-diagonal-square perturbation separately refutes invariance without a spectral rule |
| Topological argument packet | The complete scalar/formal component and all other external packets | Over fixed \(\mathbb{RP}^2\), trivial and nontrivial torsion complex lines have identical rational Chern character and different integral classes. Distinct bases further refute recovery of the base from the same scalar series |
| Integer-label packet for an arbitrary transport | Abstract free commutative multiplicative monoid, scalar component, other packets | Permute the prime generators, for example exchange 2 and 3, and transport all exponent vectors. Abstract multiplication is unchanged up to isomorphism but numerical labels and the embedded code change |
| Spatial selection packet | Every member of \(E_S\), the canonical operator/semigroup/matrix/auxiliary Gaussian branches, and other packets | \(\mathbb R^2\) versus \(\mathbb R^3\) separates dimension; on fixed \(\mathbb R^2\), \(r=\|x\|^2\) versus \(r=\|x\|^4\) separates the designated observable and orthogonal additivity. Even within the orthogonally additive class, \(r=\|x\|^2\) and \(r=2\|x\|^2\) leave a free external radius scale |

These witnesses compare marked objects, or distinct laws/integral classes where the target is an isomorphism class. A pure renaming of an unmarked structure is not offered as a non-isomorphism counterexample. The graph specifies which target retains a mark.

### Proof of the shape-certificate witness

Take
\[
 g(t)=(t-1)^4e^{-t},\qquad h(t)=(t-1)^4e^{-2t}.
\]
They are linearly independent real analytic functions, with their first three derivatives zero at one. The functional
\[
 M(\epsilon,\delta)=\int_0^\infty
 e^{-1-I(t)-\epsilon g(t)-\delta h(t)}dt
\]
is differentiable near \((0,0)\): the two perturbations and their needed derivatives are bounded, and the original density is integrable. Moreover
\(M(0,0)=1\) and \(\partial_\delta M(0,0)=-\int p(t)h(t)dt<0\).
The implicit-function theorem gives \(\delta(\epsilon)\) with \(M=1\). Since \(t^2g''\) and \(t^2h''\) are bounded, sufficiently small coefficients preserve \(J''>0\). The affine anchors and unit curvature at one remain fixed, so \(J\ge0\) with unique minimum one. Endpoint divergence is unchanged. Linear independence makes \(J_\epsilon\ne I\) for \(\epsilon\ne0\). Hence anchors, positivity, real analyticity and probability normalization alone are not another hidden complete shape certificate.

This witness tests removal of the identifying Sigma clause. It is not a counterexample to any complete clause of \(E_S\), and it does not make the already fixed intrinsic object into a variable parameter.

## D2. Local side conditions that must not be counted twice

| Apparent datum | Exact disposition |
|---|---|
| \(H,I,p\) separately | Two are algebraically redundant once one is known |
| Curvature anchors in recentering | The recentering equation supplies them; bare curvature still needs them |
| Second differentiability/convexity of a scale-invariant Bregman potential | Differentiability and the functional identity derive its full form; scale and affine calibration then fix it |
| Nonnegative support and mass for complete Gamma moments | Derived from the moments of a positive measure on \(\mathbb R\) |
| Mixing support/mass and existence in fixed J | Derived from the complete integer samples; the exponent-two recipe remains explicit |
| Candidate density smoothness for Gumbel/equilibrium | Derived from the exact CDF/survival target; no candidate density need be supplied |
| Bernstein values at zero or finitely many initial integers | Redundant once one entire integer tail is known in the Bernstein class |
| Laguerre endpoint condition | Both endpoints are limit point for the specified normalized expression; no boundary extension parameter |
| Semigroup weak continuity | Derived from nonnegative additive Laplace exponents |
| Independent angle and uniform angle under supplied isotropy | Both follow from isotropy in the fixed ambient category, almost everywhere in radius |
| SPD shape and regularity | Fixed by the rank-one seed, spectral invariance and scalar-block recursion; no arbitrary potential parameter |
| Original integer-code injectivity | A well-defined mathematical predicate of the chosen \(P\), not another coordinate that can change while \(P\) remains fixed; no effective decision algorithm for arbitrary real input is asserted |
| Zero drift with full time-one Gamma law | Derived; positive drift is free only in the weaker inverse problem supplying the Lévy measure alone |
| All self-decomposition scales or an independently supplied residual scale | One linked residual law at a contracting scale suffices; within the exact residual family its zero atom is \(c^2\), so the scale is recoverable. The original-law linkage remains essential |
| Global analytic continuation after global \(S\) is given | Redundant. It remains a class restriction in a germ-to-arbitrary-function inverse |
| \(D\) and residual cancellation | Not independent after radial operator and cancellation are imposed: they force \(D=1\) or 3. The extra \(D\ge2\) then selects 3 |
| A finite base and the complete universal characteristic tail | The base sees only a finite truncation; the full tail is reconstructed from \(S\), not inferred from that truncation |

The original code can be replaced, for canonical transport, by \(e_0(n)=H(n+1)\), \(n\ge1\). Since \(H'(t)<0\) on \(t>1\), it is injective without a placement restriction. This removes an admissibility problem from that **alternative construction**, not the need to label an arbitrary supplied code and not the collision counterexample for \(e(n)=\sigma(n)\).

## D3. Classification of every surviving input

Each item below receives exactly one primary class. Conditions attached to it are predicates, not additional numerical parameters.

| Class | Items and scope |
|---|---|
| A — placement | \(\mu>0,0<a<1\), equivalently \(\mu,\gamma\) in the placed family |
| B — coordinate / marking | The positive real coordinate and its affine origin/unit; the additive Gumbel coordinate and exact shifts; CGF argument and uncentering shift if an uncentered law is targeted; series variable and fixed \(y\); EGF/PGF convention and scale; labelled Möbius root/generators and full-domain action; multiplication-coordinate mark for an operator |
| C — category / realization | Specified local conservative differential expression and Hilbert realization; probability convolution/time, linked independent self-decomposition, or iid-GW framework; isotropic Euclidean-vector-law class; spectral/block matrix template; Bernstein representation; native topology/Thom/splitting context; inner-product-space and radial-operator categories. Matrix rank, offspring convention and dimension are context choices where a single instance is requested |
| D — designated object | Which ambient observable is called the spatial radius, including its free scale \(c\) when \(r=c\|x\|^2\); which process, tree, angular law, sample experiment or matrix extension is being identified; which externally selected bundle/class is the argument of a universal correction recipe. Such designations are constrained by the chosen C-class, not inferred from a scalar identity |
| E — arithmetic labels | Integer labels, factor labels and their code assignment for the transported arithmetic target. Injectivity is an admissibility predicate of that assignment |
| F — global continuation | Connected real-analytic candidate membership where a formal/local datum is used to identify a supplied global function; absent as a separate datum for a global intrinsic source |
| G — genuinely unknown | None in the finite audited graph after Z4. Lack of Lean coverage is not mathematical uncertainty |

Overlapping descriptions are resolved by typing: for example “iid-GW framework” is C, while the particular externally named random tree is D; its integer offspring indices are part of that framework, not the separate arithmetic transport E. A marked parameter such as \(y\) is B, not a new independent Sigma shape parameter.

## D4. Sharp local deletion tests

The complete proof record gives these additional necessity witnesses. They are inverse-problem conditions, not all simultaneous root variables.

- Remove an affine curvature anchor: add an affine function to \(H\). Remove scale calibration from recentering: multiply \(H\) by a constant.
- Remove both lower semicontinuity and convexity from the conjugate inverse: raise \(I\) at one point; the full conjugate stays unchanged.
- Remove one Gumbel max law: a small log-periodic modulation remains. Remove the CDF anchor: a free location remains.
- Retain only the deficit law: shift both inverse branches by a common small level bump. Retain only the level involution: reparameterize the levels while solving the single normalization equation.
- Remove the uncentering mark: \(N\) and \(N+k\) have the same centered CGF. This does not affect reconstruction of \(I\) from the centered function.
- Remove one polynomial probe in the local operator class: a coefficient function remains free. Remove the local class: a unitary rotation of higher modes preserves the probes and changes the operator.
- Remove the zero-atom exclusion in size-bias or equilibrium inversion: \(r\delta_0+(1-r)\mu\) has the same transformed law.
- Supply only the Gamma Lévy measure: add arbitrary drift \(d\ge0\). Supply only finitely many spectral invariants: vary more eigenvalues than independent scalar constraints.
- Remove the complete coefficient tail: triangular formal recursion leaves a free coefficient or tail. For \(\chi_{-1}\), the exact series is \(1+u\) and discards the original unit series.
- Remove real analytic continuation: add a sufficiently small smooth zero-integral perturbation away from the germ and closure point.
- Remove dimension at least two from orthogonal additivity: on a line orthogonality imposes no such radial rigidity. Remove nonnegativity: linear odd terms survive. Remove residual cancellation: any dimension remains admissible in the radial formula.
- Replace full functions by all exact derivative-zero sets: the normalized analytic family \(f_k\) in Z4 preserves every set and changes the density.

These proofs establish the stated blockwise irredundancy and the local minimality actually used by the closure theorem. They do not claim a shortest encoding across arbitrary mathematical languages or an inverse map from formal reconstruction to physical reality.
