# Phase IV independent audit of matrix, spatial and arithmetic realizations

The statement-only proofs were saved in [realizations-blind.md](realizations-blind.md) before opening the corresponding Phase III arguments. The earlier probability assignment had exposed probability sections and incidental search snippets; the blind file explicitly records that limited prior exposure. This comparison then read Phase III II.5, III.6, III.8–III.10 and IV.7–IV.11, together with the older sixteen-branch audit, dependency/audit ledgers and relevant manuscript sections. The Euler-product converse was encountered during comparison and checked separately below; it is not claimed as part of the original blind exercise. No global report was edited.

Symbols: **✓ ⇔** exact identifying equivalence in the stated category; **✓ ⇒** valid forward construction; **△ +H** essential retained datum or a statement requiring repair; **✗** refuted unqualified converse. Historical labels refer to these workspace audits, not novelty in the mathematical literature.

## Findings and historical classification

| Node | Verdict | Old / strengthened / new within this workspace |
|---|---|---|
| SPD lift from rank-one I, orthogonal invariance and scalar-block recursion | **✓ ⇔**, no regularity needed | **Old**: already proved in M1 and the sixteen-branch audit |
| Canonical spectral/Gaussian construction versus identification of an arbitrary lift | **✓ ⇒** construction; **△ +H** identification | **Clarified in Phase III**; the counterexamples were already old |
| Hessian, Bregman divergence, congruence, precision reversal, conjugate, geodesic and distance | **✓ ⇔** with affine calibration/category | **Old formulas** in the manuscript/M1–M3; Phase III develops them correctly |
| Matrix symmetrization not determined by distance alone | **✓** counterexample | **Old boundary**, now given a particularly explicit equal-distance pair |
| Determinant inequalities and Wishart likelihood/transform | **✓ ⇒** with supplied Gaussian iid model and sample count | **New immediate refinements in Phase III** |
| Nonnegative orthogonal additivity implies c times squared norm without continuity | **✓ ⇔**, dimension at least two | **Old strengthened theorem** already in the sixteen-branch audit; not a new Phase III collapse |
| Orthogonal star composition implies `exp(c||x||²)−1` | **✓ ⇔** under the nonnegative logarithmic-observable condition | **Old** |
| Profile-independent radial residual and D=1 or 3 | **✓ ⇔** in the selected radial-operator category | **Old**; Phase III broadens the explicit network countermodel presentation |
| Whole scalar network identifies an arbitrary spatial observable or dimension | **✗** | **Old obstruction**, tested against all proposed bridges in Phase III |
| Labelled Calkin–Wilf parent algorithm and calibrated generator reconstruction | **✓ ⇔** with full-domain extension condition | **Old**, with an explicit domain repair in Phase III |
| Nonnegative unimodular matrix words, Stern–Brocot reversal and Euclidean/CF decoding | **✓ ⇔** with root/order/numerical marks | **New immediate refinements in Phase III** |
| Bare tree determines real generator maps or I below t=1 | **✗** | **Old marking boundary**, sharpened to a full-domain extension issue |
| Original integer-code collision criterion | **✓ ⇔** exact parameter criterion | **Strengthened in Phase III** beyond earlier sufficient injection tests |
| Prime/divisor/valuation/gcd/lcm/Möbius/Dirichlet transport | **✓ ⇔** inside the supplied unit-adjoined monoid | Prime transport **old**; full arithmetic inventory **new refinement in Phase III** |
| Euler product recovers its numerical generator multiset | **✓ ⇔** in the convergent positive Euler-factor category | **New conditional converse in Phase III** |
| Original code versus alternative shifted intrinsic code | **✓** distinction; replacement does not fix original collisions | **New explicit construction in Phase III** |
| Every original-code collision destroys multiplication | **✓**; proof below | **New strengthening in this audit** of the previously exhibited collision |

The major realization claims pass. Two matrix sentences require small repairs, and the continued-fraction terminal convention should explicitly exempt one-term integer expansions. No unconditional matrix/spatial/arithmetic identification emerges by combining the canonical auxiliary constructions.

## 1. SPD uniqueness and the two indispensable rules

**Exact statement.** A family `Φ_n:SPD_n→R` with `Φ_1(t)=I(t)`, orthogonal conjugation invariance and `Φ_(m+n)(X⊕Y)=Φ_m(X)+Φ_n(Y)` is uniquely

`Φ_n(X)=Σ_i I(λ_i(X))=tr X−log det X−n`.

Orthogonal diagonalization followed by one-dimensional block recursion is the entire proof. No continuity, convexity, measurability or differentiability assumption is used. Full arbitrary-block additivity can be reduced to scalar-block recursion. This result, including the weaker recursion and absence of regularity, was already in the older audit; it should not be counted as newly proved in Phase III.

The two counterexamples in IV.7 are valid and retain nonnegativity. The function `F_n(X)=Σ_i I(X_ii)` has the rank-one seed and block additivity but changes when `diag(2,1)` is rotated by π/4. Indeed its values differ by

`I(2)−2I(3/2)=log(9/8)≠0`.

The spectral perturbation `G_n=Φ_n+εΣ_(i<j)(log λ_i−log λ_j)^2`, ε>0, has the seed and invariance but violates block additivity on distinct scalar blocks. Hence the scalar seed alone, or either one rule, cannot identify a designated matrix lift. Constructing the canonical Φ by spectral calculus or Gaussian KL proves that this particular object satisfies the rules, not that an independently supplied F does.

## 2. Matrix differential geometry: verification and two repairs

All matrices in this section are real symmetric positive definite; tangents and dual parameters are symmetric, with the trace pairing. The derivatives and divergence are

`∇Φ(X)=Id−X^(−1)`,

`g_X(U,V)=tr(X^(−1)UX^(−1)V)`,

`D(X,Y)=tr(Y^(−1)X)−log det(Y^(−1)X)−n`.

Their derivation from the inverse derivative `d(X^(−1))[U]=−X^(−1)UX^(−1)` is correct. The generalized eigenvalue expression reduces D≥0, with equality only for X=Y, to I≥0. Cyclic trace and similarity prove simultaneous congruence invariance. They also prove `D(X^(−1),Y^(−1))=D(Y,X)`. The potential Φ itself is only orthogonally invariant; the report correctly distinguishes this from congruence invariance of D and g.

**△ Required trace placement correction, III.6 after (3.22).** The text writes `g_X(U,U)=tr(X^(−1/2)UX^(−1/2))^2`. Taken literally this squares the trace and is false. The correct expression is

`g_X(U,U)=tr[(X^(−1/2)UX^(−1/2))²]=||X^(−1/2)UX^(−1/2)||_F²`.

For X=Id and U=diag(1,−1), the metric equals two while the square of the trace is zero. This is a notation-level error in the positivity justification; the preceding metric formula and all conclusions survive the repair.

For `K=log(X^(−1/2)YX^(−1/2))`, the geodesic is `X^(1/2)exp(sK)X^(1/2)` and its length is `||K||_F`. Phase III's eigenvalue-speed lower bound is sound: ordered eigenvalues of a smooth symmetric path are locally Lipschitz; their derivatives exist almost everywhere, including a suitable choice within repeated eigenspaces, and the diagonal metric-speed contribution bounds the speed of their logarithms. The independent proof in the blind file avoids this eigenvalue-crossing issue entirely by differentiating the matrix exponential. Its factor

`2sinh((z_i−z_j)/2)/(z_i−z_j) ≥ 1`

in absolute value bounds the curve's metric speed below by the Frobenius speed of its matrix logarithm. Integration gives the same global distance lower bound, achieved by the displayed path.

The symmetrization is `4Σ_i sinh²((log λ_i)/2)`, whereas distance squared is `Σ_i(log λ_i)²`. The report's pair `(a,0)` and `(a/√2,a/√2)` gives different symmetrizations for every a≠0. Subtract their cosh series: the quadratic terms cancel and every coefficient from degree four onward is positive. Thus the claimed failure of a scalar distance-only formula in rank at least two is exact.

The conjugate is `−log det(Id−Θ)` on Θ≺Id and +∞ elsewhere. The maximum is at X=(Id−Θ)⁻¹. At a boundary eigenvalue Θ=1, the logarithmic term alone diverges as the matching eigenvalue of X grows, so the domain is strictly Θ≺Id. The argument is correct at the boundary as well as beyond it.

The determinant bounds also pass: I≥0 gives `det X≤exp(tr X−n)`, with equality only at Id; applying this to nX/tr X gives `det X≤(tr X/n)^n`, with equality exactly at scalar matrices. The Hessian of log det is −g, proving concavity.

**Metric-selection boundary.** The Hessian of the uniquely selected Φ fixes the displayed g. Bare affine invariance is weaker: the family `α tr(X⁻¹UX⁻¹V)+β tr(X⁻¹U)tr(X⁻¹V)`, α>0 and β>−α/n, is also congruence invariant. This is explicitly recorded in the primary paper [Thanwerdas–Pennec, formula (3)](https://arxiv.org/pdf/1906.01349). Phase III does not claim uniqueness from invariance alone; compressed summaries should preserve its Hessian/affine-coordinate premise.

## 3. Wishart transform and likelihood: correct model, wording repair

For supplied iid `Z_j~N(0,X)`, j=1,…,m with positive integer m and known mean zero, the scatter W=ΣZ_jZ_jᵀ has likelihood

`log L(X)=−(m/2)log det X−(1/2)tr(X^(−1)W)+constant`.

Factorization through W proves sufficiency. Gaussian integration for one sample gives the determinant factor `det(Id−2X^(1/2)ΘX^(1/2))^(−1/2)` precisely when the matrix inside is SPD; independence raises it to the mth power. The sample count, iid law, mean convention and covariance category are all material. For m<n the scatter is singular almost surely, exactly as the report warns. For m≥n it is SPD almost surely under the nonsingular Gaussian model.

If C=W/m is SPD, the likelihood is maximized at X=C, and the correct signed relation is

`[−log L(X)]−[−log L(C)]=(m/2)D(C,X)`.

**△ Wording repair in the last sentence of the likelihood paragraph.** Replace “the negative log likelihood difference from its maximum” by **“the excess of negative log likelihood above its minimum”**, or “the log-likelihood deficit below its maximum.” The displayed divergence has the correct orientation; only the extremum description is reversed. If C is singular, the SPD likelihood has no attained maximizer and this reference-to-C formula cannot be read with an SPD C.

## 4. Spatial orthogonal additivity: no hidden regularity

**Exact theorem.** On a supplied real inner-product space of dimension at least two, a globally nonnegative function r additive over every orthogonal pair is exactly `r(x)=c||x||²`, c≥0.

The independent proof and Phase III's proof coincide in their essential steps. Splitting into even and odd parts, equal-norm orthogonal decompositions force the even part to depend only on squared norm. Orthogonal vectors of arbitrary lengths make that dependence additive on R≥0; nonnegativity makes it monotone, hence linear. For the odd part, equal-length perpendicular vectors imply o(2x)=2o(x), while positivity bounds `|o(x)|≤c||x||²`. Apply the bound at x/2^k to force o=0. No continuity, measurability, homogeneity or rotation hypothesis is used. This exact argument already appears in the earlier sixteen-branch audit, so Phase III's presentation is validation and reuse of that strengthened theorem.

The essential assumptions have explicit countermodels. On a line, r(x)=x⁴ is nonnegative and orthogonally additive because an orthogonal pair must contain zero. Removing nonnegativity in higher dimension permits nonzero linear terms, including `||x||²+ℓ(x)`. If nonnegative z has orthogonal star composition `z(x+y)=z(x)+z(y)+z(x)z(y)`, its logarithm log(1+z) satisfies the theorem, so `z=exp(c||x||²)−1`. Mere z>−1 permits a linear term in that logarithm.

The theorem classifies an already designated observable satisfying the composition law. The scalar formal group gives a formula for combining scalar values; it does not assert that a chosen spatial map respects orthogonal vector sums. The distinction in III.10 is logically necessary.

## 5. Radial residual and whole-network spatial countermodels

For a twice differentiable nonvanishing profile f on x>0 and α=(D−1)/2,

`(x^αf)″/(x^αf)−[f″/f+(D−1)f′/(xf)]=(D−1)(D−3)/(4x²)`.

Two derivatives cancel all f′ and f″ terms, leaving α(α−1)/x². Thus (3.32) is correct and independent of the chosen profile. In the supplied integer-dimensional radial-operator category, cancellation is equivalent to D∈{1,3}; only an independently retained restriction D≥2 reduces that set to {3}. A non-Sigma profile such as exp(−x²) also cancels in dimension three, so cancellation has no reverse identifying force for I or p.

The whole-network models in III.10 and IV.11 are legitimate. Keep every scalar identity and canonical auxiliary construction fixed, and add a separate designated Euclidean spatial sort. In R² with r(x)=||x||⁴, perpendicular unit vectors give 4 on their sum and 2 as the sum of their values. In R² with squared norm, orthogonal additivity holds but the residual is −1/(4x²). In R¹ cancellation holds without dimension three. The canonical R⁴ Gaussian construction can coexist with each designated spatial sort and does not identify them.

The radial OU computation also supports the report's warning: for `t=||z||²/2`, `(1/2)Δ−(1/2)z·∇` acts on f(t) as `t f″+(D/2−t)f′`. Matching the supplied shape-two Laguerre operator selects D=4 for this **particular Gaussian realization**. It does not select a physical spatial dimension or imply D=3. Likewise the pullback of a one-dimensional metric is a tensor of rank at most one; it must not be confused with the full Hessian of a composite function, which includes a second-derivative term from the spatial map.

## 6. Rational trees, words and the real-domain boundary

The parent formulas in III.8 preserve gcd and strictly decrease numerator plus denominator, giving a unique root path for every positive reduced rational. The matrix freeness proof is correct: the outer L maps every positive input below one, while outer R maps it above one; equal actions force equal outer letters, which can be cancelled. No nonempty word is the identity.

The nonnegative determinant-one matrix generation proof also passes. Apart from Id, a column dominates the other componentwise; subtracting the smaller column preserves integrality, nonnegativity and determinant one and reduces the entry sum. Opposite strict inequalities with determinant one force the identity boundary case. Reversing the steps produces a generator word. The exact monoid is the **nonnegative-entry** part of SL₂(Z), including Id and generators with zero entries; it is not literally a strictly-positive-entry monoid.

Stern–Brocot updates interval endpoint columns on the right, while Calkin–Wilf successive path steps act on a fraction vector on the left. Their word-order reversal is correct. The endpoint convention in the report, initial first column (1,0)ᵀ and second (0,1)ᵀ, means upper endpoint first and lower second. This makes L and R align as stated. The explicit check CW(LR)=3/2 while SB(LR)=2/3 illustrates why unreversed words cannot be equated.

**△ Continued-fraction endpoint precision.** The usual unique finite expansion `[a₀;a₁,…,a_k]` requires a_k≥2 **when k≥1**; a one-term integer expansion [a₀] permits a₀≥1. Without that exception, the report's unqualified terminal rule excludes the root 1=[1]. Run lengths also include the usual terminal-minus-one correction because the parent algorithm stops at 1/1. The report claims complete Euclidean quotient lists with conventions, not an incorrect literal equality of every run length with every digit, so this is a small domain clarification.

The Farey branches and their ranges in (3.29) are correct. ψ₁(x)=1/(1+x) is decreasing, differs from R, and shares the midpoint endpoint with ψ₀. The forward branch formulas are mutually inverse on interiors and agree at the branch junction under the supplied convention.

**Full-domain converse.** Positive rational tree data determine L and R on their marked positive-rational inputs. Three marked pairs fix each map in the Möbius category, including its pole and the extension of L to −1<s<0. That extension is needed in `I(t)=∫_0^(t−1)L(s)ds` for t<1. Connected real-analytic continuation is an alternative. Without either rule, adding a small smooth bump to I in (1/4,1/2) preserves all positive-rational generator data and even strict convexity, yet changes the full function. This verifies the domain repair already made in III.8 and IV.8. A bare tree still has neither the numerical labels nor the coordinate maps.

## 7. Original code: exact collision criterion and a stronger obstruction

Subtracting placed Sigma values gives

`e(n)−e(m)=log((1+γn)/(1+γm))−μ(n−m)`.

The countable-curve criterion (3.31) is therefore exactly equivalent to injectivity on the specified integer carrier when all pairs in that carrier are excluded. Monotonicity beyond the closure point is a sufficient easier condition, not a necessary one. The admissible example γ=1, μ=log(5/4) has e(3)=e(4), while

`e(6)−e(8)=log(175/144)>0`.

This proves the product-by-representatives failure in IV.10 and the confusion of the prime label three with composite four. The same intrinsic I,p network permits this placement, so no branch depending only on intrinsic shape can rule it out.

**New strengthening: every collision fails multiplication.** Suppose n>m>0 and e(n)=e(m). Then

`μ(n−m)=∫_m^n γ/(1+γu)du`.

For every real k>1,

`e(kn)−e(km)=k∫_m^n[γ/(1+kγu)−γ/(1+γu)]du<0`.

In particular every integer k≥2 distinguishes the two products of the collided representatives. Thus, for this original Sigma code on integers at least two, **injectivity is necessary and sufficient for the representative-defined multiplication to be well defined**, not merely necessary for faithful reconstruction. This sharper conclusion follows from the strictly decreasing rational derivative and applies to every collision curve, beyond the single numerical example used in the report.

## 8. Transported integer structure, unit and alternative code

With injection, n↦e(n) is a bijection onto its image and transports multiplication exactly. The report handles the missing unit correctly: on the original n≥2 carrier, define reflexive divisibility using either equality or a nonunit factor; then adjoin an abstract 1_S before stating all gcd/lcm or divisor-lattice operations. It is not justified to identify 1_S with the real value σ(1) unless injectivity was checked for that enlarged domain.

Unique factorization proves the full III.9 table. Irreducibles are the encoded primes; their exponents give valuations, factorization length, distinct-prime count, componentwise gcd/lcm, products of finite exponent chains for divisor lattices, and divisor counts. Summing signs over square-free divisors gives `(1−1)^k`, hence the Möbius inversion identity. Dirichlet convolution is well defined because every element has finitely many divisors and unique quotients. A conventional nonzero multiplicative arithmetic function has value one at the unit; allowing the identically zero function is a harmless alternate convention, but arbitrary prescribed unit values would not satisfy the usual multiplicativity equation.

These operations are intrinsic to the supplied free commutative monoid. Numerical prime names, integer addition and size-dependent formulas such as the classical totient require extra numerical labels. Prime permutations preserve the abstract monoid. Phase III correctly avoids claiming an inverse from an unlabelled multiplication structure to the analytic Sigma shape.

The alternative code in Phase III is `n↦σ(r_*+n/μ)`. Since `μr_*+μ/γ=1`, its intrinsic t-coordinate is n+1, so it equals `H(n+1)+C_P` for the fixed placement-dependent additive constant C_P. Subtracting that constant gives the statement-only alternative `e₀(n)=H(n+1)`. For n≥1 these codes are strictly decreasing because `H′(t)=1/t−1<0` on t>1. They provide an injective arithmetic model for every placement and include the integer-unit label when indexed from one. They are different codes and do not alter any collision of the original n↦σ(n).

## 9. Euler-product converse: separately verified after comparison

The numerically labelled spectral identity `Tr(1+A)^(−s)=ζ(s)` and the Euler product `ζ(s)=∏_p(1−p^(−s))^(−1)` hold for Re s>1. Finite geometric expansion, unique factorization and absolute convergence prove the product. This step uses numerical integer multiplication and the marked exponential coordinate p^(−s); an abstract prime permutation does not preserve those numerical weights.

For the converse, let `Z(s)=∏_q(1−q^(−s))^(−m_q)` with positive integer multiplicities, real q>1, and convergence for all sufficiently large real s. Convergence already rules out infinitely many generators in any bounded interval reaching down to one. Thus a nonempty remaining multiset has a smallest q₀ with finite multiplicity m₀. Expanding the logarithm gives

`log Z(s)=Σ_q m_q Σ_(k≥1)q^(−ks)/k = m₀q₀^(−s)(1+o(1))`.

To justify the last limit, dominate after multiplication by q₀^s using the convergent series at one fixed sufficiently large s₀; every other factor has a strictly smaller exponential rate. Therefore

`q₀=lim_(s→∞)(log Z(s))^(−1/s)`,

`m₀=lim_(s→∞)q₀^s log Z(s)`.

Subtract the **entire** contribution `−m₀log(1−q₀^(−s))` and repeat. Removing the entire factor also removes powers that might coincide with another generator; it is crucial for the iterative proof. Local finiteness and convergence ensure that every generator is eventually reached. The empty multiset is detected by Z≡1. Hence the full product uniquely determines the numerical multiset within the stated category. Phase III's proof is correct but compressed; the domination and empty-product details above complete it.

## Recommended edits and proof status

1. Put the square inside the trace in III.6's metric-positivity sentence.
2. Replace “negative log likelihood difference from its maximum” with “negative log likelihood excess above its minimum.”
3. State the continued-fraction terminal-digit restriction only for expansions with at least two terms; preserve the root integer expansion.
4. Optionally strengthen III.9 with the general proof that every original-code collision obstructs multiplication.
5. Preserve the existing distinction between a canonical constructed auxiliary object and identification of an independently designated matrix, spatial, tree or arithmetic object.

All other audited statements and countermodels pass with their explicit domains. The blind file supplies direct proofs rather than finite numerical evidence. No new Lean/Coq certificate or mechanized matrix, metric, arithmetic or spatial theorem is claimed here. The separate probability audit now also contains the independently checked normalized analytic density `4t/(t+2)^3`, which settles the old exact-derivative-zero-set question negatively; that development does not affect these realization verdicts.
