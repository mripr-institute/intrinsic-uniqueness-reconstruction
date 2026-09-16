# Phase IV independent probability and transform audit

The statement-only derivations were recorded in [probability-blind.md](probability-blind.md) **before** opening the Phase III report. This comparison then read Phase III §§I.3–I.7, II.3, III.3, III.12 and IV.3–IV.6, and checked the older dependency ledger, sixteen-branch audit and manuscript for prior coverage. No global report was edited. All claims below refer to the marked intrinsic functions `I(t)=t−1−log t` and `p(t)=t exp(−t)`, t>0; placement parameters are outside this audit.

Verdict symbols: **✓ ⇔** means the exact node identifies the stated target within its candidate class; **✓ ⇒** is a valid forward implication; **△ +H** indicates an essential retained hypothesis or an ambiguous sentence needing qualification; **✗** is a refuted converse. “Old,” “strengthened,” and “new” describe novelty within this workspace's sequence of audits, not mathematical priority in the literature.

## Decision table

| Claim | Verdict after independent derivation | Classification relative to the prior audit |
|---|---|---|
| Positive measure on R, moments `(n+1)!` including n=0 | **✓ ⇔** Gamma(2,1); mass and support derived | **Strengthened in Phase III**: earlier E10 assumed a nonnegative probability law |
| Probability recurrence `(n+1)π_(n+1)=π_n` | **✓ ⇔** Poisson(1) | **New reduced identifier in Phase III**; basic Poisson/CGF correspondence already old |
| Full marked centered CGF or oriented KL slice → I | **✓ ⇔** as scalar-function reconstruction | **Old identity/reconstruction**, made explicit; **△** centering cannot recover an unmarked original location |
| Two exact marked max laws plus `F(0)=e^(−1)` | **✓ ⇔** standard Gumbel CDF, no smoothness premise | **Strengthened in Phase III** over the old full smooth density/Haar node |
| Linked deficit law plus exact coordinate involution | **✓ ⇔** continuous strict-branch potential J | **New joint converse in Phase III**; both separate forward nodes were old |
| All deficit cumulants replace its law | **✓ ⇔** for the deficit law; no candidate MGF premise needed | **Strengthened in Phase III**; displayed cumulant values were old |
| Reverse size bias, equilibrium, marked tilt | **✓ ⇔** with the stated boundary/parameter data | Size-biased exponential was **old**; explicit equilibrium/tilt inverses are **new immediate refinements in Phase III** |
| Gamma Lévy density plus zero drift in probability category | **✓ ⇔** Gamma subordinator law | **Old exact Lévy node**, with alternatives for identifying drift clarified in Phase III |
| Explicit Gamma self-decomposition | **✓ ⇒** compound-Poisson residual formula | **New immediate refinement in Phase III**; generic self-decomposability does not identify Gamma |
| Bernstein function from all integer samples | **✓ ⇔**; proof is correct | **New converse in Phase III**; **strengthened here to any complete integer tail** |
| Marked rooted/Borel coefficients → inverse germ | **✓ ⇔**; global p needs an analytic continuation category or a selected canonical extension | **Old** inverse; retain its domain and scaling conditions |
| Arbitrary tree law from Borel total size | **✗**; deterministic path countermodel | **Old identification boundary**, explicit in Phase III |
| One-ancestor iid GW law with Borel(1) total size | **✓ ⇔** Poisson(1) offspring/tree law | **New explicit reverse refinement in Phase III** of the old branching construction |

The main Phase III probability uniqueness theorems survive. The material edit is to disambiguate the centered-CGF sentence; the useful additional reduction is Bernstein recovery from an integer tail. The existing drift, coordinate, normalization, density-link and branching qualifications cannot be removed by the presented cross-branch constructions.

## 1. Complete moments: proof and sharp boundary

**Exact statement.** Let μ be a finite positive Borel measure on R with `∫x^n μ(dx)=(n+1)!` for every integer n≥0. Then `μ(dx)=1_(x>0)x exp(−x)dx`.

For 0<c<1, positivity permits monotone summation:

`∫cosh(cx)μ(dx)=Σ_(n≥0)(2n+1)c^(2n)=(1+c²)/(1−c²)²`.

Since `exp(c|x|)≤2cosh(cx)`, the bilateral MGF exists throughout a strip about the imaginary axis. Dominated Taylor expansion near zero gives `(1−z)^(−2)`; analytic continuation and uniqueness of characteristic functions identify Gamma(2,1) on the **whole real line**. Phase III I.6 supplies the same correct argument. Mass one is the zeroth moment. The topological support is [0,∞), while the law has no atom at zero.

The support conclusion is substantive: it was an input in the earlier E10. Omitting only the zeroth equation permits an arbitrary additional positive atom at zero. Dropping positivity permits the signed Schwartz perturbation described in I.6: the inverse Fourier transform of a real even smooth bump supported away from zero has every polynomial moment zero. Finitely many prescribed moments allow bounded compactly supported density perturbations orthogonal to those monomials.

The adjacent exponential-moment support result also passes: `∫e^(−ns)ν(ds)=(n+1)^(−2)` for n≥0 forces total mass one and excludes `s≤−ε` by exponential growth. Then `y=e^(−s)` puts the problem on [0,1], and polynomial density identifies the measure with density −log y, hence `ν(ds)=s exp(−s)ds`. This is the correct kernel identification in I.6–I.7; it does not identify arbitrary stationary coordinate densities from spectra.

## 2. Poisson recurrence, CGF and KL: valid scalar reconstruction, location caveat

Iteration and normalization give `π_n=e^(−1)/n!` from the displayed recurrence. Direct calculation yields

`Λ(u)=log E exp(u(N−1))=e^u−1−u`, and `I(t)=Λ(log t)`.

The full marked family identities are

`D(Pois(a)||Pois(b))=aI(b/a)`,

`D(Exp(rate a)||Exp(rate b))=I(b/a)`,

`2D(N(0,variance a)||N(0,variance b))=I(a/b)`.

Thus the slices specified by Phase III I.5 and the statement-only task recover I exactly. Their orientations, the meaning of rate versus variance, and the marked t parameter matter. The forward Poisson divergence `D(Pois(t)||Pois(1))=t log t−t+1` is a different potential; the report correctly distinguishes it and correctly gives the centered Legendre transform on z≥−1, including its boundary value one.

**△ Repair to I.5, line 147.** The sentence “Conversely the complete CGF near zero determines the law and recurrence by MGF uniqueness” should distinguish uncentered K from centered Λ. MGF uniqueness determines the random variable whose CGF was actually supplied. For `N_k=Y+k`, `Y~Pois(1)`, k≥1,

`log E exp(u(N_k−EN_k))=e^u−1−u`,

yet N_k is not Poisson(1) and does not satisfy the displayed probability recurrence. This countermodel even stays on N₀. It refutes only recovery of an **unmarked original location**, not reconstruction of I or the law of the centered variable.

Suggested exact replacement:

> The uncentered CGF `K(u)=e^u−1` determines the Poisson(1) law and its recurrence. The centered CGF `Λ(u)=e^u−1−u` determines the centered law and reconstructs I; it determines the original Poisson(1) law when the centering shift is marked as one, equivalently when the datum is `log E exp(u(N−1))=Λ(u)`.

If the original sentence intended the uncentered K throughout, this is a clarity repair rather than a failed theorem. A complete centered CGF interpreted as already attached to the fixed variable N−1 also has no defect.

## 3. Gumbel max laws: no hidden regularity needed

**Exact statement.** A CDF F on R with `F(x+log 2)^2=F(x)`, `F(x+log 3)^3=F(x)` for every x and `F(0)=e^(−1)` is `exp(−exp(−x))`.

The base-2 equation gives `F(k log 2)=exp(−2^(−k))` for every integer k. Monotone sandwiching forces `0<F(x)<1` at every finite x, so `g=−log F` is finite, positive and nonincreasing. On the dense subgroup generated by log 2 and log 3, `g(d)=exp(−d)`. The subgroup is dense because rational dependence would imply an equality of positive powers of distinct primes. Approximation from both sides and monotonicity give g(x)=exp(−x) everywhere. This validates I.4 without an initial support, smoothness or strict-monotonicity assumption.

Dropping the anchor leaves `exp(−c exp(−x))`, c>0. Keeping only the base-2 equation and the anchor admits `exp(−exp(−x)h(x))`, where `h(x)=1+εsin(2πx/log 2)` and ε is sufficiently small that h>0 and h′<h. The counterexamples in I.4 are valid.

**Measure notation clarification.** With t(x)=exp(−x), the precise positive-measure statement is

`t_*(dF)=exp(−t)dt=p(t)dt/t`.

As an oriented differential, dx=−dt/t; the measure substitution uses its absolute Jacobian. Also dt/t is the infinite Haar measure, calibrated by `∫p(t)dt/t=1`; it is not a probability Haar measure. This makes the intended convention in (1.11) explicit. It is the Haar-weighted probability, not the Gamma probability `p(t)dt`, that becomes Gumbel under x=−log t.

## 4. Joint deficit law and involution: the continuous proof is complete

**Exact class.** J:(0,∞)→[0,∞) is continuous, J(1)=0, strictly decreasing left of one and strictly increasing right of one, tends to infinity at both endpoints, and `q_J=exp(−1−J)` integrates to one. The supplied law is that of J(T) under **this same** q_J, and the supplied involution pairs its equal-level roots in the same t coordinate.

Let `a(v)≤1≤b(v)` be the two inverse branches, including a(0)=b(0)=1, and `w(v)=b(v)−a(v)`. The pushforward of Lebesgue measure under J has locally finite Stieltjes distribution w. Hence

`dF(v)=exp(−1−v)dw(v)`, `w(v)=e∫_[0,v]exp(s)dF(s)`.

If j is the exact coordinate involution, `D(t)=t−j(t)` is a continuous increasing bijection from [1,∞) to [0,∞). Therefore `b(v)=D^(−1)(w(v))` and `a(v)=j(b(v))`. These reconstruct both branches, and thus J everywhere. There is no hidden ordinary derivative or density-of-F assumption. Phase III (1.7)–(1.8) is correct; the strictness and endpoint assumptions it explicitly supplies justify all inversions.

**Both marginal countermodels remain valid after normalization.** A common small smooth displacement of a(v) and b(v), supported in a compact positive level interval, preserves w and thus the complete deficit law and probability mass, but changes J and j. Conversely, take two disjointly supported smooth level bumps f,g and set `J=(u+εf(u)+δg(u))∘I`. Small coefficients preserve strict monotonicity of the level reparameterization and its endpoint behavior. The mass functional has nonzero δ derivative whenever g≥0 is nonzero; the implicit function theorem chooses δ(ε) so that mass remains one. This preserves j but changes J. Supports away from zero also retain `f_level(0)=0` and `f_level′(0)=1`. This verifies, rather than merely assumes, the strengthened countermodels in I.3 and IV.3.

**Deficit cumulants.** Direct integration gives

`M_V(s)=exp(−s)Γ(2−s)/(1−s)^(2−s)`, s<1,

and divergence for s≥1. Expanding its logarithm yields `κ₁=γ_E` and `κ_n=(n−1)![ζ(n)−1/(n−1)]` for n≥2. The Gamma-series identity used in this algebra was checked against [NIST DLMF 5.7.3](https://dlmf.nist.gov/5.7#E3). Cumulants understood algebraically through finite moments recover all moments. For any candidate nonnegative law with those moments, monotone convergence of the positive exponential series gives a finite MGF for small positive s, since the same series converges for the known law. MGF uniqueness then recovers F. The report's removal of a separate candidate-MGF assumption is valid.

The zeta/spectral detour in I.3 constructs a canonical kernel but cannot identify the designated J: the common-displacement examples retain all the cumulants used by that detour. The density link and coordinate involution remain identifying data in this inverse problem.

## 5. Reverse probability transforms and Gamma Lévy data

**Size bias.** For a nonnegative probability μ of finite positive mean m, the size-biased law is `β(dx)=xμ(dx)/m`. If μ({0})=0 and `c=∫x^(−1)β(dx)<∞`, then `μ(dx)=β(dx)/(cx)` and m=1/c. Gamma(2,1) size bias therefore reverses to Exp(1). Every mixture `rδ₀+(1−r)Exp(1)`, 0≤r<1, has that same size bias, proving the necessity of excluding an atom at zero. III.3 states the correct boundary.

**Equilibrium: an available hypothesis reduction.** For any positive lifetime X of finite mean m, the equilibrium law has a canonical decreasing right-continuous density `q(t)=P(X>t)/m`. Its right limit at zero gives m=1/q(0+), and `P(X>t)=mq(t)` recovers the entire original law, including any positive atoms, without assuming that the original law has a density. Equality almost everywhere of the equilibrium densities determines their canonical monotone representatives.

For the observed `q(t)=(1+t)exp(−t)/2`, this yields m=2 and survival `(1+t)exp(−t)`, hence density p by differentiation. Thus no independent smoothness assumption on the candidate is needed when the **full target equilibrium law** is supplied. The actual displayed q is smooth. The formula `p=−mq′` in III.3 is correct in its stated absolutely-continuous-density class; the survival-function inverse gives the stronger general statement. Admitting an atom at zero again permits arbitrary mixtures with δ₀ because both positive tail and mean scale by the same factor.

**Tilt.** For a given tilt θ, the inverse is

`μ(dx)=e^(−θx)μ_θ(dx)/∫e^(−θy)μ_θ(dy)`.

The Gamma tilted density, its mean, variance and cumulants displayed in III.3 are correct. A missing tilt/rate mark leaves a unit-scale ambiguity.

**Lévy density.** The density `ν(dx)=2exp(−x)dx/x` satisfies the Lévy integrability condition. Integrating its derivative in λ gives `ψ(λ)=2log(1+λ)` when drift and killing vanish, and the semigroup transform is `(1+λ)^(−2r)`. A probability semigroup excludes killing but permits any added drift d≥0. With this exact ν, the alternatives in III.3 are indeed equivalent ways to force d=0: ψ(λ)/λ→0, support infimum zero at time one, or mean two. The shifted Gamma process `S_r+dr`, d>0, has exactly the same ν. This is a genuine necessary qualifier, already preserved by Phase III.

**Self-decomposition.** The independent residual for `T =_law cT′+Y_c`, 0<c<1, has Lévy density `2(exp(−x)−exp(−x/c))/x`. It is nonnegative, with total mass `−2log c`, and its compound-Poisson zero atom is c². Its Laplace transform is `((1+cλ)/(1+λ))²`, so the displayed construction is correct. Independence here is constructed on a product space. Neither self-decomposability nor infinite divisibility alone identifies Gamma shape or rate.

The nearby Stieltjes statements also pass: `(1+λ)^(−2)` is completely monotone but cannot be a nonzero Stieltjes function, since λ times it tends to zero whereas a nonzero positive Stieltjes representation forces positive lower limit. The actual probability Stieltjes transform is `1−ze^z E₁(z)`; splitting `t/(t+z)` and then applying Laplace uniqueness twice proves the stated formula and injectivity.

## 6. Bernstein sampling: correct theorem and stronger tail version

**Phase III statement: ✓ ⇔.** Every Bernstein function is determined by its values at all integers n≥0. Its representation is

`f(λ)=k+dλ+∫_(0,∞)(1−exp(−λx))ν(dx)`.

This representation and its integrability/uniqueness conditions were checked against the authors' [Deng–Schilling research paper, formula (2)](https://arxiv.org/pdf/1606.04610). The sample argument is independently proved here and is not attributed to that paper.

Define the finite measure on [0,1]

`ρ=dδ₁+(x↦exp(−x))_*[(1−exp(−x))ν(dx)]`.

Then `f(n+1)−f(n)=∫y^nρ(dy)`. All n≥0 give all compact-interval moments, so uniform polynomial approximation determines ρ. Its atom at one yields d; undoing the pushforward and positive weight yields ν; f(0)=k. This fully validates (3.13). A general smooth function fails the theorem because an added `εsin(2πλ)` vanishes at all sampled integers; the Bernstein category does essential work.

**Stronger exact theorem, new in this audit.** For any integer N≥1, knowing f(n) for every n≥N already determines f. The increments at n=N,N+1,… are all moments of the finite measure `η(dy)=y^Nρ(dy)`. Compact moment uniqueness determines η. The representation itself implies `ρ({0})=0`; divide η by y^N on (0,1] to recover ρ, then recover d and ν as above. The one value f(N) fixes k. Consequently f(0) and any finite initial set of integer samples are redundant. This directly strengthens the Phase III result without a new candidate hypothesis.

## 7. Rooted/Borel coefficients: precise continuation and branching conclusions

For the formal solution R=z exp(R), Lagrange inversion yields

`[z^n]R(z)^k=(k/n)n^(n−k)/(n−k)!`, n≥k≥1.

The complete rooted coefficients `n^(n−1)` with their EGF convention therefore determine the inverse germ `z=t exp(−t)`. The Borel PGF is `B(s)=R(s/e)` and has inverse `s=t exp(1−t)=e p(t)`. The factor e is a retained scale mark. The radius 1/e and the coefficient formulas in III.12 are correct. The increasing solution B(s) reaches one as s approaches one, so its coefficients sum to one.

**△ Exact global formulation.** If a candidate p is real analytic on the connected interval (0,∞) and agrees with this inverse germ for small positive t, then analytic uniqueness forces p(t)=t exp(−t) throughout the interval. Equivalently one may **construct** the canonical global representative using that symbolic formula. These are distinct formulations; a formal germ does not identify every smooth global extension. Phase III explicitly speaks of the canonical analytic representative and warns about smooth extensions in its scope, so the qualified theorem passes. Any compressed diagram claiming an unqualified germ-to-arbitrary-global-function equivalence must retain this condition.

**Stronger smooth countermodel with normalization.** Choose a nonzero smooth h compactly supported in (2,3) with integral zero and set `p_ε=p+εh`. For sufficiently small nonzero ε, positivity and strict decrease on the support survive; outside the support p_ε=p. Thus p_ε is a positive normalized density with the same complete germ at zero, the same maximum `p_ε(1)=e^(−1)`, the same two monotone branches and endpoint behavior, but differs globally. This shows that even normalization and the calibrated shape conditions do not replace analyticity for this local-to-global claim.

**Tree identifiability.** Borel total size alone does not determine an arbitrary tree law: a deterministic rooted path of a sampled Borel size has the same total size but no branching vertex; a Poisson GW tree has positive probability of two children at its root. Alternatively a star and a path of the same sampled size give two explicit distinct laws.

Within the iid Galton–Watson class started from one ancestor, let Φ be the offspring PGF. Conditioning on the root offspring and using independent descendant trees gives `B(s)=sΦ(B(s))`. Since B maps (0,1) onto (0,1), and also satisfies `B(s)=s exp(B(s)−1)`, one obtains `Φ(w)=exp(w−1)` for 0<w<1. Analytic coefficient uniqueness recovers the Poisson(1) offspring distribution; the iid construction then fixes the tree law. No tree-shape inference is smuggled in from counts alone.

## Recommended report changes and verification limits

1. Clarify I.5's centered-CGF converse using the replacement above; preserve its valid reconstruction of I.
2. State the Bernstein converse using a complete integer tail if the strongest proved reduction is desired.
3. Use the survival-function equilibrium inverse to avoid a needless candidate density regularity premise.
4. Express (1.11) as a pushforward identity or use an absolute Jacobian; retain the distinction between Haar weighting and the Gamma probability.
5. Retain connected real analyticity or explicitly say “constructed canonical global representative” wherever a germ or formal coefficient sequence is promoted to a full-domain function.

The other main probability proofs need no repair. The conclusions rest on the analytic and measure-theoretic arguments given above and in the prior blind file. No finite numerical sample or symbolic check was used as evidence for a universal uniqueness theorem, and no new formal mechanization is claimed.

## Subsequent independent check: exact derivative-zero sets do not identify Gamma

After completing the blind probability audit and its comparison, the coordinating auditor supplied the candidate family

`f_k(t)=(k−1)k^k t/(t+k)^(k+1)`, t>0, k>1.

The following normalization and derivative calculation were independently checked here; this addendum is not represented as part of the original blind derivation.

Substitution t=ku and a beta integral give

`∫_0^∞ t/(t+k)^(k+1)dt=k^(1−k)B(2,k−1)=k^(−k)/(k−1)`.

Thus f_k is a positive probability density, real analytic on (0,∞), vanishing at zero and infinity. Direct differentiation gives the base case, and for every n≥1 induction gives

`f_k^(n)(t)=(-1)^(n−1)(k−1)k^(k+1)(k+1)_(n−1)(n−t)/(t+k)^(k+n+1)`.

Indeed the derivative of `(n−t)/(t+k)^(k+n+1)` is `−(k+n)(n+1−t)/(t+k)^(k+n+2)`, which gives exactly the next rising factorial. Every prefactor is nonzero, and the denominator is positive on t>0. Therefore the **entire positive zero set** of f_k^(n) is `{n}`, with a simple zero, for every n≥1. These are precisely the Gamma(2,1) derivative zero sets, since `(t e^(−t))^(n)=(-1)^(n−1)(n−t)e^(−t)`.

The simplest example is `f_2(t)=4t/(t+2)^3`, which has an algebraic tail and differs from `t e^(−t)`. Consequently the exact-all-zero-sets smooth positive probability converse left **?** in Phase III III.4/IV.3 is **✗**. This counterexample retains normalization, positivity, analyticity, endpoint vanishing and the complete zero sets, not merely selected incidences. It does not claim to retain a separately imposed height `f(1)=e^(−1)` or exponential-tail condition. Those were not assumptions of the stated unresolved class.
