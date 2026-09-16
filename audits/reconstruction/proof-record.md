# Sigma Phase IV: complete proof and counterexample record

This record supplies the proof interfaces used by the frozen theorem and graph, followed by the independently rebuilt local proofs. A statement about a candidate law identifies a measure first; its pointwise density is then its prescribed continuous representative. Numerical diagnostics do not establish the universal statements. The source audits remain separately available, with their blind-review custody and disagreements intact.

## Proof register

| IDs | Exact proof location in this record / independent source |
|---|---|
| C0, IV-C | Intrinsic and placement calculations immediately below |
| C1–C8 | Core/series appendix: CS01–CS05 and CS12–CS14; C8 is the continuation boundary |
| P1–P6 | Probability appendix sections 1–7; core E7–E13 supplies ODE/hazard interfaces |
| P7 | Entropy characterization below |
| P8 | Convolution completion below and probability appendix Lévy/self-decomposition section |
| P9 | The linked one-scale self-decomposition converse below |
| O1–O6 | Operator appendix sections 1–8; Bernstein tail reduction also independently in probability appendix |
| O7 | Complete Laguerre polynomial observations below |
| F1–F2 | Core/series appendix CS06–CS09, including full residue proof and marked inverse maps |
| M1–M2 | Realizations appendix sections 1–3; its blind proof is included for the full distance lower bound |
| M3 | Isotropic radial construction below; realizations appendix gives the normalized OU calculation |
| R1–R2 | Realizations appendix sections 6–9, including the general collision obstruction |
| B1–B2 | Realizations appendix sections 4–5; core/series CS10–CS11 |
| Z4 | Exact all-order countermodel appendix, independently checked in two other appendices |
| IV-A–IV-B | Explicit local inverses in this register plus the composition proof below |
| IV-D | [Minimal primitives](sigma-phase-iv-minimal-primitives.md), including its full shape-perturbation proof and deletion witnesses |
| IV-E–IV-F | Canonical construction and boundary calculations below and in the listed appendices |

The formalized parts, their actual Lean theorem names and omitted analytic steps are recorded in [verification](sigma-phase-iv-verification.md). No theorem in this register is promoted to machine verification merely because it shares notation with a checked lemma.

## C0 / IV-C. Intrinsic identities and placed normalization

For \(t>0\), the real logarithm and exponential are inverse. Thus \(H=\log t-t+1\) gives \(I=-H\) and \(p=e^{H-1}=te^{-t}>0\), while \(H=1+\log p\) is the inverse representation. Integration by parts gives \(\int_0^\infty p=1\) and \(\int_a^\infty p=(1+a)e^{-a}\). There is no free density amplitude in this normalization.

Let \(\mu>0,0<a<1\) and \(\gamma=\mu/a\). The map \(t=\mu r+a\) is a bijection from \((-a/\mu,\infty)\) to \((0,\infty)\). Directly,
\[
 \frac{\mu^2(1+\gamma r)}{\mu+\gamma}
 =\frac{\mu}{1+a}(\mu r+a),
\]
so
\[
 \sigma_P(r)=H(t)+\log\frac\mu{1+a}+a-1,
 \qquad e^{\sigma_P(r)}dr=\frac{p(t)dt}{(1+a)e^{-a}}.
\]
On \(r\ge0\) the transformed domain is \(t\ge a\), and the integral is one. On the full analytic domain the integral is \(e^a/(1+a)\). This explains why global analytic reconstruction and the original probability normalization have different domains.

Set \(q=\gamma/(1+\gamma r)>0\). Differentiation gives \(\sigma'=q-\mu\), \(\sigma''=-q^2\), hence
\[
 \mu=\sqrt{-\sigma''}-\sigma',\qquad
 \gamma=\frac{\sqrt{-\sigma''}}{1-r\sqrt{-\sigma''}}.
\]
The denominator equals \((1+\gamma r)^{-1}>0\). Thus the placed family recovers \(P\) uniquely. Conversely the above substitution constructs it from \((S,P)\). Changing \(\mu\) changes the curvature at closure; changing \(a\) at fixed \(\mu\) changes \(r_*=(1-a)/\mu\). These changes preserve the intrinsic object and prove both placement-coordinate deletion witnesses. Recovering parameters from a jet outside the family is refuted by a bump away from the observed point.

## P7. The complete entropy clause

This is an old alternative P1 characterization, not a new branch. The candidate class consists of Lebesgue probability densities \(f\) on \((0,\infty)\) with \(\int tf=2\), \(\int f\log t=1-\gamma_E\), finite absolute integrals for these constraints, and well-defined differential entropy (or the corresponding extended relative-entropy convention). For \(p\), the constraints follow by Gamma integration and its derivative.

Since \(\log p=\log t-t\), every candidate has \(\int f\log p=-1-\gamma_E\). Nonnegativity of relative entropy follows, for instance, by integrating \(z\log z-z+1\ge0\) with respect to \(pdt\), where \(z=f/p\). It gives
\[
 D(f\Vert p)=\int f\log f+1+\gamma_E\ge0.
\]
Consequently entropy is at most \(1+\gamma_E\), achieved by \(p\); equality forces \(f/p=1\) almost everywhere by the strict equality condition in the scalar inequality. Conversely this same calculation proves \(p\) is the unique maximizer. Only the **complete constrained maximizer clause** identifies \(p\); generic maximum entropy terminology does not.

## O7. Complete marked Laguerre polynomial observations

Let \(M\) be a finite positive measure on \(\mathbb R\), with mass one and all polynomials integrable. Suppose
\(\int L_n^{(1)}(t)M(dt)=0\) for every \(n\ge1\), with the standard marked polynomial coefficients. Their leading coefficient is \((-1)^n/n!\ne0\). Therefore the nth equation uniquely determines the nth ordinary moment from all lower moments. The known measure \(pdt\) satisfies the same equations. Induction proves that every moment of \(M\) is \((n+1)!\). The independently proved P1 moment theorem on \(\mathbb R\) identifies \(M=pdt\), including its positive support. Conversely Laguerre orthogonality gives these equations.

Thus complete marked orthogonality reverses to the intrinsic measure. A specified full orthonormal basis is more than necessary for that particular inverse; a bare eigenvalue list is not a substitute for the marked polynomial coefficients and measure linkage.

## P8. Unique probability convolution completion

In the category of probability measures on \([0,\infty)\) with additive time and convolution, define \(\mu_0=\delta_0\) and \(\mu_r=\Gamma(2r,1)\) for \(r>0\). The Gamma integral gives
\[
 L_{\mu_r}(\lambda)=(1+\lambda)^{-2r},\quad\lambda\ge0.
\]
Products of these transforms and Laplace uniqueness prove \(\mu_r*\mu_s=\mu_{r+s}\), establishing existence without an extra continuity assumption.

Conversely let \(\eta_r\) be any such probability convolution completion with \(\eta_1=pdt\). For fixed \(\lambda\ge0\), its Laplace transform is strictly positive and at most one. Thus
\(g_\lambda(r)=-\log L_{\eta_r}(\lambda)\) is nonnegative and additive. Nonnegativity makes it monotone: if \(s\ge r\), then \(g(s)=g(r)+g(s-r)\ge g(r)\). Rational additivity and rational squeezing give \(g(r)=r g(1)=2r\log(1+\lambda)\) for all real \(r\ge0\). Laplace uniqueness gives \(\eta_r=\mu_r\). Weak continuity follows from these transforms and the probability continuity theorem. No additional time parameter remains; the law at time one and the unit-time mark identify the shape scale.

Independent increments with these laws are constructed by finite products on disjoint time intervals. The compatible finite-dimensional distributions define a process law in the usual extension framework; a canonical subordinator path version requires its standard path-space convention. This does not assert that an independently supplied process with the same time-one marginal has those increments. The process \(X_r=rT\) has \(X_1\sim p\) and dependent increments, so the identification premise is necessary.

Differentiating in \(\lambda\) and integrating back from zero gives
\[
 2\log(1+\lambda)=\int_0^\infty(1-e^{-\lambda x})\frac{2e^{-x}}x\,dx.
\]
The integral is finite by its endpoint behavior. A probability semigroup excludes killing; a Lévy measure alone still permits the added drift \(d\lambda\), \(d\ge0\). The complete time-one transform above forces \(d=0\). Moreover
\[
 \frac{2e^{-x}}x=2\int_1^\infty e^{-sx}ds,
 \qquad \log(1+\lambda)=\int_1^\infty\frac{\lambda}{s(s+\lambda)}ds.
\]
The first identity makes the Lévy density completely monotone by differentiation under the integral on compact positive intervals; hence this exponent is a complete Bernstein function. The second follows by subtracting \(1/(s+\lambda)\) from \(1/s\). Its derivative \(2/(1+\lambda)\) is a Stieltjes function. For any specified nonnegative self-adjoint operator these scalar integral identities pass to the spectral functional calculus on its natural domains; they do not choose an arbitrary operator from the scalar source. The other Stieltjes and self-decomposition assertions, and their exact reverse information, are proved in the probability/operator appendices.

## P9. One linked self-decomposition determines the original law

Fix \(0\le c<1\). The observed residual law can be constructed as the sum of two independent variables with law \(c\delta_0+(1-c)\operatorname{Exp}(1)\), since its transform is
\[
 R_c(\lambda)=\left(c+\frac{1-c}{1+\lambda}\right)^2
 =\left(\frac{1+c\lambda}{1+\lambda}\right)^2.
\]
In particular its zero atom is \(c^2\), which identifies \(c\) within this family, and its characteristic function is \(((1-ic\xi)/(1-i\xi))^2\).

Suppose an arbitrary Borel probability variable on \(\mathbb R\) satisfies \(X\stackrel d=cX'+Y_c\), where \(X'\) has the same law as \(X\) and the two terms are independent. Its characteristic function satisfies
\[
 \varphi(\xi)=\varphi(c\xi)
       \left(\frac{1-ic\xi}{1-i\xi}\right)^2
 =\varphi(c^n\xi)\left(\frac{1-ic^n\xi}{1-i\xi}\right)^2.
\]
Continuity of every probability characteristic function at zero gives \(\varphi(c^n\xi)\to1\). Hence \(\varphi(\xi)=(1-i\xi)^{-2}\), and characteristic-function uniqueness gives \(X\sim\Gamma(2,1)\). Positive support, density and moments are conclusions. Conversely independent Gamma(2,1) \(X'\) and the displayed residual have the required characteristic function, so they construct the decomposition. This is **+H; ⇔** with the original-law linkage; one residual entry suffices and its scale need not be supplied separately.

The residual law alone does not identify an independently named, unrelated original law: hold \(Y_c\) fixed and choose Gamma(2,1) or Gamma(3,1) for an unrelated \(X\). At \(c=1\), the residual is \(\delta_0\) and both of those laws satisfy the decomposition equation, so contraction cannot simply be removed. The endpoint \(c=0\) does identify \(X=Y_0\); positivity of \(c\) is not a necessary uniqueness hypothesis. Independence can instead be replaced by the exact characteristic-function factorization as identifying data; neither formulation follows for an arbitrary supplied coupling. This closes the existing native conditional inverse and does not assert that generic self-decomposability determines Gamma shape or rate.

## M3. Isotropic Gaussian angular identification

The ambient \(\mathbb R^4\), its Euclidean structure and \(T=\|Z\|^2/2\) are supplied. Suppose \(T\sim p\) and the vector law is rotation invariant. As \(T>0\) almost surely, let \(U=Z/\|Z\|\). For bounded measurable \(a(T)\), \(b(U)\), rotational invariance gives the same expectation after applying any rotation to \(U\). Average over normalized Haar measure of the compact rotation group and apply Fubini. Transitivity on the sphere gives
\[
 \mathbb E[a(T)b(U)]=\mathbb E[a(T)]\int_{S^3}b(u)d\omega(u).
\]
Thus \(U\) is uniform and independent of \(T\); equivalently the conditional angular law is uniform for almost every radius. This proof does not select pointwise versions of conditional distributions on null radii.

Conversely construct independent \(T\sim p\) and uniform \(U\), and put \(Z=\sqrt{2T}U\). The radius density is \(p(r^2/2)r=(r^3/2)e^{-r^2/2}\). Since sphere area is \(2\pi^2\), division by polar volume \(2\pi^2r^3dr\) gives the Cartesian density \((2\pi)^{-2}e^{-\|z\|^2/2}\), the standard Gaussian. This proves existence and uniqueness within the supplied isotropic category.

For a smooth radial test \(f(t)\), \(|\nabla t|^2=2t\), \(\Delta t=D\), and \(z\cdot\nabla t=2t\). Hence
\[
 \left(\tfrac12\Delta-\tfrac12z\cdot\nabla\right)f(t)
 =t f''(t)+(D/2-t)f'(t).
\]
Matching the canonical Laguerre coefficient gives \(D=4\) in this auxiliary Gaussian realization. The independent spatial residual theorem concerns a separately designated spatial sort and does not identify it with this one.

## IV-A / IV-B. Global uniqueness and closure proof

Fix the marked candidate classes in the registry. For each row, the following appendices prove an identifying inverse and verify the forward target on the explicit \(S\). In rows represented by a law or a transform, equality is equality of the linked candidate law; in rows represented by a potential, equality is equality on its marked domain. In a formal row, the direct identity is formal and the global inverse is restricted to the explicit analytic continuation class. These distinctions are part of the maps' signatures.

Let \(e_A:S\mapsto A\) and \(d_A:A\mapsto S\) be those maps, on the solution classes for the exact clauses. Their proofs establish \(d_Ae_A=\mathrm{id}\) and \(e_Ad_A=\mathrm{id}\). For two presentations, define \(f_{AB}=e_Bd_A\). Then
\[
 f_{BA}f_{AB}=e_A d_B e_B d_A=e_A d_A=\mathrm{id}_A,
\]
and similarly in the other direction. This proves the one global mutual-reconstruction theorem. Uniqueness of \(S\) gives compatibility of every route. A disagreement about any identifying inverse must be settled locally before applying this composition; the independent audit ledger records those settlements.

For a context-indexed template, the same equations hold in the fixed \(C\) fibre with \((S,C)\). Forgetting \(C\), or applying an unrelated canonical-selection recipe after a forgetful map, does not preserve these equations. The explicit Gamma2/Gamma3 operator countermodel proves that distinction. The machine graph therefore computes the intrinsic identifying component without conditional, transport or construction-only edges. Its finiteness makes maximality a bookkeeping statement about the enumerated universe once the local proofs and countermodels have been supplied.

## Completeness and counterexample scope

All Phase III sections are mapped to an independent verdict in [the audit ledger](sigma-phase-iv-independent-audit.md). The full/quotient graph carries every theorem ID and its retained data. The remaining consequences (finite jets, deficit marginal, involution alone, zero sets, finite spectral invariants, unmarked labels and external realizations) each have a precise lost datum or explicit countermodel in the appendices. In particular, Z4 resolves the previously unknown exact-zero-set implication in its stated class; more restrictive entire or globally log-concave classes are not added to this finite universe.

The following appendices reproduce the independently rebuilt proofs. Their generic audit words concern review outcomes; the mathematical statuses are the specified identities, implications, conditional implications and counterexamples. Original source files preserve the blind/unblind review record separately.



# Appendix A. Core and formal-series proofs

# Phase IV independent core and scalar-series audit

The statement-only audit was saved as [core-series-blind.md](phase-iv-audit/core-series-blind.md) before opening Phase III. This audit subsequently read Phase III §§I.1–I.2, II.1–II.2, III.4–III.5, III.7, III.11, IV.1–IV.3, IV.8–IV.9, together with the earlier master E0–E14 clauses in the manuscript, dependency ledger and sixteen-branch audit. It does not modify the manuscript or global report.

**Verdict.** The stated calibrated core, Todd tower, characteristic-series inverses, and conditional universal Thom comparison pass. The reduced exact Legendre theorem also passes: either lower semicontinuity or convexity suffices. The precise derivative-zero uniqueness question left open in Phase III is **refuted**, including in the real analytic positive probability class. The proof is CS14 below. The main remaining qualifications are the marked coordinate, the candidate category, normalizations, and the separation of universal scalar data from topology.

**Blind/unblind reconciliation.** Blind CS03 correctly warned that an unrestricted conjugate identifies only a convex closure, but its generic closed-convex prescription was stronger than necessary for this particular target. Phase III's exposed-minimizer argument proves the sharper lsc-only or convex-only converse; the full proof was independently checked below. The later beta-prime counterexample was supplied by the coordinating auditor after the blind record, and was then independently verified. It is not represented as a blind discovery.

Throughout, the intrinsic marked real coordinate is `t>0`, `H(t)=log(t)−t+1`, `I=−H`, `p=exp(H−1)=t exp(−t)`. The reciprocal passages require positive p and retain its multiplicative level. Placement is separate: none of these intrinsic nodes recovers an unmarked `(mu,a)`.

## Frozen E0–E14 interface

Every forward implication in this table follows from the displayed intrinsic functions. Every reverse is valid in exactly the category stated. Local audit exports retain the original E IDs as well as the CS IDs below.

| Exported ID | Exact identifying node and domain | Reverse proof and retained data |
|---|---|---|
| E0 | Full function `H=log(t)−t+1`, t>0 | Defines the intrinsic component; retains its coordinate. |
| E1 / CS01 | Twice differentiable H, `H''=−1/t²`, `H(1)=H'(1)=0` | Integrate twice. Without the two affine identifiers the family is `log(t)+At+B`. |
| E2 / CS01 | Twice differentiable H, `H''=−(H'+1)²`, `H(1)=H'(1)=0` | Set q=H'+1; the calibrated solution of q'=−q² is 1/t. Equivalent exact flow: `q(t+s)=q(t)/(1+s q(t))` wherever both t and t+s are positive, with q(1)=1 and H(1)=0. Taking t=1 in the full flow already identifies q directly. |
| E3 / CS02 | Differentiable H on the full positive ray, `H(av)−H(a)−aH'(a)(v−1)=H(v)` for every a,v>0, and H''(1)=−1 | Both affine anchors follow from the equation. A second derivative only at 1 propagates everywhere; prior C² regularity is unnecessary. |
| E4 / CS02 | `h(x star y)=h(x)+h(y)−xy`, x,y>−1, and h differentiable at 0 with h'(0)=0 | The identity propagates differentiability at 0 to every point and gives `(1+x)h'(x)=−x`; h(0)=0 is automatic. |
| E5 / CS12 | h differentiable on D=(−1,infinity), `h'(D) subset D`, `ell=id+h`, `ell(h'(z))=−ell(z)`, and either h(0)=0 or h'(0)=0 | Domain condition gives ell'>0 and injectivity. Full unanchored family is `h_K(z)=K log(1+z)−z−(K/2)log K`, K>0. Either anchor selects K=1. |
| E6 / CS03 | Actual Bregman divergence of differentiable Phi is invariant under simultaneous positive scaling; two affine anchors and one scale calibration | Necessarily `Phi=A I+affine`. Thus separate C²/strict-convexity assumptions are redundant. One usable scale mark is `Phi'(2)−Phi'(1)=1/2`; the old `Phi''(1)=1` is equivalent once the shape is derived. |
| E7 | p solves p''+2p'+p=0 on t>0, extends continuously to 0 with p(0)=0, and has integral 1 | General solution `(A+Bt)e^(−t)`; endpoint fixes A and mass fixes B. Equivalent causal distributional Green equation `(D+1)²g=delta_0`, support in [0,infinity), and convolution of two causal `e^(−t)` kernels. |
| E8 | Positive probability measure on (0,infinity) satisfying every compact smooth Stein test, or normalized density satisfying `(tp)'=(2−t)p` | Distributional integrating factor identifies a constant multiple of `t e^(−t)`; mass fixes it. The strengthened measure-on-R theorem requires tests on all of R, as in Phase III III.1. Tests only inside (0,infinity) cannot see an atom at 0 or mass on the negative ray. |
| E9 | Probability on [0,infinity) with full Laplace transform `(1+s)^(−2)`, s>=0 | Laplace uniqueness. Densities are identified a.e. before choosing their continuous representative. |
| E10 | Finite positive Borel measure on R with every moment `(n+1)!`, n>=0 | The n=0 equation supplies mass; positivity plus the even moments gives an exponential moment and MGF uniqueness. Positive support is derived. Detailed proof is also independently recorded in probability.md. |
| E11 | Probability on (0,infinity) with `E T^(i xi)=Gamma(2+i xi)` for every real xi | Characteristic-function uniqueness for log T. Equivalently the Mellin function `integral t^(s−1)p(t)dt=Gamma(s+1)`, Re s>−1. The determining line is s=1+i xi. |
| E12 / CS03 | Full extended-real conjugate C(theta)=−log(1−theta) below 1, infinity otherwise; candidate F is either lsc on the positive ray or convex | Either candidate class alone yields F=I extended by infinity off the positive ray. Properness and the other regularity properties are conclusions. |
| E13 | Actual hazard `x/(1+x)` of an absolutely continuous probability on the nonnegative ray, positive survival at finite x, S(0)=1 | `S'/S=−x/(1+x)` integrates to `S=(1+x)e^(−x)`, and p=−S'. If a hazard equation is imposed only a.e., local absolute continuity of S must be retained; a derivative a.e. does not by itself exclude a singular survival component. |
| E14 / CS13 | Injective f=H' on t>0 preserving every cross-ratio, f(1)=0, f(2)=−1/2, f(3)=−2/3, H(1)=0 | Comparison with the fractional-linear map 1/t−1 using three fixed arguments identifies f everywhere, and the primitive anchor identifies H. |

These are calibrated complete statements, not interchangeable names for subjects. The old manuscript's global C² convention and explicit E5 injectivity and E6 strict convexity are sufficient but not minimal. Their removal is valid under the exact replacement conditions above.

## CS01–CS02: curvature, recentering, group logarithm and cocycle

For curvature, subtract log t and apply twice the fact that a differentiable function with zero derivative on an interval is constant. For Riccati, uniqueness of the first-order equation with initial value q(1)=1 gives q=1/t throughout the connected domain; no intervening pole is admissible. The known solution exists on the whole positive ray. Calibrated exact-flow data give the same result without first assuming an ODE: put t=1 and s=v−1.

For tangent-subtracted recentering, v=1 gives H(1)=0. Differentiating with respect to v at 1 gives H'(1)=0. Differentiating once at arbitrary v gives

`a[H'(av)−H'(a)]=H'(v)`.

The existence of H''(1) now implies the existence of H''(a), by the difference quotient at v=1, and `a²H''(a)=H''(1)`. Thus H''(1)=−1 recovers E1. Without the scale mark the exact family is `cH`; no extra affine anchors are missing.

On D=(−1,infinity), `x star y=x+y+xy` is a commutative group because `1+(x star y)=(1+x)(1+y)>0`. Its identity is 0 and inverse is `−x/(1+x)`. The continuous logarithms are `ell(x)=c log(1+x)`. The cocycle equation is precisely the assertion that `ell=h+id` is such a logarithm. Even differentiability merely at 0 propagates: write

`h(x+(1+x)y)−h(x)=h(y)−xy`

and divide by `(1+x)y` as y tends to 0. Consequently `(1+x)h'(x)=h'(0)−x`, and the calibrated solution is unique. Without the slope calibration the differentiable family is `c log(1+x)−x`. Without any regularity the family is `A(log(1+x))−x` with A additive; value normalization at 0 does not remove this freedom.

The cocycle `−xy` satisfies `c(x,y)+c(x star y,z)=c(y,z)+c(x,y star z)` by expansion. Its group quotient and tangent-subtracted recentering presentations add no independent data.

## CS03: Bregman and exact Legendre converse

Direct substitution gives `B_I(t,s)=I(t/s)`. For a differentiable candidate Phi, simultaneous scale invariance implies, by differentiating only the first variable,

`c[Phi'(ct)−Phi'(c)]=Phi'(t)−Phi'(1)`.

Set g(t)=Phi'(t)−Phi'(1), swap c and t, and subtract to obtain

`g(c)(1−1/t)=g(t)(1−1/c)`.

Fix any c other than 1. This forces `g(t)=A(1−1/t)`, including at t=1. Integration proves `Phi=A I+Phi'(1)(t−1)+Phi(1)`. A curvature or nonzero derivative-difference calibration fixes A=1; two affine marks then give Phi=I. Convexity and smoothness are consequences. The affine and scale freedom explicitly tests all three independent normalizations in this candidate family.

For the symmetric anchored data, the actual Bregman expression is

`B_Phi(t,1)+B_Phi(1,t)=(t−1)(Phi'(t)−Phi'(1))`.

Equality with `t+t^(−1)−2` gives the same calibrated derivative for t≠1 and then everywhere. Only differentiability and two affine anchors are needed. Reciprocal values alone do not substitute for Bregman data: `Phi(t)=(t+t^(−1))/2−1` has `Phi(t)+Phi(1/t)=t+t^(−1)−2`, and matches value, slope and curvature at 1, but is not I. A one-sided anchored identity `Phi(t)−Phi(1)−s(t−1)=I(t)` is even more direct and needs only that finite support slope s to be specified, not a pre-existing global smoothness assumption.

For the Legendre statement extend I by infinity to t<=0. Maximization gives

`I*(theta)=−log(1−theta)` for theta<1, and infinity for theta>=1.

Conversely suppose F*=C, with extended-real F on R. Fenchel's inequality gives F>=C*=I, and finiteness of C excludes negative-infinity values of F and ensures a nonempty effective domain. For t0>0 choose theta0=1−1/t0. The function

`I(t)−theta0 t=(1−theta0)t−1−log t`

is coercive at both positive endpoints and has unique minimizer t0. A maximizing sequence for the definition of F*(theta0), compared with this lower envelope, must converge to t0. Its F-values converge to I(t0). Lower semicontinuity of F at t0 therefore gives F(t0)<=I(t0), hence equality. Only lsc at the positive points is needed because F>=I already gives F=infinity elsewhere.

Alternatively, if F is convex, the same optimizing sequences make its effective domain dense in the positive ray. A convex dense subset of that interval contains it: bracket any point with two domain points. F is consequently finite and continuous there, so the preceding argument applies. Convexity alone is sufficient; lower semicontinuity alone is sufficient. These are two sufficient classes with explicit omission tests, not an assertion of an absolute weakest class.

If neither regularity alternative is imposed, raise I by 1 at a single positive point and leave it unchanged elsewhere. The conjugate stays C because nearby points approximate the removed optimizer. The modified function is neither convex nor lsc. Thus the unrestricted converse is false, but the old requirement to assume both closedness and convexity is unnecessary for this exact target.

## CS04: self-concordance and three distinct automorphism questions

`I''=t^(−2)` and `I'''=−2t^(−3)` prove standard self-concordance with equality. For a C³ candidate with positive second derivative, signed equality plus `Phi''(1)=1` gives `((Phi'')^(−1/2))'=1`, hence Phi''=t^(−2); two affine anchors recover I. The unsigned equality also suffices on the entire positive ray: the continuous nonzero third derivative has constant sign. The opposite sign would give `(Phi'')^(−1/2)=2−t`, impossible for all t>0. On (0,2), the different potential `−log(2−t)−(t−1)` shows why that global domain or an orientation mark matters. The inequality alone fails to identify I, as cI for c>=1 shows.

I is not a finite-parameter self-concordant barrier on the entire positive ray because `(I')²/I''=(t−1)²` is unbounded. Its affine-equivalent logarithmic part −log t has parameter 1. Phase III's distinction is correct.

The metric `dt²/t²` becomes Euclidean under log t; its distance is `|log(t/s)|`. Its global isometries are t↦a t and t↦a/t, a>0. Marking 1 leaves identity and inversion; adding orientation to that mark leaves identity. Joint automorphisms of the directed divergence `I(t/s)` are just dilations. To see the distinction without relying on classification, inversion replaces the ratio by its reciprocal and `I(r)` is not `I(1/r)`. The symmetric identity is correctly `B_I(t,s)+B_I(s,t)=4sinh²(|log(t/s)|/2)`.

The actual group automorphisms form a different family. Every continuous, measurable, monotone, or differentiable global automorphism of the fixed star law is

`F_c(x)=(1+x)^c−1`, c in R and c≠0.

Conjugate by log(1+x) and exp−1 to obtain an additive regular bijection of R, hence multiplication by c. Without regularity an arbitrary additive bijection gives a possibly discontinuous group automorphism. Calibration F'(0)=1 forces c=1. Formal automorphisms over a characteristic-zero field have the same formula, with c a nonzero field element: the formal logarithm reduces them to additive formal series, whose higher coefficients vanish. An arbitrary invertible formal change `f=x+O(x²)` transports the group law to another presentation and need not preserve this fixed law.

The integer n-series is `[n]_star(x)=(1+x)^n−1`: repeated **group addition** for n>=0 and the group inverse for n<0. Phase III's phrase “repeated composition” should be read/replaced this way; ordinary function composition satisfies `[m]_star compose [n]_star=[mn]_star`, not `[m+n]_star`.

## CS05 and CS14: derivative reconstruction, continuation, and exact-zero counterexample

On a connected interval r>b, `F''=−(r−b)^(−2)` gives exactly `F=log(r−b)+Ar+B`. Thus all higher derivative identities add nothing once n=2 is supplied, and two affine data remain necessary. A lone n-th derivative identifies only modulo a polynomial of degree at most n−1. The placement-recovery formulas and finite-difference formula in Phase III III.4 are correct inside their declared family; they do not identify arbitrary candidates from a finite jet or discrete samples. A periodic perturbation preserves all integer samples, while a smooth bump away from the observation point preserves its complete jet.

Inside `rho(r)=C(1+gamma r)e^(−mu r)`, the formula for rho^(n) and its zero `r_n=−1/gamma+n/mu` is correct. Two consecutive indexed zeros determine mu and gamma, and mass determines C. That family hypothesis cannot be replaced by smooth positive normalization, even when the complete exact zero set of every derivative is supplied.

**CS14 — counterexample, universal n proof.** For any real k>1 set

`f_k(t)=(k−1)k^k t/(t+k)^(k+1)`, t>0.

Its integral is 1: substitution t=ks gives

`integral f_k = k(k−1) integral_0^infinity s/(1+s)^(k+1) ds = 1`.

The last integral equals `1/[k(k−1)]`, either by subtracting two elementary power integrals or by the beta integral. The function is strictly positive and real analytic on the positive ray, and tends to zero at both endpoints. Write C=(k−1)k^k. Then

`f_k=C[(t+k)^(−k)−k(t+k)^(−k−1)]`.

For every integer n>=0,

`f_k^(n)(t)=C(−1)^n (k)_n (t−n)/(t+k)^(k+n+1)`.

Here `(k)_n` is the rising factorial, with `(k)_0=1`. Differentiating the fraction multiplies it by −(k+n) and replaces `(t−n)/(t+k)^(k+n+1)` by `(t−n−1)/(t+k)^(k+n+2)`, proving the formula inductively. For n>=1 every non-linear prefactor is nonzero and the denominator is positive, so the exact positive zero set is the singleton `{n}`, with a simple zero and the same sign pattern as the n-th derivative of p. This retains all zero interlacing and endpoint vanishing.

The simplest counterexample is `f_2(t)=4t/(t+2)^3`; it has unit mass and

`f_2^(n)(t)=(−1)^(n−1)8(3)_(n−1)(n−t)/(t+2)^(n+3)`, n>=1.

Its algebraic tail distinguishes it from p. For finite k, f_k is not entire: it has a singularity at −k. It is not globally log-concave because

`(log f_k)''=−1/t²+(k+1)/(t+k)² > 0` exactly when `t>1+sqrt(k+1)`.

No claim is made that this counterexample preserves a separately supplied exponential tail, global log-concavity, maximum height, or complete moments. None is an assumption of Phase III's stated open class. Therefore replace the **?** at III.4, IV.3 and the corresponding coverage/graph discussion by **refuted** for that exact candidate class. Reimposing one of those extra constraints would define a different question and is not needed for this closure.

For continuation, the complete germ or Taylor sequence identifies an arbitrary global candidate only in a declared uniqueness category, such as real analytic functions on the same connected positive ray. Alternatively the exact recovered expression may be used to **construct** its canonical global representative. Formal equivalence does not select an arbitrary smooth global extension. The bump examples in IV.8 are valid; sufficiently small compactly supported perturbations preserve strict convexity because I'' has a positive minimum on that compact support. Even positivity and probability normalization do not replace the analytic category, as the zero-integral bump example in probability.md demonstrates.

## CS06–CS09: complete scalar-series closure

Work over a characteristic-zero field as Phase III specifies; a commutative rational algebra also suffices for these identities. The variable u is marked and `Q(0)=1`. Expressions such as `u/(1−exp(−u))` mean the inverse of the normalized unit `(1−exp(−u))/u`, not inversion of a nonunit series.

**CS06.** Write `Q=1+sum_(j>=1) q_j u^j`. Its degree-n equation is

`[u^n]Q^(n+1)=(n+1)q_n+P_n(q_1,...,q_(n−1))=1`.

Since n+1 is invertible, coefficient induction proves uniqueness. Existence is proved by the exact residue calculation below with k=0. If degree N is omitted, choose q_N freely and recursively satisfy every later condition. Thus every degree is necessary within this particular triangular data set; finite truncations leave the tail free. If q_0 is merely invertible but not specified as 1, a free parameter remains, and the recursion divides instead by `(n+1)q_0^n`. The degree-0 equation, if included, fixes q_0.

**CS07.** Put `z=1−exp(−u)`, a formal compositional coordinate with linear term u; its inverse is u=−log(1−z). Then

`[u^n]exp(k u) QT(u)^(n+1)`

`= Res [ exp(k u)/(1−exp(−u))^(n+1) ] du`

`= Res z^(−n−1)(1−z)^(−k−1) dz`

`= binomial(n+k,n)`.

This holds for every n>=0 and as a polynomial identity in k over Q, so in particular for all integers k, including negative ones. Phase III's integer-k claim passes and its stronger polynomial form is immediate. The k=0 slice uniquely characterizes QT; all other twists follow, without any topological/index hypothesis.

For clarity, arbitrary exponent coefficients are a separate question. One universally valid finite formula is

`[u^n]QT(u)^k = sum_(sum j m_j=n) (k)_[M] product_(j=1..n) (q_j^(m_j)/m_j!)`, where `M=sum m_j` and `(k)_[M]` is the falling factorial.

For positive integers k>n, Lagrange inversion gives the alternative `c(k,k−n)(k−n−1)!/(k−1)!`, using unsigned Stirling numbers of the first kind. Neither alternative is needed for the full twist theorem above.

**CS08.** The identities

`QT=exp(u/2) QA`, `QL=QT(2u)−u`, `QT=QL(u/2)+u/2`

hold by substitution into the standard definitions. Moreover `(QL+u)/(QL−u)=exp(2u)`, with unit denominator. Starting from the complete standard QA, put `b=u/QA`; the unique square root of b²+4 with constant term 2 gives `w=(b+sqrt(b²+4))/2`, w(0)=1, and `w−w^(−1)=b`. Since `b=2sinh(u/2)`, the unique unit root is w=exp(u/2), hence QT=w QA. These are genuine reversible maps on the indicated exact scalar nodes. Feeding an arbitrary even unit into the algebraic square-root construction does not prove it was the standard QA; it just constructs a series with prescribed odd part.

The corresponding real formulas extend through u=0 by value 1 and hold for every real u. QA is positive there, so the selected real square root is `2cosh(u/2)>0`. QT and QA have their nearest nonremovable complex poles at ±2pi i, and QL at ±pi i; consequently their Taylor discs alone do not cover the real line. Their explicit formulas provide the claimed real analytic continuation. Formal equality plus arbitrary smooth continuation is a different, false, converse.

**CS09.** For a fixed marked scalar y, `Q_y(u)=QT((1+y)u)−yu`. If y≠−1 in the stated field,

`QT(v)=Q_y(v/(1+y))+yv/(1+y)`.

Thus y=0 gives Todd and y=1 gives L; y=−1 gives exactly 1+u and discards all higher coefficients. Over a general ring one must require 1+y to be invertible, not merely nonzero. Over Q[y] the inverse belongs to the localization at 1+y. The source uses a field, so its y≠−1 condition is already sufficient. Multiplicative inversion of normalized units is involutive and loses no universal scalar information.

## CS10–CS11: universal Thom correction and topological countermodels

The scalar Euler-coordinate formula passes: if `z=x/(1+x)`, then `z(x star y)=z(x)+z(y)−z(x)z(y)`. Interpreting x as `[L]−1` and z as `1−[L*]` is an additional map into actual K-theory; the scalar equation alone does not create a bundle or base space.

Under the supplied complex K-theory and ordinary-cohomology Thom isomorphisms, standard Chern character with ch(L)=exp(u), and compatible orientations, there is a unique correction class C(V) satisfying

`ch(U_K(V))=pi* C(V) U_H(V)`.

Naturality supplies a compatible universal line correction. Zero-section restriction gives `u C(u)=1−exp(−u)` because the K Euler class is `1−[L*]` and the cohomological Euler class is u. In the compatible inverse limit Q[[u]], multiplication by u is injective. Therefore C=QT^(-1). Multiplicativity of Thom classes/Chern character plus injective splitting gives `C(V)=product_i QT(u_i)^(-1)=Td(V)^(-1)`. Supplied collapse/Gysin constructions transport this Thom comparison to Riemann–Roch. This is a conditional topological theorem with a derived correction; it is not a scalar construction of the imported foundations.

The converse from the **full universal line series** is immediate inversion. On one finite base, u is generally nilpotent and may be a zero divisor, so zero-section cancellation there is invalid. Even a complete Thom class on that base sees only finitely many universal coefficients; no single finite-base identity or index number identifies the universal tail. Phase III states this boundary correctly.

The rational torsion countermodel is valid. On RP², the complexification L of the tautological real line has nonzero c1 in H²(RP²;Z)=Z/2 and `ch(L)=1` rationally. Its K-class differs from the trivial line: any stable trivialization would trivialize its determinant and therefore L itself. One can also see nontriviality without presuming the c1 calculation: a nowhere-zero section of L would give an odd map S²→C\{0}, hence an odd map S²→S¹. Lift its angle to R using simple connectivity of S². The difference of the angles at antipodal points is a continuous odd multiple of pi and hence constant, while swapping the points reverses it, a contradiction. L tensor L is trivial, in agreement with order-two torsion. Thus scalar series and rational characteristic images cannot recover integral bundle/K data even when the base is already fixed.

## CS12–CS13: completion and calibrated projectivity

For E5, put q=h' and ell=id+h. The typed condition q(D) subset D gives `ell'=1+q>0`; the mean value theorem makes ell strictly increasing and its inverse on its range continuous. From `ell(q)=−ell` obtain `q=ell^(-1)(−ell)`, so q is continuous. The inverse derivative theorem now applies because ell'>0, and q is C¹. Applying the completion equation twice and using injectivity gives q(q(z))=z. Differentiate to get

`(1+z)q'(z)=−(1+q(z))`.

Therefore `(1+z)(1+q(z))=K>0`; integration gives `h=Klog(1+z)−z+C`. Substitution back into the original equation gives `2C=−Klog K`. Conversely every resulting h_K has the typed derivative range and satisfies the equation. Its two possible normalizations are `h_K(0)=−(K/2)log K` and `h_K'(0)=K−1`; either vanishes exactly when K=1. The earlier manuscript's injectivity is redundant under the derivative-domain condition, and that condition must remain explicit. This independently validates the reduction in the prior audit and Phase III's inventory.

For E14 use the stated cross-ratio convention `(x1−x3)(x2−x4)/((x1−x4)(x2−x3))`. For three distinct fixed arguments it is an injective fractional-linear function of the fourth. Comparing the tuples (1,2;3,t) for f and the known map m(t)=1/t−1 forces f(t)=m(t) away from the three marks; calibration supplies the remaining points. No analytic continuation or extra continuity assumption is needed for this exact global cross-ratio identity. The no-pole condition is embodied by a real-valued map on all t>0. Two marks leave a projective family; an additive primitive anchor is still separate.

The manuscript's zero-Schwarzian version uses **jet marks**, not the three value marks above: `f=H' in C³`, f' nowhere zero, `Sf=f'''/f'−(3/2)(f''/f')²=0`, `f(1)=0`, `f'(1)=−1`, `f''(1)=2`, and H(1)=0. Set w=f''/f'. Then w'=w²/2 and w(1)=−2, so w=−2/t; integrating successively gives f'=−1/t² and f=1/t−1, then H. This is a valid alternative calibrated node. A zero Schwarzian by itself merely characterizes a fractional-linear family, and does not select Sigma. If three value marks are used instead, the global fractional-linear classification yields the same result; do not silently replace one calibration set by an incomplete subset of the other.

## Formalization practicality and evidence boundary

| Exports | Practical Lean scope | What must not be advertised as already checked |
|---|---|---|
| E1–E6, CS01–CS04, CS12 | Real derivatives, algebraic identities and MVT uniqueness are practical with explicit domain and differentiability hypotheses. E5 needs the inverse-function theorem or a direct monotone inverse argument. | Full converse coverage is not implied by existing forward identity lemmas. |
| E7–E11, E13 | ODE identities and finite recurrences are short; transform, measure and distributional uniqueness need their actual analytic foundations. | A named transform-uniqueness axiom is a conditional import, not a new machine proof of that theorem. |
| E12 | Exact scalar maximization and the optimizing-sequence proof are feasible, with extended-real order, coercivity and 1D convex continuity infrastructure. | Biconjugation under both closedness and convexity does not certify the stronger lsc-only theorem. |
| E14, CS13 | Cross-ratio comparison is rational algebra plus integration. Schwarzian needs a nonvanishing derivative and ODE uniqueness. | Checking one Möbius formula does not classify every candidate. |
| CS06–CS09 | Coefficient induction and the algebraic inverse identities are practical once formal exponentials/logarithms and square-root uniqueness are available. | Finite coefficient checks do not prove the entire tower; formal residue change of variables is a substantive imported/proved lemma. |
| CS10–CS11 | Universal scalar cancellation and multiplicative splitting calculations are practical. | Topological Thom, splitting, K-theory and torsion claims are conditional on their topology libraries/foundations, not supplied by scalar Lean arithmetic. |
| CS14 | The explicit k=2 rational countermodel's derivative induction, positivity and elementary integral are tractable. | A few derivative orders do not certify all exact zero sets. The displayed induction is the universal proof. |

No new Lean theorem is claimed by this audit file. Its exported statements are written mathematical proofs with explicit dependencies. The reproducible symbolic diagnostics in [core-series-checks.py](phase-iv-audit/core-series-checks.py), recorded in [core-series-checks.json](phase-iv-audit/core-series-checks.json), check the Todd twists through n=6, the T/A/L identities through degree 7, the rational counterexample's exact mass, and its derivative formula through order 12. All pass. They remain finite checks; the universal arguments are the proofs above.



# Appendix B. Probability proofs

# Phase IV independent probability and transform audit

The statement-only derivations were recorded in [probability-blind.md](phase-iv-audit/probability-blind.md) **before** opening the Phase III report. This comparison then read Phase III §§I.3–I.7, II.3, III.3, III.12 and IV.3–IV.6, and checked the older dependency ledger, sixteen-branch audit and manuscript for prior coverage. No global report was edited. All claims below refer to the marked intrinsic functions `I(t)=t−1−log t` and `p(t)=t exp(−t)`, t>0; placement parameters are outside this audit.

Verdict symbols: **⇔** means the exact node identifies the stated target within its candidate class; **⇒** is a valid forward implication; **+H** indicates an essential retained hypothesis or an ambiguous sentence needing qualification; **×** is a refuted converse. “Old,” “strengthened,” and “new” describe novelty within this workspace's sequence of audits, not mathematical priority in the literature.

## Decision table

| Claim | Verdict after independent derivation | Classification relative to the prior audit |
|---|---|---|
| Positive measure on R, moments `(n+1)!` including n=0 | **⇔** Gamma(2,1); mass and support derived | **Strengthened in Phase III**: earlier E10 assumed a nonnegative probability law |
| Probability recurrence `(n+1)π_(n+1)=π_n` | **⇔** Poisson(1) | **New reduced identifier in Phase III**; basic Poisson/CGF correspondence already old |
| Full marked centered CGF or oriented KL slice → I | **⇔** as scalar-function reconstruction | **Old identity/reconstruction**, made explicit; **△** centering cannot recover an unmarked original location |
| Two exact marked max laws plus `F(0)=e^(−1)` | **⇔** standard Gumbel CDF, no smoothness premise | **Strengthened in Phase III** over the old full smooth density/Haar node |
| Linked deficit law plus exact coordinate involution | **⇔** continuous strict-branch potential J | **New joint converse in Phase III**; both separate forward nodes were old |
| All deficit cumulants replace its law | **⇔** for the deficit law; no candidate MGF premise needed | **Strengthened in Phase III**; displayed cumulant values were old |
| Reverse size bias, equilibrium, marked tilt | **⇔** with the stated boundary/parameter data | Size-biased exponential was **old**; explicit equilibrium/tilt inverses are **new immediate refinements in Phase III** |
| Gamma Lévy density plus zero drift in probability category | **⇔** Gamma subordinator law | **Old exact Lévy node**, with alternatives for identifying drift clarified in Phase III |
| Explicit Gamma self-decomposition | **⇒** compound-Poisson residual formula | **New immediate refinement in Phase III**; generic self-decomposability does not identify Gamma |
| Bernstein function from all integer samples | **⇔**; proof is correct | **New converse in Phase III**; **strengthened here to any complete integer tail** |
| Marked rooted/Borel coefficients → inverse germ | **⇔**; global p needs an analytic continuation category or a selected canonical extension | **Old** inverse; retain its domain and scaling conditions |
| Arbitrary tree law from Borel total size | **×**; deterministic path countermodel | **Old identification boundary**, explicit in Phase III |
| One-ancestor iid GW law with Borel(1) total size | **⇔** Poisson(1) offspring/tree law | **New explicit reverse refinement in Phase III** of the old branching construction |

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

**Repair to I.5, line 147.** The sentence “Conversely the complete CGF near zero determines the law and recurrence by MGF uniqueness” should distinguish uncentered K from centered Λ. MGF uniqueness determines the random variable whose CGF was actually supplied. For `N_k=Y+k`, `Y~Pois(1)`, k≥1,

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

**Phase III statement: ⇔.** Every Bernstein function is determined by its values at all integers n≥0. Its representation is

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

**Exact global formulation.** If a candidate p is real analytic on the connected interval (0,∞) and agrees with this inverse germ for small positive t, then analytic uniqueness forces p(t)=t exp(−t) throughout the interval. Equivalently one may **construct** the canonical global representative using that symbolic formula. These are distinct formulations; a formal germ does not identify every smooth global extension. Phase III explicitly speaks of the canonical analytic representative and warns about smooth extensions in its scope, so the qualified theorem passes. Any compressed diagram claiming an unqualified germ-to-arbitrary-global-function equivalence must retain this condition.

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

The simplest example is `f_2(t)=4t/(t+2)^3`, which has an algebraic tail and differs from `t e^(−t)`. Consequently the exact-all-zero-sets smooth positive probability converse left **?** in Phase III III.4/IV.3 is **×**. This counterexample retains normalization, positivity, analyticity, endpoint vanishing and the complete zero sets, not merely selected incidences. It does not claim to retain a separately imposed height `f(1)=e^(−1)` or exponential-tail condition. Those were not assumptions of the stated unresolved class.



# Appendix C. Operator and spectral proofs

# Phase IV operator/spectral audit

## Scope and verdict

The independent derivation was saved in [operator-blind.md](phase-iv-audit/operator-blind.md) before opening Phase III or earlier operator audits. The subsequent comparison used Phase III I.6–I.7, III.1–III.3, IV.4, V.1–V.4, plus `work/audit-v2/operator-derivation.md`, `operator-statements-blind.md`, `operator-blind-review.md`, and `operator-converse-addendum.md`.

**Mathematical verdict:** the substantive Stein, local-operator, endpoint, spectral, kernel, determinant, and Hausdorff claims pass. The Bernstein integer-sampling converse also passes. Phase III already avoids the zero-mode ambiguity noted in the blind audit: its actual definition is the shifted ordinary trace `Z_A(s)=Tr(1+A)^(-s)`, not an unqualified trace of `A^(-s)`.

**Required correction:** the compressed graph must distinguish canonical construction from identification of the source object. The path `marked A → spectrum → fixed J completion → intrinsic S` reconstructs the canonical Gamma(2) mixing law. It is not a reverse reconstruction of an arbitrary stationary coordinate law. I.7 says this correctly in prose, but a plain SCC computation on V.4 merges the bare spectral/unitary nodes with the intrinsic component and erases this distinction. Retain the recipe/category in the node, or keep construction arrows out of the graph used to assert mutual identification.

Two smaller precision edits are advisable: explicitly require the relevant finite trace data in the general compact-resolvent inverse theorem; and explicitly distinguish polynomial identities of differential expressions from membership in the compactly supported minimal domain. These qualifications do not affect the canonical Laguerre conclusions.

## 1. Exact intrinsic and local characterizations

### 1.1 Full-line weak Stein characterization — PASS

For a finite positive Borel measure P on R, the hypotheses
\[
P(\mathbb R)=1,\qquad
\int[t f'(t)+(2-t)f(t)]P(dt)=0
\quad(f\in C_c^\infty(\mathbb R))
\]
are equivalent to `P(dt)=1_{t>0}te^{-t}dt`. The candidate measure needs no prescribed density, positive support, or moments.

The distributional equation is `(tP)'=(2-t)P`. On any interval avoiding zero, division by t and a smooth integrating factor show that the measure is absolutely continuous. The positive and negative half-line solutions are respectively `C_+ t e^{-t}dt` and `C_- |t|e^{-t}dt`, with nonnegative constants. Finite mass eliminates C_-. The remaining possible singular part is mδ_0. Since the positive solution has `t p(t)→0` at zero, its distributional flux supplies no delta there; substituting the atom produces `0=2mδ_0`. Thus m=0 and normalization fixes C_+=1. Integration by parts proves the reverse implication.

The earlier audit's nonunique kernels `τ=t+Ce^t/t` concern a different inverse problem: P is already fixed and τ is unknown. They do not contradict this theorem, in which τ=t and the drift normalization are fixed while P is unknown. Tests supported only inside (0,∞) would not identify a full-line probability; the full-line test class is essential to the support conclusion.

### 1.2 Two polynomial probes — PASS in the stated category

In the fixed coordinate t∈(0,∞), let `Bf=-a(t)f''-b(t)f'` be a conservative local second-order expression. If
\[
B(2-t)=2-t,
\qquad B(t^2/2-3t+3)=t^2-6t+6,
\]
then the first equation gives b=2-t and the second gives
`-a-(2-t)(t-3)=t²-6t+6`, hence a=t. This is pointwise if the coefficients and equations are pointwise, and almost everywhere if their meaning is almost everywhere. The two polynomials are formal probes of the expression or elements of an explicitly enlarged domain; neither belongs to C_c^∞(0,∞).

The pair is irredundant within this coefficient class. Omitting the quadratic probe leaves a arbitrary positive. Omitting the linear probe permits, for small ε and compactly supported smooth k,
`b=2-t+εk`, `a=t-εk(t-3)>0`.
Both displayed counterfamilies are valid. Outside the local expression category, a unitary rotation of the third and fourth Laguerre modes, fixing modes 0,1,2, changes the operator while retaining the two probes and the constant vector. This last example is a countermodel in the self-adjoint operator category; positivity preservation of its semigroup is not asserted.

Recovering the differential expression does not itself choose an unspecified Hilbert realization. With the normalized zero-current Pearson measure or the explicitly prescribed canonical realization, the invariant density is the Gamma density, and the unique closure below follows. Phase III III.1 retains this qualification correctly.

## 2. Essential self-adjointness and the full spectral theorem — PASS

Write `w(t)=te^{-t}`, `q(t)=t²e^{-t}`. On `H=L²((0,∞),w dt)`, the symmetric nonnegative minimal operator is
\[
A_0f=-w^{-1}(qf')',\qquad D(A_0)=C_c^\infty(0,\infty).
\]
The zero-energy solutions are `1` and `u(t)=∫_1^t e^s/s² ds`. Their asymptotics are
\[
u(t)=-t^{-1}+\log t+O(1)\quad(t\downarrow0),
\qquad u(t)\sim e^t/t^2\quad(t\to\infty).
\]
Consequently `|u|²w∼1/t` at zero and `|u|²w∼e^t/t³` at infinity, neither integrable. The constant is square integrable at both ends. The Weyl alternative makes both endpoints limit point; the deficiency indices are (0,0). Thus `A=closure(A_0)=A_0*` is the unique self-adjoint realization. The origin is the critical, logarithmically divergent limit-point case. The endpoint criterion is the standard result in [Gesztesy–Littlejohn–Nichols, Section 3](https://arxiv.org/html/1910.13117v2#S3); the asymptotic computations here are independent.

The exact domain is
\[
D(A)=\{f\in H:f,qf'\in AC_{\rm loc}(0,\infty),\ -w^{-1}(qf')'\in H\}.
\]
No boundary condition is additionally selected. To see automatic zero flux directly, put h=Af. Then `(qf')'=-wh`, and wh is integrable globally by Cauchy–Schwarz. Each endpoint flux has a finite limit. A nonzero limit forces the excluded `1/t` or `e^t/t²` behavior and contradicts f∈H. Both flux limits therefore vanish. A finite value f(0) is not required.

Rodrigues orthogonality gives
`∫L_n^(1)L_m^(1)w dt=(n+1)δ_nm`, while the differential equation gives `AL_n^(1)=nL_n^(1)`. These polynomials lie in the maximal domain. For completeness, if f∈H is orthogonal to all polynomials, `F(z)=∫f(t)w(t)e^{zt}dt` is analytic for Re z<1/2. All derivatives at zero vanish; hence F=0 throughout that half-plane. Fourier uniqueness for the finite complex measure `fw dt` yields f=0. Therefore
\[
e_n=L_n^{(1)}/\sqrt{n+1},\qquad Ae_n=ne_n
\]
is a complete orthonormal eigenbasis, and the spectrum is exactly the simple set N_0. The exact domains are `Σn²|c_n|²<∞` for A and `Σn|c_n|²<∞` for its form. This also validates the earlier operator audit's essential-self-adjointness and completion claims.

## 3. Complete traces identify the unitary class — PASS with explicit convergence

For the canonical A,
\[
Z_A(s)=\operatorname{Tr}(1+A)^{-s}=\zeta(s),\quad\Re s>1,
\qquad
K_A(\tau)=\operatorname{Tr}e^{-\tau A}=(1-e^{-\tau})^{-1},\quad\Re\tau>0.
\]
These are the exact ordinary trace-class domains. Meromorphic continuation is not an ordinary operator trace. Since `(1+A)^(-s)` uses the positive real eigenvalues n+1, no logarithm branch is involved. The shifted trace includes the information about the zero eigenspace. An unshifted zeta convention would have to omit that eigenspace and separately retain its dimension, but Phase III does not make that error.

**Precise inverse statement.** Let B be nonnegative self-adjoint with compact resolvent. Assume either its heat traces are finite for all positive times, or its shifted zeta traces are finite on a right half-line. Their complete values determine its eigenvalue multiset, hence B up to unitary equivalence. In the zeta case, write `r_j=1+λ_j`. From `Z(s)=Σr_j^{-s}`, recover the least r by `lim_{s→∞}Z(s)^(-1/s)` and its multiplicity by `lim r^s Z(s)`. Subtract and iterate. For heat use the corresponding large-time exponential rate and coefficient. Finiteness at one suitable time or exponent supplies a dominating summable tail for these limits.

Compact resolvent alone does not guarantee either trace hypothesis. For example the diagonal eigenvalues `λ_j=log log(j+e^e)` tend to infinity, so the resolvent is compact, but both `Σe^{-τλ_j}` and `Σ(1+λ_j)^{-s}` diverge for every positive τ,s. This is a precision qualification to Phase III III.2, not a counterexample when finite full trace data are actually supplied.

The stronger integer-data assertion also passes: if `Tr(1+B)^(-2)<∞`, let `x_j=(1+λ_j)^(-1)` and `η=Σx_j²δ_{x_j}`. It is a finite measure on [0,1], and its moments are `Z_B(k+2)`. Hausdorff uniqueness identifies η. Every nonzero atom x has mass `m x²`, so it identifies the eigenvalue x^-1−1 and integer multiplicity m. No atom at zero arises from a finite eigenvalue. This proof needs neither interpolation of ζ nor values at noninteger s.

## 4. Finite special values and determinants — PASS

For any finite modification of the eigenvalues `r_j=1+λ_j>1`, the zeta correction
\[
\Delta Z(s)=\sum_{j=1}^N(r_j^{-s}-r_{j,0}^{-s})
\]
is entire. Thus poles and residues are unchanged. Keeping a nonzero real special value at s_i fixes `Σr_j^{-s_i}`; keeping the finite part at s=1 fixes `Σr_j^{-1}`. A zeta determinant fixes `Σlog r_j`. The special value at s=0 imposes no constraint on a perturbation with the same number of eigenvalues.

After duplicate constraints are discarded, the gradients of the nonzero-real-value constraints are proportional to `r_j^{-s_i-1}`, and the determinant adds the distinct exponent r_j^-1. These rows have full rank at distinct positive r_j. An elementary proof sets u_j=log r_j: a nonzero combination of m exponentials with distinct real exponents has at most m−1 distinct zeros, by induction and Rolle's theorem after dividing by the lowest exponential. The implicit-function theorem therefore leaves a nonconstant local family when more eigenvalues than independent constraints are varied. Small perturbations retain distinctness, nonnegativity, and the fixed infinite tail. This supplies the rank argument required for the exact finite family claimed in Phase III.

A fully explicit simultaneous example replaces the three shifted eigenvalues 2,3,4 by a,b,c with
\[
a=2+\epsilon,\qquad b+c=7-\epsilon,
\qquad bc=24/(2+\epsilon).
\]
For sufficiently small nonzero ε, b,c remain positive, distinct, greater than one, and near 3,4. Their sum remains 9 and their product remains 24. Consequently Z(0), Z(-1), Z'(0), the residue at one, and the zeta determinant are all unchanged while the full spectrum changes. The zero eigenvalue and every other eigenvalue remain fixed. A single determinant has the still simpler two-eigenvalue perturbation `2→2c`, `3→3/c` used in IV.4.

This concerns the specified finite familiar invariants. It is not a claim that no specially encoded finite datum could ever contain the whole spectrum.

## 5. Kernel, resolvent, and determinant formulas — PASS

Let q=e^-τ with τ>0. Relative to `p(y)dy=ye^{-y}dy`,
\[
K_\tau(x,y)=\sum_{n\ge0}q^n\frac{L_n^{(1)}(x)L_n^{(1)}(y)}{n+1}
=\frac{e^{-q(x+y)/(1-q)}}{(1-q)\sqrt{qxy}}
I_1\!\left(\frac{2\sqrt{qxy}}{1-q}\right).
\]
This is the α=1 Hille–Hardy formula; Γ(α+1)=1 at that parameter, so there is no missing normalization factor. The kernel tends to one as τ→∞ and its integral in p(y)dy is one. The Lebesgue transition density has the additional factor p(y). [NIST DLMF 18.18.27](https://dlmf.nist.gov/18.18.E27).

For α>0 the Laplace integrals of K_τ with weights e^-ατ and τe^-ατ give the first and second resolvent kernels. Their eigenvalues are `(n+α)^-1` and `(n+α)^-2`. The first resolvent is Hilbert–Schmidt and not trace class; the second has trace ζ(2,α). For α,β>0,
\[
\operatorname{Tr}[(A+\alpha)^{-1}-(A+\beta)^{-1}]
=\psi(\beta)-\psi(\alpha).
\]
Subtracting the reciprocal series establishes the sign. A complete resolvent operator determines A on the range of that resolvent; its scalar trace does not.

The regularized determinant is
\[
\det_\zeta(A+\alpha)=\sqrt{2\pi}/\Gamma(\alpha),\quad\alpha>0,
\]
from `ζ'(0,α)=log Γ(α)−½log(2π)`. In particular `det_ζ(1+A)=det'_ζ(A)=√(2π)`, with the prime excluding the zero mode in the latter. [NIST DLMF 25.11.18](https://dlmf.nist.gov/25.11.E18).

Finally,
\[
\det(I+z(1+A)^{-2})=\prod_{k\ge1}(1+z/k^2)
=\frac{\sinh(\pi\sqrt z)}{\pi\sqrt z},
\]
\[
\det_2(I+z(1+A)^{-1})=\prod_{k\ge1}(1+z/k)e^{-z/k}
=e^{-\gamma z}/\Gamma(1+z).
\]
Both identities hold as entire functions of z. The apparent square-root choice disappears because its quotient is even. The first is the ordinary Fredholm determinant for a trace-class perturbation; the second is the Hilbert–Schmidt regularization. Their full zero multisets identify the corresponding compact-operator spectra. [NIST DLMF hyperbolic product](https://dlmf.nist.gov/4.36.E1); [NIST DLMF gamma product](https://dlmf.nist.gov/5.8.E2).

## 6. J completion: three different valid statements

### 6.1 Unknown-measure theorem — intrinsic identification when ν is the subject

Let B≥0 be self-adjoint and have a nonzero eigenvector for every n∈N_0. For a finite Borel measure ν on [0,∞), the bounded strong operator identity
\[
\int_0^\infty e^{-sB}\nu(ds)=(1+B)^{-2}
\tag{J}
\]
has the unique solution `ν(ds)=se^{-s}ds`. Finite positive measures are enough; finite signed or complex measures are also uniquely determined when the integral is defined with finite total variation.

Apply (J) to an n-eigenvector to obtain `∫e^{-ns}ν(ds)=(n+1)^-2`. The n=0 equation supplies mass one. Under y=e^-s these are every moment of a finite measure on [0,1]. Since `∫_0^1 y^n(-log y)dy=(n+1)^-2`, uniform polynomial approximation proves uniqueness and the inverse coordinate map gives ν. Existence follows from `∫_0^∞s e^{-(1+λ)s}ds=(1+λ)^-2` and functional calculus. One eigenvector per integer is enough; multiplicities and additional spectrum do not obstruct the proof.

For an initially positive finite measure on the whole real line, if all the displayed scalar integer integrals are finite and have these values, support is derived: mass on `(-∞,-ε]` would force the nth integral to grow at least exponentially, contradicting `(n+1)^-2`. This validates I.6 without requiring an integral of unbounded negative-time operators to be defined before the support proof.

Thus, if the candidate intrinsic probability itself is denoted ν in (J), this is an authentic characterization of that candidate. The identity explicitly links the candidate to the observed operator. There is no need to identify an unspecified stationary law first.

### 6.2 Canonical recipe completion — PASS as construction

The fixed scalar recipe `J(λ)=(1+λ)^-2` has Gamma(2) as a positive Laplace mixing measure for **every** nonnegative self-adjoint B. Integer spectrum proves that the restricted operator equality has no other finite nonnegative-time mixing measure. Therefore the existence assertion in I.7 is genuinely derived, and its Hausdorff uniqueness proof passes.

The exponent-two recipe is nevertheless retained structure. Replacing it by `(1+λ)^-α` gives the Gamma(α) mixing measure. Spectral data do not select α. Moreover the existence computation itself does not need spectral data; the integer spectrum supplies determinacy from the discrete observations.

I.7's assertion that the output is the canonical mixing kernel, rather than the invariant density of an unspecified realization, is mathematically correct. Its status should be written **canonical completion in the fixed J template**, with that template visible wherever its arrow is reused.

### 6.3 Stationary-coordinate reconstruction — FAIL without linkage

For each α>0 the standard Laguerre realization
\[
p_\alpha(t)=t^{\alpha-1}e^{-t}/\Gamma(\alpha),\qquad
A_\alpha=-[t\partial_t^2+(\alpha-t)\partial_t]
\]
has simple complete spectrum N_0. The cases α=2 and α=3 both have limit-point endpoints. Their heat traces, shifted zeta functions, all resolvent trace functions, and all spectral determinants agree.

Set `ν_2(ds)=se^{-s}ds`. Both pairs `(A_2,ν_2)` and `(A_3,ν_2)` satisfy (J), but their invariant coordinate laws are p_2dt and p_3dt. This countermodel survives the conjunction of **all** the abstract spectral and J data. It shows exactly what is absent: the additional statement `ν=P_stationary`, or a retained local coordinate realization forcing it.

There is even a unitary carrying 1 to 1 and intertwining A_2 with A_3, obtained by mapping their normalized Laguerre eigenbases mode by mode. It still does not carry the original multiplication coordinate to the new multiplication coordinate. An abstract operator with a distinguished constant vector is therefore insufficient. A fully marked package `(H,A,1,M_t)` does retain the coordinate law via `P(E)=⟨1,1_E(M_t)1⟩`; alternatively the prescribed local differential expression plus the normalized zero-current law suffices.

## 7. Exact SCC correction

Let F forget a stationary coordinate realization and retain only its spectrum. Let G_J construct Gamma(2) from that spectrum using the J recipe and then construct the canonical Gamma(2) Laguerre realization. Then
\[
G_J(F(p_3,A_3))=(p_2,A_2)\ne(p_3,A_3).
\]
Hence G_J is not a left inverse to F on the class of stationary realizations. A directed cycle formed by F and G_J is a cycle of computable constructions, not an equivalence of the original candidate objects.

There are two consistent graph conventions:

1. **Identification graph.** Keep only arrows proved to identify the same supplied candidate object, with every side hypothesis retained. The marked local A and its full resolvent/operator functional calculi can sit in the intrinsic component. The bare SPEC/UC node remains auxiliary; its J arrow leads to a separately named canonical mixing construction. The unknown-ν formulation (J) is a distinct intrinsic characterization node because its ν is explicitly the target law.
2. **Template graph.** Index every canonical construction by its fixed category/recipe C, for example `SPEC_J`, `MIX_J`, or `(C,A)`. Within that restricted template, one may display mutual reconstruction of the canonical objects. This is a component in the fixed C fibre. It must not be promoted to an identification theorem for arbitrary objects after forgetting C.

In particular, writing a bare `SPEC` node, an edge labelled “fixed programme J recipe,” and then an ordinary reverse arrow to the source intrinsic object hides the dependence when graph reachability is compressed. Either carry the recipe on the nodes and in the equivalence statement, or tag that edge as construction and exclude it from SCC equivalence inference. Phase III V.4 should be repaired on this point even though the qualifications in I.7 and III.2 already explain the correct mathematics.

## 8. Bernstein integer samples — PASS

For a Bernstein function with its standard representation
\[
f(\lambda)=k+d\lambda+\int_{(0,\infty)}(1-e^{-\lambda x})\Pi(dx),
\quad\int(1\wedge x)\Pi(dx)<\infty,
\]
the finite measure
\[
\rho_f=d\delta_1+(x\mapsto e^{-x})_\#[(1-e^{-x})\Pi(dx)]
\]
on [0,1] has moments `f(n+1)-f(n)`. Its finiteness follows from the Lévy integrability condition. Thus all samples f(n), n≥0, determine ρ_f by Hausdorff uniqueness. Its atom at one gives d, its restriction to (0,1) gives Π after undoing the change of variable and positive weight, and f(0)=k gives killing. There is no finite-x contribution at y=0 or y=1. Consequently all integer values determine f on [0,∞).

Knowing f(A) on the marked integer eigenspaces supplies exactly these samples, so Phase III III.3 is correct. Knowing a fixed strictly increasing f instead allows inversion of functional calculus to recover A from f(A); this is a different inverse question. Arbitrary smooth scalar functions admit modifications `εsin(2πλ)` invisible on N_0 and lack this uniqueness.

## Audit disposition

No formula replacement is needed in Phase III III.1–III.3 or IV.4 for the audited operator claims. Preserve the existing shifted-zeta definition, endpoint classification, determinant conventions, and stationary/mixing distinction. Make the inverse-trace convergence premises explicit, specify the probe-domain meaning, and revise the compressed graph so its claimed SCCs do not identify arbitrary coordinate realizations through a canonical J selection. The blind derivation, exact countermodels, and arguments above are the verification; no numerical diagnostic is being represented as proof of a universal theorem.



# Appendix D. Realization proofs

# Phase IV independent audit of matrix, spatial and arithmetic realizations

The statement-only proofs were saved in [realizations-blind.md](phase-iv-audit/realizations-blind.md) before opening the corresponding Phase III arguments. The earlier probability assignment had exposed probability sections and incidental search snippets; the blind file explicitly records that limited prior exposure. This comparison then read Phase III II.5, III.6, III.8–III.10 and IV.7–IV.11, together with the older sixteen-branch audit, dependency/audit ledgers and relevant manuscript sections. The Euler-product converse was encountered during comparison and checked separately below; it is not claimed as part of the original blind exercise. No global report was edited.

Symbols: **⇔** exact identifying equivalence in the stated category; **⇒** valid forward construction; **+H** essential retained datum or a statement requiring repair; **×** refuted unqualified converse. Historical labels refer to these workspace audits, not novelty in the mathematical literature.

## Findings and historical classification

| Node | Verdict | Old / strengthened / new within this workspace |
|---|---|---|
| SPD lift from rank-one I, orthogonal invariance and scalar-block recursion | **⇔**, no regularity needed | **Old**: already proved in M1 and the sixteen-branch audit |
| Canonical spectral/Gaussian construction versus identification of an arbitrary lift | **⇒** construction; **+H** identification | **Clarified in Phase III**; the counterexamples were already old |
| Hessian, Bregman divergence, congruence, precision reversal, conjugate, geodesic and distance | **⇔** with affine calibration/category | **Old formulas** in the manuscript/M1–M3; Phase III develops them correctly |
| Matrix symmetrization not determined by distance alone | **** counterexample | **Old boundary**, now given a particularly explicit equal-distance pair |
| Determinant inequalities and Wishart likelihood/transform | **⇒** with supplied Gaussian iid model and sample count | **New immediate refinements in Phase III** |
| Nonnegative orthogonal additivity implies c times squared norm without continuity | **⇔**, dimension at least two | **Old strengthened theorem** already in the sixteen-branch audit; not a new Phase III collapse |
| Orthogonal star composition implies `exp(c||x||²)−1` | **⇔** under the nonnegative logarithmic-observable condition | **Old** |
| Profile-independent radial residual and D=1 or 3 | **⇔** in the selected radial-operator category | **Old**; Phase III broadens the explicit network countermodel presentation |
| Whole scalar network identifies an arbitrary spatial observable or dimension | **×** | **Old obstruction**, tested against all proposed bridges in Phase III |
| Labelled Calkin–Wilf parent algorithm and calibrated generator reconstruction | **⇔** with full-domain extension condition | **Old**, with an explicit domain repair in Phase III |
| Nonnegative unimodular matrix words, Stern–Brocot reversal and Euclidean/CF decoding | **⇔** with root/order/numerical marks | **New immediate refinements in Phase III** |
| Bare tree determines real generator maps or I below t=1 | **×** | **Old marking boundary**, sharpened to a full-domain extension issue |
| Original integer-code collision criterion | **⇔** exact parameter criterion | **Strengthened in Phase III** beyond earlier sufficient injection tests |
| Prime/divisor/valuation/gcd/lcm/Möbius/Dirichlet transport | **⇔** inside the supplied unit-adjoined monoid | Prime transport **old**; full arithmetic inventory **new refinement in Phase III** |
| Euler product recovers its numerical generator multiset | **⇔** in the convergent positive Euler-factor category | **New conditional converse in Phase III** |
| Original code versus alternative shifted intrinsic code | **** distinction; replacement does not fix original collisions | **New explicit construction in Phase III** |
| Every original-code collision destroys multiplication | ****; proof below | **New strengthening in this audit** of the previously exhibited collision |

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

**Required trace placement correction, III.6 after (3.22).** The text writes `g_X(U,U)=tr(X^(−1/2)UX^(−1/2))^2`. Taken literally this squares the trace and is false. The correct expression is

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

**Wording repair in the last sentence of the likelihood paragraph.** Replace “the negative log likelihood difference from its maximum” by **“the excess of negative log likelihood above its minimum”**, or “the log-likelihood deficit below its maximum.” The displayed divergence has the correct orientation; only the extremum description is reversed. If C is singular, the SPD likelihood has no attained maximizer and this reference-to-C formula cannot be read with an SPD C.

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

**Continued-fraction endpoint precision.** The usual unique finite expansion `[a₀;a₁,…,a_k]` requires a_k≥2 **when k≥1**; a one-term integer expansion [a₀] permits a₀≥1. Without that exception, the report's unqualified terminal rule excludes the root 1=[1]. Run lengths also include the usual terminal-minus-one correction because the parent algorithm stops at 1/1. The report claims complete Euclidean quotient lists with conventions, not an incorrect literal equality of every run length with every digit, so this is a small domain clarification.

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



# Appendix E. Independent matrix-distance and spatial derivations

# Phase IV matrix, spatial and arithmetic audit: blind derivations

This file was written from the coordinator's statement-only task before opening the corresponding Phase III proofs. The earlier probability audit exposed probability sections and some search-result snippets from other sections; it did not expose the detailed matrix, spatial or arithmetic proofs. No independence stronger than that is claimed. The intrinsic functions are `I(t)=t−1−log t`, `H=−I`, `p(t)=t exp(−t)` in the marked t>0 coordinate.

Symbols: **** proved as precisely stated; **△** essential qualification; **×** false converse. Historical novelty and comparison are deferred until after this file is written.

## A. Canonical SPD lift

**Exact theorem.** For each positive integer n, let Φ_n be a real-valued function on the real symmetric positive-definite n×n matrices. Suppose Φ_1(t)=I(t), `Φ_n(QXQᵀ)=Φ_n(X)` for orthogonal Q, and `Φ_(m+n)(X⊕Y)=Φ_m(X)+Φ_n(Y)`. Then

`Φ_n(X)=tr X−log det X−n`.

Diagonalize X orthogonally and split the resulting diagonal matrix into one-dimensional blocks. This forces `Φ_n(X)=Σ_i I(λ_i)` without any regularity assumption. The displayed formula plainly satisfies all three axioms.

The two structural rules cannot independently be omitted. `Σ_i I(X_ii)` has the rank-one seed and block additivity, but is not invariant under orthogonal conjugation. Conversely the canonical Φ plus

`ε[n tr((log X)^2)−(tr log X)^2]=εΣ_(i<j)(log λ_i−log λ_j)^2`

has the rank-one seed and orthogonal invariance, but violates block additivity on two distinct scalar blocks. For ε>0 both examples are nonnegative. A canonical construction of Φ does not force an arbitrarily designated scalar-calibrated matrix function to satisfy the construction's two rules.

## B. Divergence, metric, distance and convex conjugate

Differentiation on the vector space of symmetric matrices, paired by trace, gives

`∇Φ(X)=Id−X^(−1)`,

`g_X(U,V)=tr(X^(−1)UX^(−1)V)`.

The associated Bregman divergence is

`D(X,Y)=tr(Y^(−1)X)−log det(Y^(−1)X)−n`.

It is nonnegative by reducing to the eigenvalues of the symmetric positive-definite matrix `Y^(−1/2)XY^(−1/2)`. It vanishes precisely when X=Y. Both D and g are invariant under simultaneous congruence by an invertible real matrix. Inversion satisfies

`D(X^(−1),Y^(−1))=D(Y,X)`.

This is an argument reversal for divergence, and an isometry for the metric; the potential itself is not invariant under general congruence.

**Geodesic and distance.** Put `K=log(X^(−1/2)YX^(−1/2))`. The constant-speed minimizing geodesic is

`γ(s)=X^(1/2)exp(sK)X^(1/2)`, 0≤s≤1,

and `d(X,Y)=||K||_F`.

An independent length proof avoids assuming these formulas. Congruence invariance reduces X to Id. For any piecewise smooth curve A=exp Z with Z symmetric, diagonalize Z pointwise. The differential of exp has entries

`(d exp_Z[V])_ij = V_ij (exp z_i−exp z_j)/(z_i−z_j)`

with the diagonal/continuous-limit convention. Thus

`||A′||_(g_A)^2=Σ_(i,j)[2sinh((z_i−z_j)/2)/(z_i−z_j)]² (Z′_ij)² ≥ ||Z′||_F²`.

Integrating gives `length(A)≥||log Y||_F`. Equality is attained by A(s)=exp(s log Y), which has constant metric speed. This establishes the stated minimizing path and distance; the equality condition gives its unique image, and the constant-speed parameter fixes the parametrization.

**Affine invariance alone is not a metric-selection theorem.** The canonical Hessian fixes this particular g. Even under the same congruence action, other invariant metrics exist: `α tr(X^(−1)UX^(−1)V)+β tr(X^(−1)U)tr(X^(−1)V)`, α>0, β>−α/n. This standard family is explicitly given in the authors' primary paper [Thanwerdas–Pennec, formula (3)](https://arxiv.org/pdf/1906.01349). No bare-invariance uniqueness should be inferred.

**Convex conjugate.** For symmetric Θ,

`Φ_n*(Θ)=−log det(Id−Θ)` when Θ≺Id, and `+∞` otherwise.

Stationarity gives `X=(Id−Θ)^(−1)` and direct substitution gives the finite value. If an eigenvalue of Θ is at least one, taking the corresponding eigenvalue of X to infinity makes the supremum diverge, including the boundary case through log det X.

**Symmetrization needs more than distance in rank ≥2.** If λ_i are the relative covariance eigenvalues,

`D(X,Y)+D(Y,X)=Σ_i(λ_i+λ_i^(−1)−2)=4Σ_i sinh²((log λ_i)/2)`.

Distance squared is `Σ_i(log λ_i)²`. At fixed distance r>0, compare relative eigenvalues `(exp r,1)` with `(exp(r/√2),exp(r/√2))`. Their symmetrizations are `2cosh r−2` and `4cosh(r/√2)−4`. The first exceeds the second: their power-series difference has zero quadratic term and strictly positive coefficients at all even orders ≥4. Hence no single function of distance gives symmetrization in rank ≥2. In rank one it is `4sinh²(d/2)`.

## C. Gaussian/Wishart likelihood conventions

For supplied iid centered nonsingular Gaussian samples `z_1,…,z_m~N(0,X)`, let `S=Σz_jz_jᵀ` and `C=S/m`. The covariance-dependent negative log likelihood is

`ℓ(X)=(m/2)[log det X+tr(X^(−1)C)]+constant`.

When C is SPD, its unique minimizer is C and

`ℓ(X)−ℓ(C)=(m/2)D(C,X)`.

For known zero mean, m≥n makes C SPD almost surely; if m<n, C is singular and the likelihood has no maximizing covariance in the open SPD cone. The scatter S has the Wishart law in the supplied sampling category. The iid hypothesis, Gaussian sampling family, zero-mean convention and sample count m are additional model data, not consequences of a scalar potential. The KL divergence between the two supplied Gaussian covariance laws is `D(X,Y)/2`, and between m independent copies it is m times that value.

## D. Nonnegative orthogonal additivity without continuity

**Exact theorem.** Let V be a real inner-product space of dimension at least two, and let f:V→[0,∞) satisfy `f(x+y)=f(x)+f(y)` whenever x⊥y. Then `f(x)=c||x||²` for some c≥0, with no continuity, measurability, radiality or homogeneity premise.

Here is an elementary proof. f(0)=0. Write the even and odd parts as

`e(x)=(f(x)+f(−x))/2`, `o(x)=(f(x)−f(−x))/2`.

Both are orthogonally additive, e≥0, and `|o(x)|≤e(x)`. If ||x||=||y||, the vectors `(x+y)/2` and `(x−y)/2` are orthogonal. Evenness therefore gives e(x)=e(y), so e(x)=A(||x||²). Two orthogonal vectors with arbitrary prescribed nonnegative squared lengths show `A(a+b)=A(a)+A(b)`. Since A≥0, it is monotone and hence A(a)=ca by rational approximation.

For each x choose y⊥x with ||y||=||x||. Then x+y⊥x−y, and oddness gives

`o(2x)=o(x+y)+o(x−y)=2o(x)`.

Iterating this identity downward and using `|o(x/2^k)|≤c||x||²/4^k` yields `|o(x)|≤c||x||²/2^k` for every k, so o=0. Thus f=c||x||².

Nonnegativity is necessary for this formulation: nonzero linear functionals are orthogonally additive but not of the claimed nonnegative quadratic form. In dimension one the only orthogonal pairs involve zero, so every nonnegative function vanishing at zero is orthogonally additive. Dimension at least two is essential.

If z:V→[0,∞) instead obeys `z(x+y)=z(x)+z(y)+z(x)z(y)` for x⊥y, then `f=log(1+z)` is nonnegative and orthogonally additive. Hence

`z(x)=exp(c||x||²)−1`.

Nontriviality gives c>0; a numerical calibration is needed to choose c. This theorem classifies an already supplied spatial observable obeying the stated composition law. It does not derive that law for an arbitrary designated observable from the scalar formal group.

## E. Radial residual and countermodels for dimension selection

For radial functions in Euclidean dimension D, `Δ_D f=f″+(D−1)f′/x`. With `f=x^(−(D−1)/2)u`, direct differentiation gives

`−Δ_D f=x^(−(D−1)/2)[−u″+(D−1)(D−3)u/(4x²)]`.

The inverse-square residual vanishes exactly for D=1 or D=3. If integer D≥2 is an independently retained spatial assumption, cancellation selects D=3. Cancellation alone does not remove D=1.

The full intrinsic scalar/probability/operator/formal network can remain fixed while adding an independent designated spatial sort. On R² take r(x)=||x||⁴. For perpendicular unit vectors, r(x+y)=4 while r(x)+r(y)=2, so orthogonal additivity fails even though the observable is positive, radial and smooth. On R² take r(x)=||x||²: orthogonal additivity holds, but the radial residual is `−1/(4x²)`. On R¹ squared norm gives cancellation as well. A canonical R⁴ Gaussian auxiliary realization with `T=||Z||²/2~Gamma(2,1)` can coexist with each example: it is a separate construction, not an identification of the designated spatial sort or its observable.

## F. Calkin–Wilf, nonnegative unimodular words, Stern–Brocot and Farey

Use the marked maps `L(x)=x/(1+x)` and `R(x)=1+x`, acting on x>0, with matrices

`M_L=[[1,0],[1,1]]`, `M_R=[[1,1],[0,1]]`.

The rooted Calkin–Wilf tree starts at 1. A reduced fraction a/b<1 has unique parent a/(b−a), and a/b>1 has parent (a−b)/b. Numerator-plus-denominator decreases until 1/1; coprimality is preserved. Thus every positive rational occurs exactly once, with its unique marked word.

**Matrix monoid.** Every determinant-one matrix with nonnegative integer entries is a unique word in M_L,M_R. Except for the identity, one row dominates the other coordinatewise. Indeed the only possible determinant-one exception to that comparability has a>c and b<d; writing a=c+u, d=b+v gives `1=cv+ub+uv`, forcing u=v=1 and c=b=0, i.e. identity. Subtract the smaller row from the larger to peel off a unique leftmost generator; the total of the entries decreases. This gives both existence and word uniqueness. Here “positive SL₂(Z)” must mean **nonnegative entries**; strictly positive entries do not include the identity or generators.

**Stern–Brocot word reversal.** Store an interval's upper endpoint as the first column and lower endpoint as the second, initially `(1,0)ᵀ` and `(0,1)ᵀ`. Its mediant is the column sum. A left/right step multiplies this column matrix on the right by M_L/M_R. Calkin–Wilf successive steps multiply the fraction vector on the left. Thus a Calkin–Wilf word w corresponds to the Stern–Brocot word with reversed order, not generally the same word. For example CW(LR)=3/2 while SB(LR)=2/3.

Grouping repeated Euclidean subtractions gives the positive rational continued fraction, with `a_0≥0`, later digits positive, and the terminal digit ≥2 when the expansion has more than one digit. The final subtraction run stops at 1/1, so its length is the terminal digit minus one; it must not be equated blindly with every continued-fraction digit. Retaining orientation, the root and the standard terminal convention gives exact mutual decoding.

The two Farey inverse branches on [0,1] are `ψ₀(x)=x/(1+x)` and `ψ₁(x)=1/(1+x)`. The first is increasing onto [0,1/2], the second decreasing onto [1/2,1]. They invert the branches `y/(1−y)` and `(1−y)/y` of the Farey map. The common endpoint is harmless when branch labels are retained.

**Full-domain recovery.** A complete numerically labelled Calkin–Wilf tree recovers L and R on positive rationals. Its maps extend uniquely within the Möbius category from three marked input/output pairs. In particular the same rational formula for L extends onto (−1,∞), excluding the pole. Then

`I(t)=∫_0^(t−1)L(s)ds`, t>0.

The part t<1 requires values at −1<s<0, which the positive rational tree does not directly supply. Connected real-analytic continuation is an alternative extension condition. Without it a smooth bump in I supported in (0,1) retains all data obtained from the positive-rational L action. A bare unlabelled tree cannot select the arithmetic labels, left/right map action, marked coordinate or global extension.

## G. Placed integer code and transported arithmetic

For the placed code e(n)=σ(n), the difference is

`e(n)−e(m)=log((1+γn)/(1+γm))−μ(n−m)`.

Hence a collision at n≠m occurs precisely at

`μ=log((1+γn)/(1+γm))/(n−m)`.

With γ=1 and μ=log(5/4), e(3)=e(4), whereas

`e(6)−e(8)=log(175/144)≠0`.

Consequently no well-defined product on the image can satisfy `e(a)⊗e(b)=e(ab)` for all a,b: multiplying the common code e(3)=e(4) by e(2) would have to give distinct outputs. This example lies in the placement regime μ>0 and μ/γ<1.

Under injectivity, transport through the bijection n↦e(n) is valid and elementary. Multiplication, prime elements, divisibility, prime valuations, gcd/lcm, finite divisor lattices, the Möbius function and Dirichlet convolution all transfer exactly. Valuations recover gcd/lcm by componentwise minimum/maximum, and divisor lattices are finite products of exponent chains. This is faithful relabelling in a supplied integer category, not a claim that an arbitrary real-valued scalar object canonically discovers that category.

**Unit.** If the original domain is integers n≥2, adjoin a formal unit before stating every coprime gcd, every divisor lattice including 1, or the full Dirichlet convolution algebra. Coprime gcd is one and otherwise lies outside the original image. A formal unit is safer than calling it e(1) unless injectivity was also checked after adding index 1.

The alternative intrinsic code `e₀(n)=H(n+1)`, n≥1, is strictly decreasing because `H′(t)=1/t−1<0` for t>1. It is therefore injective and includes a code for the integer unit. It supplies a valid canonical transported integer model once its indexing convention is chosen, but it is **different from** the original placed code e(n)=σ(n), and does not remove the latter's demonstrated collisions.

## Blind verdict

Every exact construction and qualified uniqueness statement in the statement-only task passes. Essential boundaries are: the two rules for identifying an arbitrary matrix lift; the supplied sampling model and covariance domain; dimension ≥2 and nonnegative orthogonal additivity for an arbitrary spatial observable; a selected radial operator/cancellation criterion for dimension selection; numerical labels and a global extension category for rational-tree recovery; and injectivity plus a unit for faithful transport of full integer arithmetic. Full metric invariance alone is weaker than selecting the displayed Hessian metric. Comparison with the corresponding Phase III proofs has not yet been performed.



# Appendix F. Exact all-order zero-set counterexample

# Exact derivative-zero sets: the probability converse is refuted

**Z4 — status ×; analytic/probabilistic.** On the marked domain \(t>0\), the complete exact zero sets \(Z_n=\{n\}\), \(n\ge1\), do not characterize \(p(t)=te^{-t}\) among smooth positive probability densities. The conclusion still fails when the candidates are required to be real analytic, to vanish at both endpoints, and to have a unique mode at one.

For any real \(k>1\), define
\[
 f_k(t)=(k-1)k^k\frac{t}{(t+k)^{k+1}}.
\]
This function is positive and real analytic on \((0,\infty)\), vanishes at zero and infinity, and has integral one. Indeed, substitution \(t=ks\) gives
\[
 \int_0^\infty\frac{t\,dt}{(t+k)^{k+1}}
 =k^{1-k}\int_0^\infty\frac{s\,ds}{(1+s)^{k+1}}
 =\frac{k^{-k}}{k-1}.
\]
The last integral follows by writing \(s=(1+s)-1\) and integrating the two powers; no distributional identification is needed.

Put \(C_k=(k-1)k^k\) and \((k)_n=k(k+1)\cdots(k+n-1)\). For every integer \(n\ge1\),
\[
 f_k^{(n)}(t)=C_k(-1)^n(k)_n\frac{t-n}{(t+k)^{k+n+1}}. \tag{Z4.1}
\]
For \(n=1\), direct differentiation gives \(C_k k(1-t)/(t+k)^{k+2}\). Differentiating the right side of (Z4.1) uses the identity
\[
 \frac{d}{dt}\frac{t-n}{(t+k)^{k+n+1}}
 =-(k+n)\frac{t-(n+1)}{(t+k)^{k+n+2}},
\]
which proves the formula by induction. Its prefactor never vanishes and its denominator is strictly positive. Thus every derivative has exactly one zero, at \(t=n\), and that zero is simple. These are exactly the zero sets of \(p^{(n)}\).

The elementary representative
\[
 \boxed{f_2(t)=\frac{4t}{(t+2)^3}}
\]
already suffices. It differs from \(p\), for example by its algebraic tail. Consequently this is a counterexample to **exact sets**, not just zero incidences. It also preserves their strict interlacing and the derivative signs between the zeros.

For the placed coordinate \(t=\mu r+a\), \(\mu>0,0<a<1\), the full-half-line probability density \(\mu f_k(\mu r+a)\) on \(r>-a/\mu\) has zeros \(r_n=(n-a)/\mu\). If probability normalization is instead on \(r\ge0\), divide by the positive survival mass \(\int_a^\infty f_k(t)dt\). This scalar factor leaves all derivative zeros unchanged and gives the same placed zero lattice as Sigma on that domain. The distinction matters: placed \(e^{\sigma_P}\) has mass one on \([0,\infty)\), whereas its integral on its entire analytic domain is \(e^a/(1+a)\).

The counterexample does not satisfy global log-concavity: \((\log f_k)''=-t^{-2}+(k+1)/(t+k)^2\) becomes positive when \(t>1+\sqrt{k+1}\). It is not entire, owing to its singularity at \(-k\). Thus (Z4.1) refutes the stated smooth and real-analytic probability converses; it makes no claim about additional entire or globally log-concave candidate restrictions. Those restrictions are unnecessary to settle the question that Phase III left open and are not new nodes in the frozen graph.

The root derived the example directly. Two statement-only independent checks verified its normalization and all-order induction, recorded in the core/series and probability audits. Finite symbolic differentiation is retained only as a diagnostic, not the proof of (Z4.1). This theorem is not claimed to be Lean-formalized.



# Appendix G. Independent global minimality and closure adversary

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

The independent [checker](phase-iv-audit/global-graph-checks.py), run as `python3 outputs/phase-iv-audit/global-graph-checks.py`, records its output and the exact graph SHA-256 in [global-graph-checks.json](phase-iv-audit/global-graph-checks.json). It independently builds the directed identification graph, including one-way identification arrows and the spectral equivalences, computes SCCs, reconstructs the quotient and checks context availability in both directions of each identification. Construction, transport, forgetful, negative and unprovided-context edges do not manufacture an identifying inverse.

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
