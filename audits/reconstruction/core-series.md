# Phase IV independent core and scalar-series audit

The statement-only audit was saved as [core-series-blind.md](core-series-blind.md) before opening Phase III. This audit subsequently read Phase III §§I.1–I.2, II.1–II.2, III.4–III.5, III.7, III.11, IV.1–IV.3, IV.8–IV.9, together with the earlier master E0–E14 clauses in the manuscript, dependency ledger and sixteen-branch audit. It does not modify the manuscript or global report.

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

No new Lean theorem is claimed by this audit file. Its exported statements are written mathematical proofs with explicit dependencies. The reproducible symbolic diagnostics in [core-series-checks.py](core-series-checks.py), recorded in [core-series-checks.json](core-series-checks.json), check the Todd twists through n=6, the T/A/L identities through degree 7, the rational counterexample's exact mass, and its derivative formula through order 12. All pass. They remain finite checks; the universal arguments are the proofs above.
