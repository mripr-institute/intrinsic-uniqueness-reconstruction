# Phase IV probability/transform audit: blind derivation

This file was written before opening `outputs/sigma-phase-iii.md` or its proof text. The statement-only task supplied `I(t)=t-1-log(t)`, `p(t)=t exp(-t)`, the marked KL orientations, and the definitions of the deficit law and coordinate involution. The conclusions below were independently derived. Symbols: **✓** proved under the stated exact hypotheses; **△** qualification essential; **✗** false without the indicated qualification. Historical classification is deferred until comparison.

## 1. Factorial moments on the whole real line

**✓ Exact statement.** If a finite positive Borel measure μ on R has every moment `∫x^n μ(dx)=(n+1)!`, for integers n≥0, then `μ(dx)=1_(x>0) x exp(-x) dx`. Both probability mass and nonnegative support are conclusions.

The zeroth moment gives mass one. For `0<a<1`, monotone convergence applied to the nonnegative even-power series gives

`∫cosh(ax) μ(dx) = Σ_(n≥0) (2n+1)a^(2n) = (1+a²)/(1-a²)²`.

Thus `∫exp(a|x|) μ(dx)<∞`. Its bilateral moment generating function is holomorphic in `|Re z|<1`; in a neighborhood of zero, dominated expansion gives

`M(z)=Σ_(n≥0)(n+1)z^n=(1-z)^(-2)`.

The Gamma(2, rate 1) probability measure has the same transform. The identity theorem extends equality through the strip, including the imaginary axis, and uniqueness of characteristic functions gives equality of the measures. This bypasses a support assumption and also bypasses an appeal to Carleman. Topological support is **[0,∞)**, although mass is carried by (0,∞) and μ({0})=0. Calling the topological support `(0,∞)` would be inaccurate.

## 2. Recurrence, centered CGF, and marked KL slices

**✓** For a probability sequence `(π_n)_(n≥0)`, `(n+1)π_(n+1)=π_n` gives `π_n=π_0/n!`; summing fixes `π_0=e^(-1)`. Therefore the law is Poisson(1).

Its centered cumulant generating function is

`K(s)=log E exp(s(N-1))=e^s-1-s=I(e^s)`.

The marked logarithmic coordinate `t=e^s` consequently recovers I. Direct integration/summation also gives, for every t>0,

* `D(Pois(1) || Pois(t))=t-1-log t=I(t)`;
* `D(Exp(rate 1) || Exp(rate t))=t-1-log t=I(t)`;
* `2D(N(0,variance t) || N(0,variance 1))=t-1-log t=I(t)`.

**△** These are exact oriented and parameter-marked identities. Reversing the first KL gives `t log t-t+1`; reversing the exponential slice gives `log t+1/t-1`; reversing the displayed Gaussian slice gives one half of that latter expression. Also, the Legendre transform of the centered Poisson CGF is `(1+x)log(1+x)-x` on x≥−1, not I(x) in an unchanged coordinate. An unlabeled KL geometry or an unlabeled Poisson law does not specify the marked t coordinate.

## 3. Two max-stability equations force Gumbel without smoothness

**✓ Exact statement.** A CDF F on R satisfying, at every x,

`F(x+log 2)^2=F(x)`, `F(x+log 3)^3=F(x)`, `F(0)=exp(-1)`

is `F(x)=exp(-exp(-x))`.

Let `a=log 2`, `b=log 3`. Repeated application in both directions gives `F(ma)=exp(-2^(-m))` for every integer m. Monotonicity sandwiches F(x) between two such values, proving `0<F(x)<1` at every finite x. Hence `G=-log F` is finite, positive, and nonincreasing. The equations give `G(x+a)=G(x)/2` and `G(x+b)=G(x)/3`. In particular,

`G(ma+nb)=exp(-(ma+nb))` for all integers m,n.

The subgroup `{ma+nb}` is dense because `log 2/log 3` is irrational: any rational relation would contradict unique prime factorization. Approximating x from below and above by subgroup points and using monotonicity yields `G(x)=exp(-x)`. Right continuity, differentiability, and initial full-support assumptions are unnecessary. Full support is derived.

**△ Sharpness examples.** Without the anchor, `exp(-c exp(-x))`, c>0, gives the unfixed location family. With only the base-2 equation and the anchor, let `h(x)=1+ε sin(2πx/a)` and `F(x)=exp(-exp(-x)h(x))`. For sufficiently small nonzero ε, `h>0` and `h'<h`, so F is a valid CDF and is not standard Gumbel.

## 4. Deficit law together with the marked level involution

**✓ Exact statement.** Let J be continuous on (0,∞), with J(1)=0, J≥0, strictly decreasing on (0,1], strictly increasing on [1,∞), and tending to infinity at both endpoints. Suppose `q_J(t)=exp(-1-J(t))` integrates to one. Let `H_J` be the entire law of `J(T)` for `T~q_J(t)dt`, and let j_J be the exact decreasing coordinate involution exchanging the two roots of each positive level and fixing 1. The pair `(H_J,j_J)` determines J uniquely. In particular equality of both data with their I-data forces J=I.

For u≥0 let the roots be `a(u)≤1≤b(u)` and set `W(u)=b(u)-a(u)`. Then `W(0)=0`, W is continuous and strictly increasing, and the pushforward of Lebesgue measure by J has distribution function W. Consequently, as locally finite Stieltjes measures,

`dH_J(u)=exp(-1-u)dW(u)`,

and the measured law reconstructs the unweighted sublevel widths:

`W(u)=e ∫_[0,u] exp(v) dH_J(v)`.

No differentiation of J or density of H_J is assumed. On 0<t≤1, `D(t)=j_J(t)-t` is a continuous strictly decreasing bijection onto [0,∞), with the order reversed. The roots are therefore

`a(u)=D^(-1)(W(u))`, `b(u)=j_J(a(u))`.

Inverting these two root branches recovers J at every point.

**✓ The law alone is insufficient even in the linked, normalized class.** Start with the I-root branches a,b. Choose a nonzero smooth bump h supported inside a compact level interval in (0,∞). Put `a_ε=a+εh` and `b_ε=b+εh`. A sufficiently small nonzero ε preserves the strict branch monotonicities and positions around 1. Their inverse branches define a different admissible J_ε. Its width equals W exactly; the displayed Stieltjes identity therefore preserves both normalization and the full law H, while moving the marked involution.

**✓ The involution alone is insufficient even in the linked, normalized class.** Choose two nonzero nonnegative smooth level bumps f,g with disjoint compact supports in (0,∞). For small ε,c put `h_(ε,c)(u)=u+εf(u)+cg(u)` and `J_(ε,c)=h_(ε,c)∘I`. Small coefficients ensure h is a strictly increasing bijection fixing zero, so every J has the original involution. The normalization functional

`N(ε,c)=∫ exp(-1-h_(ε,c)(I(t)))dt`

is differentiable near (0,0), satisfies N(0,0)=1, and has `∂_c N(0,0)=-∫exp(-1-I(t))g(I(t))dt<0`. The implicit function theorem gives c=c(ε) keeping N=1. For nonzero ε, disjoint bump supports ensure J differs from I. By the joint uniqueness just proved, its deficit law must differ.

**△** “Decreasing/increasing” should mean **strictly** here, or the theorem must separately define how an exact root pairing handles plateaus. Strictness is the cleanest exact statement. An involution known only up to conjugacy is insufficient, since the formula for W uses the specific Lebesgue t coordinate.

## 5. Reverse transforms, Gamma Lévy data, and self-decomposability

**✓ Size bias.** For X≥0 with `0<m=EX<∞`, the size-biased law is `β(dx)=x μ(dx)/m`. If μ({0})=0, the inverse exists precisely when `c=∫x^(-1)β(dx)<∞`, and is

`μ(dx)=β(dx)/(cx)`, `m=1/c`.

For β=Gamma(2,1), c=1, so μ=Exp(1). If zero atoms are allowed, every `rδ_0+(1-r)Exp(1)`, 0≤r<1, has the same Gamma(2,1) size bias. Thus the no-zero-atom qualification is essential.

**✓ Equilibrium transform.** Its canonical decreasing right-continuous density is `q_E(t)=P(X>t)/m` for t≥0. With no atom at zero, `q_E(0+)=1/m`, so the mean and then the full survival function are recovered. With a zero atom r, mixing the original positive law with rδ_0 scales both the tail and mean by 1−r, leaving the equilibrium distribution unchanged. A density known only almost everywhere still determines its canonical monotone right-continuous representative. The exponential law is fixed by equilibrium, and that fixed-point equation determines an exponential family; a marked mean determines its rate.

**✓ Marked exponential tilt.** If `μ_θ(dx)=e^(θx)μ(dx)/M(θ)` and θ is given, the inverse is `μ(dx)=e^(-θx)μ_θ(dx)/∫e^(-θy)μ_θ(dy)`. For Gamma(2,1), θ<1 gives Gamma(2,rate 1−θ). An unspecified tilt parameter leaves a rate ambiguity.

**✓/△ Gamma Lévy data.** A probability subordinator is identified in law by its killing, drift, and Lévy measure. With killing and drift both zero, `ν(dx)=2exp(-x)dx/x` gives

`ψ(s)=∫(1-exp(-sx))ν(dx)=2log(1+s)`, s≥0,

as follows by differentiation and ψ(0)=0. Hence `Eexp(-sS_t)=(1+s)^(-2t)` and S_1 has Gamma(2,1) law. The density by itself does **not** determine drift or killing: adding any `d s+κ` leaves ν unchanged. “Probability” excludes killing, but zero drift must still be imposed or recovered from additional data.

**✓ Self-decomposability, proved directly.** For 0<c<1, the quotient of the Gamma Laplace transform at s and cs has exponent

`ψ(s)-ψ(cs)=∫(1-exp(-sx)) [2exp(-x)-2exp(-x/c)]dx/x`.

The residual Lévy density is nonnegative and has finite total mass `2log(1/c)`. It defines a compound-Poisson Y_c independent of a Gamma copy X′, with `X =_law cX′+Y_c`. This proves self-decomposability without quoting a criterion. Its residual atom at zero is c².

## 6. Every Bernstein function is determined by integer samples

**✓ Exact statement.** If f,g are Bernstein functions on (0,∞) and `f(n)=g(n)` for every positive integer n, then f=g. Sampling the value at zero is not necessary.

Use the Lévy–Khintchine representation `f(s)=a+bs+∫_(0,∞)(1-exp(-sx))ν(dx)`. The finite measure

`ρ=bδ_1 + (x↦exp(-x))_*[(1-exp(-x))ν(dx)]`

on [0,1] has no atom at zero, and

`f(n+1)-f(n)=∫u^n ρ(du)`.

If zero is sampled, n≥0 provides all ordinary moments of ρ directly. If only positive integers are sampled, n≥1 gives every moment of the finite measure `η(du)=uρ(du)`. Compact-interval moment uniqueness follows from uniform polynomial approximation of continuous functions. Recover ρ on (0,1] by dividing η by u, and use ρ({0})=0. The atom at 1 gives b; undoing the pushforward and its positive weight recovers ν. Finally any one sampled value, such as f(1), determines a. Therefore all parameters and all values are fixed. The absence of an atom at zero follows from the representation itself, so is not an additional assumption.

The representation, including uniqueness and integrability, was checked against the authors’ primary research paper: [Deng and Schilling, introductory formula (2)](https://arxiv.org/pdf/1606.04610). The discrete-sample uniqueness argument above is independently supplied; that source is not being cited as proving it.

## 7. Rooted/Borel coefficients and branching-model identifiability

**✓ Marked analytic germ.** The rooted-tree exponential generating function

`R(z)=Σ_(n≥1)n^(n−1)z^n/n!`

has a locally convergent germ and satisfies `R=z exp(R)` by Lagrange inversion (equivalently the rooted labelled-tree decomposition). Its derivative at zero is one. Its marked inverse germ is therefore `p(t)=t exp(-t)`. If the unknown candidate p is **real analytic on connected (0,∞)** and agrees with that inverse germ for small positive t, the real-analytic identity theorem forces p(t)=t exp(-t) everywhere. Selecting the symbolic formula as a canonical global extension is an alternative construction, not a theorem that arbitrary global continuations are unique.

For the Borel(1) probabilities `b_n=e^(-n)n^(n−1)/n!`, the PGF is `B(z)=R(z/e)`. Its inverse germ is `z=t exp(1-t)=e p(t)`; the marked factor e must be retained. The Borel coefficients alone with an unmarked rescaling of their argument do not fix that coordinate normalization.

**✗ Without global analyticity, a local germ does not identify a global function.** For any nonzero smooth bump h supported away from zero, `p_ε(t)=p(t)exp(εh(t))` has the same germ and differs globally. A sufficiently small perturbation supported away from t=1 can also preserve positivity, the unique maximum at 1, and branch monotonicities. This is a genuine smooth countermodel, not merely a formal objection.

**✗ A total-size law does not determine an arbitrary random rooted tree.** Draw N with the Borel law and output either the rooted star on N vertices or the rooted path on N vertices. The size laws agree, but the rooted tree laws differ on N≥3.

**✓ The iid one-ancestor Galton–Watson class repairs this converse.** Let an iid Galton–Watson process with one initial ancestor have almost surely finite total size N with Borel(1) law. Let Φ be its offspring PGF and B its total-size PGF. Conditioning on root offspring and using independence gives `B(z)=zΦ(B(z))`. The Borel function satisfies `B(z)=z exp(B(z)-1)` and maps (0,1) bijectively onto (0,1). Consequently `Φ(w)=exp(w-1)` for every 0<w<1. Uniqueness of power-series coefficients gives offspring Poisson(1), and the iid branching construction then determines the tree law. The ancestor count and iid branching assumptions carry real information.

## Blind verdict

All seven precise forward/uniqueness claims are mathematically valid under the markings and candidate classes specified above. The potential reconstruction works with continuous strict branches using Stieltjes measures; it does not need hidden differentiability. Both marginal counterexamples survive the linked-density normalization. Integer-sample Bernstein uniqueness even holds when only positive integers are given. Actual failure modes are unmarked coordinates/orientations, zero-atom loss under bias/equilibrium, unspecified subordinator drift, unconstrained continuation of a local germ, and arbitrary tree models with the same size law. Comparison with Phase III remains to be performed.
