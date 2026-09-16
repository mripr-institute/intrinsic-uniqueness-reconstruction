# Phase IV independent operator audit — blind findings

Written before reading `outputs/sigma-phase-iii.md` or any preceding operator audit. The parent supplied only the claims to audit. No assumptions below are inferred from those unseen proofs.

## Verdict

The weak Stein characterization, two polynomial coefficient probes, essential self-adjointness, Laguerre spectral resolution, heat kernel, determinant formulas, and Hausdorff mixing uniqueness are valid with the qualifications below. The main danger is a type error: an abstract operator, its stationary coordinate law, and a measure used to mix its semigroup are three different objects. Spectral data plus a mixing identity do not identify an arbitrary stationary coordinate density unless their coupling is stipulated.

## 1. Weak Stein identity derives the support

Let P be a Borel probability measure on all of R. Suppose

\[
\int [x f'(x)+(2-x)f(x)]\,P(dx)=0\qquad(f\in C_c^\infty(\mathbb R)).
\]

Then P(dx)=1_{x>0}x e^{-x}dx. No density, moments, positive support, or boundary condition is required beforehand.

Indeed, in distributions, `(xP)'=(2-x)P`. On each open half-line this first-order equation has only density solutions `C_+ x e^{-x}` and `C_- |x|e^{-x}`, respectively. One can justify the absence of singular parts by multiplying the distributional equation by the smooth integrating factor on any interval avoiding zero: a distribution with zero derivative is constant. Nonnegativity gives C_±≥0; integrability at minus infinity forces C_-=0. The residual measure at zero is mδ_0, and substitution gives 2mδ_0=0. Normalization gives C_+=1. Conversely, integration by parts works because x²e^{-x} vanishes at zero and the test function has compact support.

Distinguish this full-line test class from tests supported only in (0,∞): the latter never see mass outside that interval or an atom at zero.

## 2. Two probes recover a local differential expression

For the conservative local expression `Bf=-a(x)f''-b(x)f'`, assume the two polynomial identities hold pointwise, or almost everywhere in the coefficient sense:

\[
B(2-x)=2-x,\qquad B(x^2/2-3x+3)=x^2-6x+6.
\]

The first gives b(x)=2-x. The second gives
`-a(x)-(2-x)(x-3)=x²-6x+6`, hence a(x)=x. This identifies the expression only in the stipulated local conservative class; killing terms, nonlocal operators, and arbitrary self-adjoint operators are excluded. The polynomials are not in C_c^∞, so the identities must be defined on an enlarged domain or explicitly as identities of differential expressions.

## 3. Canonical self-adjoint realization

On H=L²((0,∞),w dx), w=xe^{-x}, set p=x²e^{-x} and

\[
A_{\min}=-w^{-1}(p f')',\qquad D(A_{\min})=C_c^\infty(0,\infty).
\]

The form is nonnegative. At zero energy two independent solutions are `1` and `v(x)=∫^x e^u/u² du`. Near zero, v(x) is asymptotic to -1/x, so |v|²w is asymptotic to 1/x and is not integrable; the constant solution is integrable. At infinity v(x) is asymptotic to e^x/x², so |v|²w is asymptotic to e^x/x³ and is not integrable; the constant solution is again integrable. Thus both endpoints are limit point. The minimal operator is essentially self-adjoint; its unique self-adjoint closure A is nonnegative.

Its normalized eigenfunctions are
\[
\phi_n(x)=L_n^{(1)}(x)/\sqrt{n+1},\qquad A\phi_n=n\phi_n,
\quad n=0,1,\dots.
\]
They are a complete orthonormal basis. Completeness can also be proved directly: a vector orthogonal to every polynomial has analytic weighted Laplace transform near zero, all derivatives vanish, and Laplace uniqueness forces the vector to vanish. The maximal domain contains these polynomial solutions, so essential self-adjointness places them in D(A). The spectrum is exactly the simple nonnegative integers and the resolvent is compact.

## 4. Full spectral data and their exact limitations

The heat trace, including the zero eigenspace, is
\[
\operatorname{Tr}(e^{-\tau A})=(1-e^{-\tau})^{-1},\quad\tau>0.
\]
The spectral zeta function must omit the zero mode:
\[
\zeta_A(s):=\operatorname{Tr}_{\ker(A)^\perp}(A^{-s})=\zeta(s),\quad\Re s>1.
\]
Writing an ordinary full trace of A^{-s} without this convention is undefined. Alternatively use `(1+A)^{-s}`, whose ordinary full trace is ζ(s).

For a nonnegative self-adjoint operator with trace-class heat semigroup, its heat trace for all positive times determines all eigenvalues and multiplicities, hence its unitary equivalence class. One direct proof recovers the lowest eigenvalue by the large-time exponential rate, its multiplicity by the corresponding coefficient, subtracts that term, and repeats. Likewise the entire positive spectral zeta function on a half-plane determines the positive spectrum, but does not determine the zero-mode multiplicity: the kernel must be separately specified.

Neither trace statement identifies a coordinate density. The canonical Gamma(3) Laguerre operator
\[
A_3=-[x\partial_x^2+(3-x)\partial_x]
\quad\text{on }L^2(x^2e^{-x}dx/2)
\]
has the same simple spectrum n≥0, heat trace, positive zeta function, and every scalar spectral invariant. Both endpoints are limit point here too. Its stationary law is Gamma(3), not Gamma(2).

More generally every nonatomic probability space admits a unitary identification with the abstract separable Hilbert space carrying a diagonal operator with eigenvalues n. Unitary spectral invariants do not retain the multiplication operator representing the coordinate. Even an intertwiner preserving the constant vector need not preserve that coordinate observable.

## 5. Finite regularized values do not determine the full spectrum

A concrete finite-rank countermodel keeps zero and all eigenvalues n≥4 fixed, and replaces 1,2,3 by a,b,c, where
\[
a=1+\epsilon,\quad b+c=5-\epsilon,\quad bc=6/(1+\epsilon).
\]
For sufficiently small nonzero real ε the roots b,c remain distinct, positive, and near 2,3. Their sum and product equal those of 1,2,3. Therefore the modified zeta function has the same values at s=0 and s=-1, and the same derivative at zero, hence the same zeta determinant. Nevertheless its spectrum and full heat/zeta functions differ.

For any prescribed finite list ζ(0),ζ(-1),…,ζ(-M),ζ'(0), perturb M+2 positive eigenvalues and preserve the M power sums and their product. The gradients of the M power sums and the log product have full row rank: after multiplying column i by λ_i, the resulting rows are the powers λ_i^0,…,λ_i^M (up to nonzero row constants). The implicit function theorem gives a positive-dimensional family through distinct positive eigenvalues. This establishes the claimed insufficiency for this standard finite family. Broader collections need their own rank argument; “every imaginable finite invariant is insufficient” would be overbroad.

## 6. Heat kernel and determinant conventions

For τ>0 and q=e^{-τ}, the heat kernel relative to the probability measure `y e^{-y}dy` is
\[
K_\tau(x,y)=\frac{\exp[-q(x+y)/(1-q)]}{(1-q)\sqrt{qxy}}
I_1\!\left(\frac{2\sqrt{qxy}}{1-q}\right).
\]
It is the sum `Σ q^n L_n^(1)(x)L_n^(1)(y)/(n+1)` by the Hille–Hardy formula. The transition density relative to Lebesgue measure is `K_τ(x,y)y e^{-y}`. This distinction matters for normalization. [NIST DLMF, Hille–Hardy formula](https://dlmf.nist.gov/18.18.E27).

For a real shift α>0,
\[
\operatorname{Tr}(A+\alpha)^{-r}=\zeta(r,\alpha)\quad(r>1),
\qquad
\det_\zeta(A+\alpha)=\sqrt{2\pi}/\Gamma(\alpha).
\]
The first resolvent is not trace class. Resolvent differences are trace class, with
`Tr[(A+α)^{-1}-(A+β)^{-1}]=ψ(β)-ψ(α)` for α,β>0. The determinant follows from the Hurwitz identity `ζ'(0,α)=log Γ(α)−½log(2π)`. [NIST DLMF, Hurwitz zeta derivative](https://dlmf.nist.gov/25.11.E18).

For complex z the following are entire identities, interpreting the first expression at zero by continuity:
\[
\det(I+z(1+A)^{-2})=\frac{\sinh(\pi\sqrt z)}{\pi\sqrt z},
\qquad
\det_2(I+z(1+A)^{-1})=\frac{e^{-\gamma z}}{\Gamma(1+z)}.
\]
The first determinant is an ordinary Fredholm determinant of a trace-class perturbation. The second is the Hilbert–Schmidt regularized determinant, namely `∏_{k≥1}(1+z/k)e^{-z/k}`. The square-root display is branch independent because the quotient is even in its square-root argument. [NIST DLMF, hyperbolic sine product](https://dlmf.nist.gov/4.36.E1); [NIST DLMF, gamma product](https://dlmf.nist.gov/5.8.E2).

## 7. Mixing law: what the J identity really identifies

Let B be a nonnegative self-adjoint operator having every integer n≥0 as an eigenvalue. Let ρ be a Borel probability measure on [0,∞). Then
\[
\int_0^\infty e^{-sB}\,\rho(ds)=(I+B)^{-2}
\]
implies ρ(ds)=s e^{-s}ds. Applying the identity to an n-eigenvector gives `∫e^{-ns}ρ(ds)=(n+1)^{-2}`. Under x=e^{-s} these are all Hausdorff moments of a probability measure on [0,1]. The measure with density `−log x` on (0,1) has those moments. Polynomial density in C[0,1] proves uniqueness, and the inverse substitution gives the claimed ρ. Existence follows directly from `∫s e^{-(n+1)s}ds=(n+1)^{-2}` and the bounded spectral calculus. The same existence identity in fact works for every nonnegative self-adjoint B, even without integer spectrum.

This proves a characterization of ρ. If a model also carries a stationary coordinate law P, it proves P=Gamma(2) only when the premise explicitly says ρ=P. The Gamma(3) countermodel A_3 together with the Gamma(2) mixing measure satisfies the entire abstract spectral/J package while its stationary coordinate law is Gamma(3).

Three valid node types are therefore distinct:

1. **Intrinsic measure identity:** the unknown P itself is the mixing measure in the displayed identity. This genuinely characterizes P once all integer spectral samples are supplied.
2. **Recipe-marked construction:** a known Gamma(2) measure is fed into an explicitly fixed construction of A and its semigroup. Forward construction and recovery of the marked input may form a typed equivalence, but this is not inverse spectral identification of arbitrary stationary realizations.
3. **Unmarked abstract operator plus some mixing measure:** determines the unitary class of B and ρ separately. It has no reverse edge to the stationary coordinate law without a coupling hypothesis.

An intrinsic SCC may contain type 1, or the explicitly marked package of type 2 if the graph permits constructed objects. It must not silently replace either by type 3. A local coefficient/coordinate marker can also restore identification, but that is additional data.

## 8. Bernstein functions really are identified by all integer samples

Let f,g be Bernstein functions with their standard finite values at zero. The usual representation is
`f(λ)=a+bλ+∫(1−e^{-λt})ν(dt)`, with `∫min(1,t)ν(dt)<∞`.
Then
\[
f(n+1)-f(n)=b+\int e^{-nt}(1-e^{-t})\nu(dt).
\]
These are the Hausdorff moments of the finite measure obtained by pushing `(1−e^{-t})ν(dt)` under x=e^{-t} and adding bδ_1. Equality of f and g at every n≥0 gives equality of these measures, their atom at 1 recovers b, and undoing the positive weight recovers ν. Finally f(0)=a recovers the killing term. Thus f=g on [0,∞). Consequently `f(A)=g(A)` for the canonical A identifies the whole Bernstein function, although arbitrary scalar functions are identified only on the integer spectrum.

## Items requiring comparison after unblinding

- Does the zeta trace omit the kernel and is its multiplicity retained in reverse claims?
- Does the J measure denote the same unknown law as the stationary coordinate law, or only a separate mixing measure?
- Does the SCC include the coordinate/recipe marker explicitly, or promote an abstract spectral realization to an intrinsic law characterization?
- Are finite invariant counterexamples supported by an actual family preserving the listed invariants?
- Are local differential identities properly typed, and are the kernel reference measure and determinant shifts explicit?
