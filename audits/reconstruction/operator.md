# Phase IV operator/spectral audit

## Scope and verdict

The independent derivation was saved in [operator-blind.md](operator-blind.md) before opening Phase III or earlier operator audits. The subsequent comparison used Phase III I.6–I.7, III.1–III.3, IV.4, V.1–V.4, plus `work/audit-v2/operator-derivation.md`, `operator-statements-blind.md`, `operator-blind-review.md`, and `operator-converse-addendum.md`.

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
