# Phase IV matrix, spatial and arithmetic audit: blind derivations

This file was written from the coordinator's statement-only task before opening the corresponding Phase III proofs. The earlier probability audit exposed probability sections and some search-result snippets from other sections; it did not expose the detailed matrix, spatial or arithmetic proofs. No independence stronger than that is claimed. The intrinsic functions are `I(t)=t−1−log t`, `H=−I`, `p(t)=t exp(−t)` in the marked t>0 coordinate.

Symbols: **✓** proved as precisely stated; **△** essential qualification; **✗** false converse. Historical novelty and comparison are deferred until after this file is written.

## A. Canonical SPD lift

**✓ Exact theorem.** For each positive integer n, let Φ_n be a real-valued function on the real symmetric positive-definite n×n matrices. Suppose Φ_1(t)=I(t), `Φ_n(QXQᵀ)=Φ_n(X)` for orthogonal Q, and `Φ_(m+n)(X⊕Y)=Φ_m(X)+Φ_n(Y)`. Then

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

**✓ Geodesic and distance.** Put `K=log(X^(−1/2)YX^(−1/2))`. The constant-speed minimizing geodesic is

`γ(s)=X^(1/2)exp(sK)X^(1/2)`, 0≤s≤1,

and `d(X,Y)=||K||_F`.

An independent length proof avoids assuming these formulas. Congruence invariance reduces X to Id. For any piecewise smooth curve A=exp Z with Z symmetric, diagonalize Z pointwise. The differential of exp has entries

`(d exp_Z[V])_ij = V_ij (exp z_i−exp z_j)/(z_i−z_j)`

with the diagonal/continuous-limit convention. Thus

`||A′||_(g_A)^2=Σ_(i,j)[2sinh((z_i−z_j)/2)/(z_i−z_j)]² (Z′_ij)² ≥ ||Z′||_F²`.

Integrating gives `length(A)≥||log Y||_F`. Equality is attained by A(s)=exp(s log Y), which has constant metric speed. This establishes the stated minimizing path and distance; the equality condition gives its unique image, and the constant-speed parameter fixes the parametrization.

**△ Affine invariance alone is not a metric-selection theorem.** The canonical Hessian fixes this particular g. Even under the same congruence action, other invariant metrics exist: `α tr(X^(−1)UX^(−1)V)+β tr(X^(−1)U)tr(X^(−1)V)`, α>0, β>−α/n. This standard family is explicitly given in the authors' primary paper [Thanwerdas–Pennec, formula (3)](https://arxiv.org/pdf/1906.01349). No bare-invariance uniqueness should be inferred.

**✓ Convex conjugate.** For symmetric Θ,

`Φ_n*(Θ)=−log det(Id−Θ)` when Θ≺Id, and `+∞` otherwise.

Stationarity gives `X=(Id−Θ)^(−1)` and direct substitution gives the finite value. If an eigenvalue of Θ is at least one, taking the corresponding eigenvalue of X to infinity makes the supremum diverge, including the boundary case through log det X.

**✓ Symmetrization needs more than distance in rank ≥2.** If λ_i are the relative covariance eigenvalues,

`D(X,Y)+D(Y,X)=Σ_i(λ_i+λ_i^(−1)−2)=4Σ_i sinh²((log λ_i)/2)`.

Distance squared is `Σ_i(log λ_i)²`. At fixed distance r>0, compare relative eigenvalues `(exp r,1)` with `(exp(r/√2),exp(r/√2))`. Their symmetrizations are `2cosh r−2` and `4cosh(r/√2)−4`. The first exceeds the second: their power-series difference has zero quadratic term and strictly positive coefficients at all even orders ≥4. Hence no single function of distance gives symmetrization in rank ≥2. In rank one it is `4sinh²(d/2)`.

## C. Gaussian/Wishart likelihood conventions

For supplied iid centered nonsingular Gaussian samples `z_1,…,z_m~N(0,X)`, let `S=Σz_jz_jᵀ` and `C=S/m`. The covariance-dependent negative log likelihood is

`ℓ(X)=(m/2)[log det X+tr(X^(−1)C)]+constant`.

When C is SPD, its unique minimizer is C and

`ℓ(X)−ℓ(C)=(m/2)D(C,X)`.

For known zero mean, m≥n makes C SPD almost surely; if m<n, C is singular and the likelihood has no maximizing covariance in the open SPD cone. The scatter S has the Wishart law in the supplied sampling category. The iid hypothesis, Gaussian sampling family, zero-mean convention and sample count m are additional model data, not consequences of a scalar potential. The KL divergence between the two supplied Gaussian covariance laws is `D(X,Y)/2`, and between m independent copies it is m times that value.

## D. Nonnegative orthogonal additivity without continuity

**✓ Exact theorem.** Let V be a real inner-product space of dimension at least two, and let f:V→[0,∞) satisfy `f(x+y)=f(x)+f(y)` whenever x⊥y. Then `f(x)=c||x||²` for some c≥0, with no continuity, measurability, radiality or homogeneity premise.

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

**✓ Matrix monoid.** Every determinant-one matrix with nonnegative integer entries is a unique word in M_L,M_R. Except for the identity, one row dominates the other coordinatewise. Indeed the only possible determinant-one exception to that comparability has a>c and b<d; writing a=c+u, d=b+v gives `1=cv+ub+uv`, forcing u=v=1 and c=b=0, i.e. identity. Subtract the smaller row from the larger to peel off a unique leftmost generator; the total of the entries decreases. This gives both existence and word uniqueness. Here “positive SL₂(Z)” must mean **nonnegative entries**; strictly positive entries do not include the identity or generators.

**✓ Stern–Brocot word reversal.** Store an interval's upper endpoint as the first column and lower endpoint as the second, initially `(1,0)ᵀ` and `(0,1)ᵀ`. Its mediant is the column sum. A left/right step multiplies this column matrix on the right by M_L/M_R. Calkin–Wilf successive steps multiply the fraction vector on the left. Thus a Calkin–Wilf word w corresponds to the Stern–Brocot word with reversed order, not generally the same word. For example CW(LR)=3/2 while SB(LR)=2/3.

Grouping repeated Euclidean subtractions gives the positive rational continued fraction, with `a_0≥0`, later digits positive, and the terminal digit ≥2 when the expansion has more than one digit. The final subtraction run stops at 1/1, so its length is the terminal digit minus one; it must not be equated blindly with every continued-fraction digit. Retaining orientation, the root and the standard terminal convention gives exact mutual decoding.

The two Farey inverse branches on [0,1] are `ψ₀(x)=x/(1+x)` and `ψ₁(x)=1/(1+x)`. The first is increasing onto [0,1/2], the second decreasing onto [1/2,1]. They invert the branches `y/(1−y)` and `(1−y)/y` of the Farey map. The common endpoint is harmless when branch labels are retained.

**△ Full-domain recovery.** A complete numerically labelled Calkin–Wilf tree recovers L and R on positive rationals. Its maps extend uniquely within the Möbius category from three marked input/output pairs. In particular the same rational formula for L extends onto (−1,∞), excluding the pole. Then

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

**△ Unit.** If the original domain is integers n≥2, adjoin a formal unit before stating every coprime gcd, every divisor lattice including 1, or the full Dirichlet convolution algebra. Coprime gcd is one and otherwise lies outside the original image. A formal unit is safer than calling it e(1) unless injectivity was also checked after adding index 1.

The alternative intrinsic code `e₀(n)=H(n+1)`, n≥1, is strictly decreasing because `H′(t)=1/t−1<0` for t>1. It is therefore injective and includes a code for the integer unit. It supplies a valid canonical transported integer model once its indexing convention is chosen, but it is **different from** the original placed code e(n)=σ(n), and does not remove the latter's demonstrated collisions.

## Blind verdict

Every exact construction and qualified uniqueness statement in the statement-only task passes. Essential boundaries are: the two rules for identifying an arbitrary matrix lift; the supplied sampling model and covariance domain; dimension ≥2 and nonnegative orthogonal additivity for an arbitrary spatial observable; a selected radial operator/cancellation criterion for dimension selection; numerical labels and a global extension category for rational-tree recovery; and injectivity plus a unit for faithful transport of full integer arithmetic. Full metric invariance alone is weaker than selecting the displayed Hessian metric. Comparison with the corresponding Phase III proofs has not yet been performed.
