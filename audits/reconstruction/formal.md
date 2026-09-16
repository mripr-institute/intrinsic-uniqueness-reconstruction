**Formal verification audit H — Phase IV, 12 September 2026.**

The final clean Lean build succeeded with exit status **0**. It rebuilt all four local proof modules from copied source in a newly created directory, then ran `#print axioms` for **all 69 exported theorems**: 16 existing `SigmaAudit` results and 53 new `PhaseIV` results. Every theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The sources contain no `sorry`, `admit`, custom axiom declarations, or `unsafe` declarations. This is a kernel-checked bounded mathematical subset using Lean/mathlib's standard foundations.

The artifacts are [PhaseIV.lean](../lean/PhaseIV.lean), [PhaseIVSeries.lean](../lean/PhaseIVSeries.lean), the complete [axiom commands](../lean/PhaseIVAxioms.lean), the exact [compiler log](../lean/PhaseIV-compile.log), and the machine-readable [build manifest and per-theorem axiom map](../lean/PhaseIV-build.json). The manifest records every compiled source's SHA-256, compiler commands, fresh build directory, and exit status.

**Reproduction and environment.** From the workspace root run:

```sh
sh outputs/lean/check-phase-iv.sh
```

The [wrapper](../lean/check-phase-iv.sh) runs [PhaseIVCheck.py](../lean/PhaseIVCheck.py). `LEAN_BIN` and `MATHLIB_DIR` may point to another compatible installation. Defaults discover this workspace's `work/phase-iv-lean-env` directory; no old home-directory path is required. Each run creates a fresh `work/phase-iv-lean-build-*` directory, copies only `.lean` source into it, compiles `SigmaAudit`, `Reconstruction`, `PhaseIV`, and `PhaseIVSeries` in dependency order, then compiles the generated axiom audit. No previous local `.olean` participates. The checker rejects a missing theorem axiom report or any reported axiom outside the three standard foundations.

The archived `check.sh` and `compile.log` were inspected. Their `/Users/alex-albert/...` toolchain and mathlib paths were absent on the current `/Users/alex_albert` machine. Bounded searches included the user directory, Documents siblings, Downloads, Desktop, `.cache`, `.local`, `/Users/Shared`, `/opt/homebrew`, and local application/tool directories. No usable Lean/mathlib installation or preinstalled Coq/Isabelle executable was found. The existing `.olean` was therefore treated as a historical artifact, not evidence of a current build.

The required dependency setup downloaded the precompiled [Lean 4.14.0 Darwin arm64 release](https://github.com/leanprover/lean4/releases/tag/v4.14.0), 238,248,774 bytes, SHA-256 `ec68b843ed1baf27a1908a51d930e3b272eedb4ce9c89414b7eac7692ba23597`. The compiler identifies itself as `Lean 4.14.0`, `arm64-apple-darwin23.6.0`, commit `410fab728470`. Mathlib is pinned to tag `v4.14.0`, commit [`4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84`](https://github.com/leanprover-community/mathlib4/tree/4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84); its dependency revisions are those in its checked-out `lake-manifest.json`. The cache download retrieved 2,517 precompiled modules. Mathlib's four small cache-bootstrap modules were compiled; no mathematical library was rebuilt from source. The cache executable encountered a macOS `dyld` flag error, resolved by running the same cache program through `lake env lean --run Cache/Main.lean get ...`. Coq and Isabelle were not installed or claimed as additional checks.

**Exact proof coverage and assumptions.** In the following table, `I` is the imported `potential(t)=t−1−log(t)` and all real identities involving logarithmic coordinates carry the positivity assumptions stated in their signatures.

| Result family | Proved result and explicit candidate class |
|---|---|
| Scalar definitions | `H=-I` is an algebraic identity on all reals. For `t>0`, `density(t)=t exp(-t)=exp(H(t)-1)=exp(-1-I(t))` and is positive. The extension of `Real.log` outside its intended positive domain is never used to extend the exponential-density identity. |
| Derivative reconstruction | Reuses and rebuilds the original mean-value proof: differentiability on `(0,∞)`, `phi(1)=0`, and `phi'(t)=1−1/t` imply `phi=I` throughout that interval. |
| Anchored symmetric Bregman converse | Differentiability on `(0,∞)`, `phi(1)=phi'(1)=0`, and the actual symmetric Bregman slice `B(t,1)+B(1,t)=t+1/t−2` imply `phi=I`. Cancellation at `t≠1` derives the derivative relation; the slope anchor handles `t=1`. Neither convexity nor a second derivative is assumed. |
| Group law and cocycle | The 16 prior theorems were all rebuilt, including closure, inverse, logarithmic homomorphism, cocycle and quotient-Bregman identities for `x+y+xy` on `x>-1`. These are proved group laws, not a bundled group instance. |
| Complete normalized real group logarithm | For a function differentiable on `(-1,∞)`, `HasDerivAt L 1 0` and the actual homomorphism equation `L(x star y)=L(x)+L(y)` imply `L(x)=log(1+x)`. The proof differentiates the homomorphism equation at its identity to derive `L'(x)=1/(1+x)`, derives `L(0)=0`, and uses the connected-domain mean-value theorem. The derivative equation is a conclusion in this result. |
| Poisson recurrence and normalization | For an arbitrary real sequence, `(n+1) pi(n+1)=pi(n)` gives `n! pi(n)=pi(0)` and `pi(n)=pi(0)/n!`. Adding the actual series statement `HasSum pi 1` fixes `pi(n)=exp(-1)/n!`, using mathlib's exponential series theorem. No independent nonnegativity premise is needed for this implication. |
| Poisson MGF and CGF algebra | The explicit canonical masses have the all-real MGF sum `sum pi(n) exp(nu)=exp(exp(u)−1)`, proved as `HasSum`. The defined centered CGF `Lambda(u)=exp(u)−1−u` has derivative `exp(u)−1`, its two zero anchors, and `1+Lambda'=exp`. The code does not use a probability-measure CGF definition or prove uniqueness of arbitrary laws from MGFs. |
| KL and Bregman formulas | The oriented scalar slice, `a log(a/b)−a+b=a I(b/a)`, the mean-coordinate Bregman identity, and `B_Lambda(u,v)=exp(v) I(exp(u−v))` are proved. These are exact formulas for the named real functions; deriving KL by integration of log-likelihood ratios is not encoded. |
| Two marked differential eigenfunctions | Derivatives of `2−t` and `t²/2−3t+3` are formally computed. For the defined conservative expression `Bf=-a(t)f''-b(t)f'`, the actual equations `B f1=f1` and `B f2=2 f2` at every positive `t` imply `a(t)=t` and `b(t)=2−t`. No smoothness or positivity of `a,b` is needed for this pointwise identification. |
| Canonical Todd/A-hat/L representatives | Real representatives use the stated exponential quotients away from zero and value one at zero. The code proves `L(u)=T(2u)−u`, `T(u)=exp(u/2) Ahat(u)`, `(L(u)+u)/(L(u)−u)=exp(2u)`, and the positive quadratic-root formula reconstructing `exp(u/2)` from `u/Ahat(u)`, including `u=0`. |
| Reversible algebraic closure | Concrete maps on real functions are bundled into `Equiv`s for Todd/L, Todd/A-hat, and `chi_y` when `y≠−1`. Both inverse compositions are proved. Equality of transformed functions is equivalent to equality of the original functions. At `y=−1`, a normalized input collapses to `1+u`. The A-hat `Equiv` uses the exponential multiplier; the separate quadratic-root theorem supplies the reconstruction of that multiplier from the canonical A-hat function. |
| Todd triangular uniqueness | Over actual `PowerSeries ℚ`, agreement of two normalized unit series below degree `n` implies that their `k`th powers differ in degree `n` by `k` times the degree-`n` difference. This triangularity is proved via divisibility by `X^n` and the finite factorization of `F^k−G^k`. Strong induction then proves uniqueness of the entire tower `[X^n]F^(n+1)=1` for all `n>0`, and injectivity of the full tower observations. Triangularity is not taken as a hypothesis. |
| Formal logarithm and marked quadratic branch | The formal logarithm is explicitly constructed with coefficients `(-1)^n/(n+1)` in degree `n+1`. Its constant term, derivative coefficients, and `(1+X)L'=1` are proved. That ODE and zero constant term uniquely reconstruct it. For formal roots of `W²−BW=1`, constant terms `W(0)=V(0)=1`, `B(0)=0` force uniqueness of the marked branch. |
| Finite block assembly | A list functional with `F([])=0` and scalar prepending increment `phi(x)`, with the scalar derivative reconstruction hypotheses, equals the sum of `I` over every positive list. Concatenation additivity is proved for that sum. The additive list category is an explicit assumption and does not assert spectral or matrix structure. |

**Remaining formal gaps.** The following distinctions limit what may be cited as formally verified:

- Todd tower **uniqueness** is proved. Existence of its solution as the Todd formal exponential quotient, the formal-residue coefficient identity, omitted-degree independence, and the bridge from the real representatives to their full Taylor series are not formalized here.
- The full real differentiable group-logarithm uniqueness theorem is proved. For formal power series, the logarithm ODE and its unique solution are proved, but differentiation of a two-variable formal group functional equation to obtain that ODE remains outside this development.
- Defining the removable value as one does not itself prove analyticity or continuity there. The characteristic identities hold for those defined representatives at every real argument, while Taylor-series and analytic-continuation statements remain unformalized.
- The normalized recurrence and canonical MGF sum are checked; probability-measure construction, MGF uniqueness for an arbitrary candidate law, centered random-variable semantics, independence, Markov kernels, Stein uniqueness, and entropy inequalities are not imported as conclusions.
- The low-degree result identifies a local differential expression. Stationary measure reconstruction, endpoint classification, essential self-adjointness, semigroup uniqueness, eigenbasis completeness, and spectral determinant arguments are not checked by this theorem.
- Finite list assembly does not establish an SPD spectral theorem, orthogonal diagonalization, Gaussian KL integration, congruence invariance, or uniqueness of an arbitrary matrix lift. Those require their own explicit category assumptions and proofs.
- No Lean proof here certifies the remaining global analytic, operator, topological, matrix, or arithmetic claims of the manuscript. In particular, there is no Riemann–Roch, index, signature, infinite-dimensional process-extension, moment-determinacy, or transcendence theorem in this module.

The genuine reconstruction steps proved above contain identifying data in their signatures, not the desired conclusion disguised as a premise. The three `closure_under_*` lemmas are deliberately small consequences of independently constructed and checked inverse maps. They certify that particular algebraic closure, not a universal claim that every branch of the manuscript is equivalent.

**Axiom inventory.** `P=propext`, `C=Classical.choice`, and `Q=Quot.sound`. The following per-theorem inventory is generated from the final `#print axioms` output. These are foundational dependencies; positivity, differentiability, normalization, recurrence, additivity, and other mathematical hypotheses remain explicit arguments in the theorem source. They are not custom axioms.

| Theorem | Reported axioms |
|---|---|
| `SigmaAudit.one_add_star` | P, C, Q |
| `SigmaAudit.star_assoc` | P, C, Q |
| `SigmaAudit.star_comm` | P, C, Q |
| `SigmaAudit.star_zero` | P, C, Q |
| `SigmaAudit.star_closed` | P, C, Q |
| `SigmaAudit.one_add_invStar` | P, C, Q |
| `SigmaAudit.invStar_closed` | P, C, Q |
| `SigmaAudit.star_inverse` | P, C, Q |
| `SigmaAudit.log_star` | P, C, Q |
| `SigmaAudit.displacement_cocycle` | P, C, Q |
| `SigmaAudit.normalized_bregman` | P, C, Q |
| `SigmaAudit.symmetric_bregman` | P, C, Q |
| `SigmaAudit.finite_scalar_assembly` | P, C, Q |
| `SigmaAudit.list_scalar_assembly` | P, C, Q |
| `SigmaAudit.potential_hasDerivAt` | P, C, Q |
| `SigmaAudit.reconstruct_from_derivative` | P, C, Q |
| `PhaseIV.H_eq_neg_potential` | P, C, Q |
| `PhaseIV.density_eq_exp_H` | P, C, Q |
| `PhaseIV.density_eq_exp_potential` | P, C, Q |
| `PhaseIV.density_pos` | P, C, Q |
| `PhaseIV.reconstruct_derivative` | P, C, Q |
| `PhaseIV.symmetric_slice_identifies_derivative` | P, C, Q |
| `PhaseIV.reconstruct_anchored_symmetric_bregman` | P, C, Q |
| `PhaseIV.normalized_group_log_derivative` | P, C, Q |
| `PhaseIV.normalized_group_log_unique` | P, C, Q |
| `PhaseIV.poisson_recurrence_factorial` | P, C, Q |
| `PhaseIV.poisson_recurrence_solution` | P, C, Q |
| `PhaseIV.inverse_factorial_hasSum` | P, C, Q |
| `PhaseIV.poisson_normalized_recurrence` | P, C, Q |
| `PhaseIV.poisson_mgf_hasSum` | P, C, Q |
| `PhaseIV.centeredCGF_hasDerivAt` | P, C, Q |
| `PhaseIV.centeredCGF_anchors` | P, C, Q |
| `PhaseIV.centeredCGF_recovers_exp` | P, C, Q |
| `PhaseIV.poisson_KL_slice` | P, C, Q |
| `PhaseIV.poisson_mean_bregman` | P, C, Q |
| `PhaseIV.poisson_KL_orientation` | P, C, Q |
| `PhaseIV.centeredCGF_bregman` | P, C, Q |
| `PhaseIV.low2_identification` | P, C, Q |
| `PhaseIV.low2_canonical` | P, C, Q |
| `PhaseIV.linearEigenfunction_deriv` | P, C, Q |
| `PhaseIV.quadraticEigenfunction_deriv` | P, C, Q |
| `PhaseIV.differential_low2_identification` | P, C, Q |
| `PhaseIV.canonical_todd_to_L` | P, C, Q |
| `PhaseIV.canonical_L_recovers_exp` | P, C, Q |
| `PhaseIV.lToTodd_toddToL` | P, C, Q |
| `PhaseIV.toddToL_lToTodd` | P, C, Q |
| `PhaseIV.canonical_ahat_to_todd` | P, C, Q |
| `PhaseIV.ahatToTodd_toddToAhat` | P, C, Q |
| `PhaseIV.toddToAhat_ahatToTodd` | P, C, Q |
| `PhaseIV.chiToTodd_toddToChi` | P, C, Q |
| `PhaseIV.toddToChi_chiToTodd` | P, C, Q |
| `PhaseIV.chi_minus_one_degenerate` | P, C, Q |
| `PhaseIV.positive_quadratic_branch_unique` | P, C, Q |
| `PhaseIV.positiveQuadraticRoot_spec` | P, C, Q |
| `PhaseIV.canonical_ahat_recovers_exp` | P, C, Q |
| `PhaseIV.blockPotential_append` | P, C, Q |
| `PhaseIV.block_reconstruction` | P, C, Q |
| `PhaseIV.closure_under_todd_L` | P, C, Q |
| `PhaseIV.closure_under_todd_Ahat` | P, C, Q |
| `PhaseIV.closure_under_todd_chi` | P, C, Q |
| `PhaseIV.coefficient_power_difference` | P, C, Q |
| `PhaseIV.todd_tower_unique` | P, C, Q |
| `PhaseIV.todd_observations_injective` | P, C, Q |
| `PhaseIV.normalized_formal_log_ode_unique` | P, C, Q |
| `PhaseIV.formalLog_constant` | P, C, Q |
| `PhaseIV.formalLog_derivative_coeff` | P, C, Q |
| `PhaseIV.formalLog_ode` | P, C, Q |
| `PhaseIV.normalized_formal_log_ode_reconstruction` | P, C, Q |
| `PhaseIV.formal_unit_quadratic_branch_unique` | P, C, Q |
