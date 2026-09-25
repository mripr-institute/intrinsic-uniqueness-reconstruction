# Inventory of Lean-formalized paper results

Generated from the current independently reviewed maps by `python3 scripts/rebuild_coverage.py --write`.

The paper supplies mathematical proofs of its results. This inventory lists their Lean formalizations. Partial or missing Lean coverage does not mean that a paper result is unproved.

## At a glance

- Named paper items: 80.
- Definitions: 2.
- Named statements excluding definitions: 78.
- Fully formalized named statements: 58/78.
- Partially formalized statements: 14.
- Statements awaiting Lean formalization: 6.
- Labelled equations (equation-level checks, not additional named results): 15 (13 complete, 0 partial, 2 missing).
- Distinct mapped declarations across named items: 1457 (including definitions and helpers).

## Statements fully formalized in Lean

- **final:C0-placement** — Exact placed reconstruction
- **final:C1** — Curvature, Riccati and exact flow
- **final:C2** — Recentring transports its own regularity and anchors
- **final:C3** — Normalized group logarithm and cocycle
- **final:C3-completion** — Typed completion equation
- **final:C3-automorphisms** — Automorphisms, integer series and their calibration
- **final:C4** — Differentiable Bregman reconstruction
- **final:C5** — Exact Legendre target with either regularity condition
- **final:C6** — Self-concordance and the marked Hessian metric
- **final:C7** — Calibrated projective and Schwarzian data
- **final:C8** — Derivative, discrete and local-data boundaries
- **final:Z4** — Exact all-order derivative-zero sets do not identify $\Sigma$
- **final:P0-uniqueness** — Uniqueness principles for the transforms used below
- **final:P1** — Gamma law and complete transform characterizations
- **final:P1-samples** — Exponential samples also derive support
- **final:P1-boundaries** — Boundaries of moment identification
- **final:P2** — Marked Poisson recurrence, cumulants and divergences
- **final:P2-boundaries** — The centering mark and KL orientation are essential
- **final:P3** — Two marked max laws characterize the Gumbel CDF
- **final:P3-haar** — Haar weighting and Gumbel calibration boundaries
- **final:P4-data** — Canonical deficit law and coordinate involution
- **final:P4-cumulants** — Deficit transform, cumulants, and determinacy
- **final:P4** — The linked deficit law and involution identify the potential
- **final:P4-boundaries** — Neither linked observation alone suffices
- **final:P5** — Survival, hazard, logistic equation, and causal Green kernel
- **final:P5-survival-boundaries** — Precise survival boundaries and Gamma shift uniqueness
- **final:P5-stieltjes** — Probability Stieltjes transform and its inverse
- **final:P5-transforms** — Reverse size bias, equilibrium, and marked tilting
- **final:P5-equilibrium-fixed** — Equilibrium fixed points
- **final:P6** — Rooted coefficients, Borel probabilities, and the inverse germ
- **final:P6-boundaries** — Tree and continuation boundaries
- **final:P7** — The calibrated maximum-entropy characterization
- **final:P8-samples** — Complete integer tails identify the Gamma exponent
- **final:P8-selfdecomposition** — Explicit Gamma self-decomposition
- **final:P9** — One linked residual determines a law on the entire real line
- **final:O1** — The full-line weak Stein characterization
- **final:O1-kernel** — The integrable centered Stein kernel
- **final:O2** — Two marked probes and the Pearson realization
- **final:O2-boundaries** — The exact limits of the probe and stationary data
- **final:O3-spectrum** — The Laguerre basis and the exact integer spectrum
- **final:O7** — Complete marked Laguerre orthogonality identifies the law
- **final:O4** — Exact trace domains and reconstruction of the unitary class
- **final:O4-convergence-boundary** — Compact resolvent does not supply finite trace data
- **final:O4-heat-kernel** — The complete heat kernel relative to the invariant measure
- **final:O6** — A Bernstein function is determined by every integer tail
- **final:F1** — The normalized Todd tower and all its twists
- **final:F2** — Reversible characteristic-series formulas
- **final:F3** — Formal, analytic, and global recovery
- **final:M1** — The unique scalar-block spectral lift
- **final:M2** — Derivatives, divergence, duality, and determinant bounds
- **final:M4** — The supplied Gaussian and Wishart sampling model
- **final:R2** — Nonnegative orthogonal additivity without regularity
- **final:R3** — The profile-independent radial residual
- **final:R4** — Spatial countermodels retaining the complete intrinsic structure
- **final:B1** — Rational trees, Euclidean decoding, and the matrix monoid
- **final:B2** — Marked Farey branches and full-domain scalar recovery
- **final:B3** — Exact collisions and complete labelled arithmetic transport
- **final:B4** — Numerical Euler products and the full multiset inverse

## Exact formalized components and declaration mappings

### final:C0 — The placed presentation of $\Sigma$

Lean coverage: **definition**. [Paper statement](../paper/sections/core.tex#L8); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Placed formula, admissible parameter domain, marked affine coordinate and intrinsic coordinate.

Mapped Lean declarations:

- `Sigma.placedOriginal`
- `Sigma.placed`
- `Sigma.PlacedParameters`
- `Sigma.PlacedParameters.Admissible`
- `Sigma.Closure.Placement`

### final:C0-placement — Exact placed reconstruction

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L20); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Affine bijection and original formula; parameter and intrinsic recovery; intrinsic sign/exponential identities; closure derivatives; actual density pushforward and pullback; both masses; admissible placed presentation round trips.

Mapped Lean declarations:

- `Sigma.placed_coordinate_bijective`
- `Sigma.placed_original_identity`
- `Sigma.placed_parameter_recovery`
- `Sigma.placed_recover_offset`
- `Sigma.placed_recover_intrinsic`
- `Sigma.placed_closure`
- `Sigma.intrinsic_log_density`
- `SigmaPresentations.H_eq_neg_potential`
- `SigmaPresentations.density_eq_exp_H`
- `Sigma.intrinsic_density_integral_one`
- `Sigma.placed_density_affine_pushforward`
- `Sigma.placed_density_affine_pullback`
- `Sigma.placed_density_nonnegative_pushforward`
- `Sigma.placed_density_full_mass`
- `Sigma.placed_density_nonnegative_mass`
- `Sigma.placed_closed_nonnegative_ray_mass_one`
- `Sigma.PlacedParameters.presentationEquiv`
- `Sigma.PlacedParameters.presentationEquiv_roundtrip`

### final:C1 — Curvature, Riccati and exact flow

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L77); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Both differential equivalences, flow in both directions and anchored primitive, shifted curvature family, affine calibration and deletion witness.

Mapped Lean declarations:

- `Sigma.calibrated_curvature_iff`
- `Sigma.calibrated_riccati_iff`
- `Sigma.exact_flow_identifies`
- `Sigma.exact_flow_of_reciprocal`
- `Sigma.reconstruct_H`
- `Sigma.shifted_curvature_affine_family`
- `Sigma.affine_summand_two_data_unique`
- `Sigma.shiftedLogAffine_deriv`
- `Sigma.shiftedLogAffine_curvature`
- `Sigma.one_affine_datum_insufficient`

### final:C2 — Recentring transports its own regularity and anchors

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L107); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Only first differentiability and second derivative at one are assumed; global second derivative and both anchors are derived; converse and scale boundary are proved.

Mapped Lean declarations:

- `Sigma.recentering_iff`
- `Sigma.recentering_derivative_identity`
- `Sigma.recentering_transports_curvature`
- `Sigma.recentering_reconstruction`
- `Sigma.scaled_H_recentring`
- `Sigma.recentering_scale_calibration_necessary`

### final:C3 — Normalized group logarithm and cocycle

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L127); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Group equations and closure/inverse, logarithm/cocycle forward identities and uniqueness from derivative at identity alone.

Mapped Lean declarations:

- `SigmaBase.star_assoc`
- `SigmaBase.star_comm`
- `SigmaBase.star_zero`
- `SigmaBase.star_closed`
- `SigmaBase.invStar_closed`
- `SigmaBase.star_inverse`
- `SigmaBase.log_star`
- `SigmaBase.displacement_cocycle`
- `Sigma.group_log_derivative_from_identity`
- `Sigma.normalized_group_log_unique_at_identity`
- `Sigma.normalized_cocycle_unique_at_identity`

### final:C3-completion — Typed completion equation

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L154); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Exact K>0 family iff, derivative range, derived injectivity and second differentiability, both alternative anchors.

Mapped Lean declarations:

- `Sigma.typed_completion_iff_family`
- `Sigma.completion_derived_regularity`
- `Sigma.completionEll_strictMono`
- `Sigma.completionFamily_derivative_range`
- `Sigma.completionFamily_typed_equation`
- `Sigma.completionFamily_anchors_select_one`
- `Sigma.completion_value_anchor_identifies`
- `Sigma.completion_slope_anchor_identifies`

### final:C3-automorphisms — Automorphisms, integer series and their calibration

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L184); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Differentiable-at-zero endomorphism classification and nonzero slope under injectivity; explicit inverse/composition; natural repeated group addition.
- Continuous, measurable, monotone and antitone automorphism classification on the exact group domain D=(-1,infinity), with nonzero coefficient and the literal real-power formula. Measurability is required only on the domain subtype; automatic continuity of additive measurable maps is proved.
- Signed integer repeated group addition, including zero and negative indices, its literal integer-power formula and composition law; the derivative-at-zero calibration selects coefficient one and hence the identity.
- Every additive real bijection produces an actual group automorphism with two-sided inverse on D. A rational-linear projection supplies a genuinely nonlinear additive bijection and a conjugate group automorphism unequal to every real-power map.
- Over every characteristic-zero field, the full bivariate formal-group identity forces exactly the standard binomial power family, and every scalar in that family satisfies the full identity.
- Formal automorphisms are exactly the family members with nonzero scalar, using actual zero-constant two-sided compositional inverses; the tangent condition is derived from invertibility.
- Genuine formal substitution semantics, multiplication of parameters under composition, addition of parameters under the formal group law, native natural-power compatibility, unique parameter and tangent-one identity calibration.

Mapped Lean declarations:

- `Sigma.group_endomorphism_classification`
- `Sigma.group_automorphism_slope_nonzero`
- `Sigma.groupPower_composition`
- `Sigma.groupPower_inverse`
- `Sigma.groupPower_hom`
- `Sigma.groupPower_one`
- `Sigma.starN`
- `Sigma.groupPower_nat_nseries`
- `Sigma.groupPower_nat_nseries_hom`
- `Sigma.group_automorphism_continuous_classification`
- `Sigma.group_automorphism_monotone_classification`
- `Sigma.real_additive_measurable_continuous`
- `Sigma.group_automorphism_measurable_classification`
- `Sigma.groupPower_rpow`
- `Sigma.starZ`
- `Sigma.groupPower_int_nseries`
- `Sigma.starZ_formula`
- `Sigma.starZ_domain`
- `Sigma.starZ_composition`
- `Sigma.groupPower_hasDerivAt_zero`
- `Sigma.groupPower_calibration`
- `Sigma.nonlinear_additive_bijection`
- `Sigma.additiveConjugate`
- `Sigma.additive_conjugate_closed`
- `Sigma.additive_conjugate_hom`
- `Sigma.additive_conjugate_inverse`
- `Sigma.wild_group_automorphism`
- `Sigma.formalBinomialUnit`
- `Sigma.formalStarPower`
- `Sigma.formalStarPullback`
- `Sigma.IsFormalStarEndomorphism`
- `Sigma.formal_star_endomorphism_ode`
- `Sigma.formal_star_endomorphism_classification`
- `Sigma.formal_star_power_is_endomorphism`
- `Sigma.formal_star_endomorphism_iff`
- `Sigma.formal_binomial_unit_add`
- `Sigma.formal_binomial_unit_nat`
- `Sigma.formalCompose`
- `Sigma.formal_compose_monomial`
- `Sigma.formal_compose_polynomial`
- `Sigma.formal_star_pullback_X_pow`
- `Sigma.formal_star_pullback_locality`
- `Sigma.formal_star_power_composition`
- `Sigma.formal_star_power_inverse`
- `Sigma.IsFormalStarAutomorphism`
- `Sigma.formal_star_automorphism_classification`
- `Sigma.formal_star_automorphism_tangent_iff`
- `Sigma.formal_star_power_parameter_injective`
- `Sigma.formal_star_endomorphism_calibration`

### final:C4 — Differentiable Bregman reconstruction

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L214); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Differentiability-only affine-family iff, three calibrations, symmetric slice inverse, exact ratio divergence and calibration independence.

Mapped Lean declarations:

- `Sigma.bregman_scale_iff_affine_family`
- `Sigma.calibrated_scale_bregman_unique`
- `Sigma.anchored_symmetric_bregman_unique`
- `Sigma.affinePotential_bregman`
- `Sigma.affinePotential_scale`
- `Sigma.affinePotential_calibration`
- `Sigma.affinePotential_parameters_unique`
- `Sigma.bregman_three_calibrations_independent`

### final:C5 — Exact Legendre target with either regularity condition

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L248); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Actual full EReal supremum over all real primal coordinates, finite/infinite dual ranges including theta=1, either regularity condition alone, forced off-ray infinity, raised-point witness with unchanged full conjugate and neither regularity condition.

Mapped Lean declarations:

- `Sigma.extended_intrinsic_full_conjugate`
- `Sigma.extended_intrinsic_conjugate_infinite`
- `Sigma.exact_legendre_target_identifies`
- `Sigma.fenchel_candidate_off_positive`
- `Sigma.fenchel_convex_candidate_lower_semicontinuous`
- `Sigma.legendre_target_without_regularity_countermodel`

### final:C6 — Self-concordance and the marked Hessian metric

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L282); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Signed and unsigned C3 reconstruction on whole positive ray; Hessian metric distance via path lengths and a realizing path; symmetric divergence; metric-coordinate reconstruction; inversion orientation boundary; calibrated quadratic witness; absence of finite barrier parameter.

Mapped Lean declarations:

- `Sigma.self_concordance_signed_identifies`
- `Sigma.self_concordance_unsigned_identifies`
- `Sigma.sc_intrinsic_C3`
- `Sigma.sc_intrinsic_calibration`
- `Sigma.sc_intrinsic_signed_equality`
- `Sigma.sc_hessian_path_distance`
- `Sigma.scPathLength_eq_hessian_length`
- `Sigma.sc_native_hessian_path_distance`
- `Sigma.sc_symmetrization_distance`
- `Sigma.sc_anchored_curvature_reconstructs`
- `Sigma.sc_distance_inversion`
- `Sigma.sc_inversion_reverses_order`
- `Sigma.scQuadratic_calibrated_inequality`
- `Sigma.scQuadratic_not_intrinsic`
- `Sigma.sc_no_finite_barrier_parameter`

### final:C7 — Calibrated projective and Schwarzian data

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L314); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Calibrated projective and C3 Schwarzian inverse theorems with exact marks; forward models; anchored primitive; explicit uncalibrated counterexample.

Mapped Lean declarations:

- `Sigma.calibrated_cross_ratio_identifies`
- `Sigma.projectiveModel_preserves_cross_ratios`
- `Sigma.projectiveModel_three_marks`
- `Sigma.calibrated_schwarzian_identifies`
- `Sigma.projectiveModel_C3`
- `Sigma.projectiveModel_schwarzian_zero`
- `Sigma.projectiveModel_schwarzian_marks`
- `Sigma.projective_anchored_primitive_identifies`
- `Sigma.projectiveAffineCounter_preserves_cross_ratios`
- `Sigma.projectiveAffineCounter_schwarzian_data`
- `Sigma.projectiveAffineCounter_not_model`

### final:C8 — Derivative, discrete and local-data boundaries

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L341); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Actual placed logarithmic derivatives at all orders at least two; exponential placed-density derivatives and zero sets; two-index parameter identification; one-sided sequence uniqueness; analytic continuation from the density inverse germ.
- The independent-amplitude family C*(1+gamma*r)*exp(-mu*r) has the stated actual derivative at every positive integer order and its unique real zero n/mu-1/gamma for positive parameters. Two consecutive indexed zeros identify mu and gamma. Its positive-ray integral is C*(1/mu+gamma/mu^2), and equality of masses identifies C without assuming it was normalized in advance.
- Exact placed discrete-curvature formula on the complete stated domain r-1>-a/mu with mu>0; no extra offset restriction. Generic integer sequences are uniquely determined by two consecutive values and equal second differences on all integers.
- Half-lattice uniqueness from any consecutive anchor pair at or above its lower endpoint, requiring recurrence only where all three indices are admissible. For every real function a witness preserves every integer sample, differs by a smooth function, and differs at the positive point 1/4, inside every admissible placed domain since -a/mu<0.
- On every nonempty convex open real domain, equality of n-th derivatives is equivalent to a difference of the literal form sum over i<n of c_i*x^i. Only existence of successive derivatives of orders below n is required; continuity of the highest derivative is not assumed. Both implications are proved.
- For every observed point there exists a distinct positive, integrable, mass-one smooth density with the same germ and all iterated derivatives there, the same germ near the mode and zero endpoint, and equality on a far tail. The perturbation has compact support and its discrepancy is explicitly within the positive ray. Smoothness is ContDiff infinity, not analyticity.
- General analytic germ uniqueness is already supplied by imported Mathlib AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq, with analytic candidates on a preconnected common domain and equality near a domain point.

Mapped Lean declarations:

- `Sigma.placed_log_iteratedDeriv`
- `Sigma.placedLogDerivative_step`
- `Sigma.gamma_iteratedDeriv`
- `Sigma.gamma_exact_zeros`
- `Sigma.placed_density_iteratedDeriv`
- `Sigma.placed_density_exact_derivative_zero`
- `Sigma.affineExponentialDensity`
- `Sigma.affineExponentialDerivative`
- `Sigma.affine_exponential_iteratedDeriv`
- `Sigma.affine_exponential_exact_zero`
- `Sigma.affine_exponential_mass`
- `Sigma.affine_exponential_mass_identifies_amplitude`
- `Sigma.affine_exponential_indexed_zeros_identify`
- `Sigma.two_indexed_derivative_zeros_identify`
- `Sigma.second_difference_sequence_unique`
- `Sigma.log_second_difference`
- `Sigma.placed_discrete_curvature`
- `Sigma.second_difference_integer_sequence_unique`
- `Sigma.second_difference_half_lattice_unique`
- `Sigma.integer_samples_nonidentifying`
- `Sigma.equal_iteratedDeriv_polynomial_difference`
- `Sigma.polynomial_difference_equal_iteratedDeriv`
- `Sigma.equal_iteratedDeriv_iff_polynomial_difference`
- `Sigma.inverse_germ_identifies_analytic_density`
- `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`
- `Sigma.smooth_density_germ_nonidentification`
- `Sigma.smooth_density_same_jet_counterexample`

### final:Z4 — Exact all-order derivative-zero sets do not identify $\Sigma$

Lean coverage: **complete**. [Paper statement](../paper/sections/core.tex#L385); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Entire real k>1 family, exact formula and derivatives, positivity, analyticity, actual integral normalization, both endpoint limits, exact simple zeros and inequality to p; k=2 witness.

Mapped Lean declarations:

- `Sigma.zeroFamily_formula`
- `Sigma.zeroFamily_positive`
- `Sigma.zeroFamily_iteratedDeriv`
- `Sigma.zeroFamily_exact_zeros`
- `Sigma.zeroFamily_simple_zeros`
- `Sigma.zeroFamily_integrable`
- `Sigma.zeroFamily_mass_one`
- `Sigma.zeroFamily_tendsto_zero`
- `Sigma.zeroFamily_tendsto_infinity`
- `Sigma.zeroFamily_not_gamma`
- `Sigma.zeroFamily_analytic`
- `Sigma.gamma_iteratedDeriv`
- `Sigma.gamma_exact_zeros`
- `Sigma.zeroCounterdensity_mass_one`
- `Sigma.zeroCounterdensity_analytic`
- `Sigma.zeroCounterdensity_not_gamma`

### final:P0-uniqueness — Uniqueness principles for the transforms used below

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L17); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Finite compact moment uniqueness; nonnegative Laplace uniqueness; finite real-line characteristic uniqueness; local MGF uniqueness with exactly the required integrability neighborhood.

Mapped Lean declarations:

- `Sigma.operator_hausdorff_moment_unique`
- `Sigma.operator_nonnegative_mixing_measure_unique`
- `Sigma.finite_measure_characteristic_unique`
- `Sigma.finite_measure_local_mgf_unique`

### final:P1 — Gamma law and complete transform characterizations

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L47); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Native Gamma(2,1) probability, exact intrinsic density, support and absence of atoms.
- Complex Laplace and Mellin formulas on Re z > -1; characteristic function and all factorial moments.
- All four actual measure inverses, including real-line moment/characteristic candidates without positive-support assumptions.
- Actual mean, variance, expected logarithm and iterated-CGF-derivative cumulants.

Mapped Lean declarations:

- `Sigma.gamma_pdf_intrinsic`
- `Sigma.gamma_probability_normalized`
- `Sigma.gamma_probability_no_atom`
- `Sigma.gamma_probability_topological_support`
- `Sigma.gamma_complex_laplace`
- `Sigma.gamma_probability_characteristic`
- `Sigma.gamma_complex_mellin`
- `Sigma.gamma_probability_moments`
- `Sigma.operator_full_line_factorial_moment_unique`
- `Sigma.operator_full_line_mixing_characterization`
- `Sigma.gamma_characteristic_identifies_real_line_measure`
- `Sigma.imaginary_mellin_identifies_positive_probability`
- `Sigma.gamma_probability_mean`
- `Sigma.gamma_probability_variance`
- `Sigma.gamma_probability_expected_log`
- `Sigma.gamma_probability_log_integrable`
- `Sigma.gamma_probability_cumulants`

### final:P1-samples — Exponential samples also derive support

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L116); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Every integer exponential sample, including zero, identifies the actual finite real-line measure and derives strictly positive support.

Mapped Lean declarations:

- `Sigma.operator_full_line_mixing_characterization`
- `Sigma.operator_integer_samples_positive_support`

### final:P1-boundaries — Boundaries of moment identification

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L135); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Explicit actual finite positive measure gammaProbability+dirac 0 retains every strictly positive-order factorial moment and is distinct, proving necessity of the zeroth moment.
- A distinct finite signed measure is constructed as the Gamma signed measure plus an integrable continuous Lebesgue density whose every polynomial moment vanishes.
- For every finite cutoff m, a distinct positive probability measure has finite ordinary moments matching gammaProbability in every order n at most m.

Mapped Lean declarations:

- `Sigma.gamma_with_zero_atom_positive_moments`
- `Sigma.gamma_with_zero_atom_mass`
- `Sigma.gamma_with_zero_atom_distinct`
- `Sigma.positivity_removed_all_moments_counterexample`
- `Sigma.finite_moments_do_not_identify_gamma`

### final:P2 — Marked Poisson recurrence, cumulants and divergences

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L160); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Native PMF recurrence both ways and actual marked/unmarked CGF formulas and local probability-law inverses.
- All three native Radon-Nikodym entropy integrals, with absolute continuity and integrability independently proved, correct rate/variance orientation, and marked slices.
- Literal derivative-based Bregman formula and scalar log-coordinate reconstruction.
- Actual EReal supremum Legendre transform, including z=-1 and infinity for z<-1.

Mapped Lean declarations:

- `Sigma.poisson_probability_recurrence`
- `Sigma.poisson_one_recurrence`
- `Sigma.poisson_probability_cgf`
- `Sigma.poisson_centered_probability_cgf`
- `Sigma.poisson_local_cgf_identifies_real_line_law`
- `Sigma.marked_centered_poisson_local_cgf_identifies_law`
- `Sigma.centered_poisson_potential_in_log_coordinate`
- `Sigma.centered_poisson_reconstructs_potential`
- `Sigma.poisson_relative_entropy`
- `Sigma.exponential_relative_entropy`
- `Sigma.gaussian_relative_entropy`
- `Sigma.poisson_relative_entropy_slice`
- `Sigma.exponential_relative_entropy_slice`
- `Sigma.gaussian_relative_entropy_slice`
- `Sigma.poisson_relative_entropy_actual_bregman`
- `Sigma.poisson_potential_derivative`
- `Sigma.poisson_centered_conjugate_complete`

### final:P2-boundaries — The centering mark and KL orientation are essential

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L229); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual shifted natural-valued Poisson measures are distinct with the same mean-centered CGF.
- Actual entropy reversals have the stated different potentials, with explicit unequal values at two.

Mapped Lean declarations:

- `Sigma.shifted_poisson_mean`
- `Sigma.shifted_poisson_centered_cgf`
- `Sigma.shifted_poisson_not_original`
- `Sigma.reversed_poisson_entropy_slice`
- `Sigma.reversed_exponential_entropy_slice`
- `Sigma.reversed_gaussian_entropy_slice`
- `Sigma.poisson_entropy_reversal_distinct`
- `Sigma.exponential_entropy_reversal_distinct`
- `Sigma.gaussian_entropy_reversal_distinct`

### final:P3 — Two marked max laws characterize the Gumbel CDF

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L246); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Two marked max equations and anchor imply Gumbel from monotonicity alone; canonical probability, density and endpoint limits are proved.
- Converse and all positive integer max identities.

Mapped Lean declarations:

- `Sigma.gumbel_two_max_laws_unique`
- `Sigma.gumbel_two_max_probability_unique`
- `Sigma.gumbel_cdf_continuous`
- `Sigma.gumbel_cdf_tendsto_atTop`
- `Sigma.gumbel_cdf_tendsto_atBot`
- `Sigma.gumbel_probability_density`
- `Sigma.gumbel_density_intrinsic`
- `Sigma.gumbel_max_law`

### final:P3-haar — Haar weighting and Gumbel calibration boundaries

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L282); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual coordinate pushforward and normalized Haar-weighted density; scale invariance and infinite Haar mass.
- Marked density and measure reconstruction and actual probability counterexamples for removing the anchor or retaining only base two.

Mapped Lean declarations:

- `Sigma.gumbel_coordinate_pushforward`
- `Sigma.positive_haar_weighted_probability`
- `Sigma.positive_haar_density_integral`
- `Sigma.positive_haar_scale`
- `Sigma.positive_haar_infinite`
- `Sigma.positive_haar_recovers_gamma`
- `Sigma.marked_gumbel_density_identifies`
- `Sigma.positive_haar_probability_identifies`
- `Sigma.gumbel_without_anchor_counterexample`
- `Sigma.gumbel_base_two_counterexample`
- `Sigma.gamma_probability_ne_haar_weighted`

### final:P4-data — Canonical deficit law and coordinate involution

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L313); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual deficit pushforward CDF and withDensity equality; no atom at zero; exact Lambert branches and density for positive levels.
- Native asymptotic equivalence with sqrt(2)/(e sqrt(v)).
- Canonical positive-ray involution, strict decrease, smoothness including joining point, derivative -1, fixed point and preserved potential/density.

Mapped Lean declarations:

- `Sigma.canonical_deficit_cdf`
- `Sigma.gamma_deficit_cdf_negative`
- `Sigma.gamma_deficit_no_atom_at_zero`
- `Sigma.canonical_deficit_roots_lambert`
- `Sigma.gamma_deficit_cdf_lambert`
- `Sigma.gamma_deficit_probability_density`
- `Sigma.gamma_deficit_cdf_derivative`
- `Sigma.gamma_deficit_density_equivalent`
- `Sigma.canonical_deficit_involution_lambert_lower`
- `Sigma.canonical_deficit_involution_lambert_upper`
- `Sigma.canonical_deficit_involution_smooth`
- `Sigma.canonical_deficit_involution_derivative_one`
- `Sigma.canonical_deficit_involution_strictAnti`
- `Sigma.canonical_deficit_involution_involutive`
- `Sigma.canonical_deficit_involution_fixed_point`
- `Sigma.canonical_deficit_involution_preserves_density`

### final:P4-cumulants — Deficit transform, cumulants, and determinacy

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L375); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual deficit MGF and sharp real integrability domain s<1.
- Moment determinacy derives candidate exponential integrability; common algebraic cumulant recurrence determines moments.
- Actual conditional probability and exact upper-incomplete-Gamma transform for a>0,s<1.
- Convergent Euler log-Gamma product and absolutely convergent double-series exchange for every |s|<1, including negative s.
- Exact Euler/zeta series of the actual deficit CGF, with natural zeta identified with native riemannZeta.
- Actual iterated-derivative cumulants in every positive order, including Euler's constant at order one and all displayed second, third and fourth cumulant values.
- The actual centered variance integral equals the second cumulant, pi^2/6-1.
- The explicit Euler/zeta cumulant sequence satisfies the target algebraic recurrence, and any probability law with all finite moments satisfying that recurrence equals the deficit law without an exponential-moment premise.

Mapped Lean declarations:

- `Sigma.gamma_deficit_mgf`
- `Sigma.gamma_deficit_exponential_integrable`
- `Sigma.gamma_deficit_mgf_integrable_iff`
- `Sigma.gamma_deficit_moments_identify_real_line_probability`
- `Sigma.gamma_deficit_algebraic_cumulants_identify`
- `Sigma.gamma_deficit_conditional_transform`
- `Sigma.gamma_deficit_conditional_exponential_integrable`
- `Sigma.log_gamma_euler_product`
- `Sigma.euler_log_gamma_term_series`
- `Sigma.euler_log_gamma_double_summable`
- `Sigma.natural_zeta_riemann`
- `Sigma.log_gamma_zeta_series`
- `Sigma.deficit_cgf_log_gamma`
- `Sigma.deficit_cgf_zeta_series`
- `Sigma.deficit_cgf_full_series`
- `Sigma.deficit_cgf_formal_germ`
- `Sigma.deficit_cumulant_coeff`
- `Sigma.deficit_cumulant_one`
- `Sigma.deficit_cumulant_zeta`
- `Sigma.natural_zeta_two`
- `Sigma.natural_zeta_four`
- `Sigma.deficit_cumulants_two_three_four`
- `Sigma.deficit_mgf_formal_germ`
- `Sigma.gamma_deficit_algebraic_cumulant_recurrence`
- `Sigma.deficitCumulantValue`
- `Sigma.gamma_deficit_explicit_algebraic_cumulant_recurrence`
- `Sigma.gamma_deficit_explicit_algebraic_cumulants_identify`
- `Sigma.gamma_deficit_mean`
- `Sigma.gamma_deficit_second_moment`
- `Sigma.gamma_deficit_variance`

### final:P4 — The linked deficit law and involution identify the potential

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L440); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Full actual law-and-involution uniqueness in the continuous ray-only two-branch class, without differentiability, density of deficit or extra pairing monotonicity assumptions.
- Concrete canonical target and converse supplied by the canonical pairing and linked-density theorems.
- The complete explicit Euler/zeta algebraic cumulant list may replace deficit-law equality, with no candidate exponential-moment assumption.

Mapped Lean declarations:

- `Sigma.linked_deficit_and_involution_unique_on_positive_ray`
- `Sigma.canonical_deficit_pair_identifies_on_positive_ray`
- `Sigma.canonical_linked_density_measure`
- `Sigma.rayDeficitLaw`
- `Sigma.canonical_deficit_pair_identifies_from_explicit_cumulants`

### final:P4-boundaries — Neither linked observation alone suffices

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L484); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual upper-branch source probability has the same deficit law and differs from Gamma.
- A nonzero smooth common-level coordinate shift gives a genuinely noncanonical two-branch potential with all anchor and endpoint conditions. Equal widths imply equality of actual linked deficit measures; normalization and real density integrability are derived. Its canonical pairing differs.
- A balanced zero-mean level perturbation gives an explicit increasing reparametrization fixing zero. The resulting noncanonical two-branch potential has a normalized actual linked probability, preserves the canonical involution at every positive point, and has a different actual deficit law.

Mapped Lean declarations:

- `Sigma.upper_branch_source_counterexample`
- `Sigma.upper_branch_potential_probability`
- `Sigma.upper_branch_Ici_one`
- `Sigma.gamma_Ici_one_lt_one`
- `Sigma.deficit_level_shift_orderIso`
- `Sigma.shifted_deficit_potential_two_branch`
- `Sigma.shifted_deficit_roots_and_width`
- `Sigma.equal_widths_level_measure`
- `Sigma.equal_widths_linked_deficit_law`
- `Sigma.linked_probability_real_normalization`
- `Sigma.canonical_deficit_law_does_not_identify_potential`
- `Sigma.involution_counterpotential_two_branch`
- `Sigma.involution_counterpotential_density_integrable`
- `Sigma.involution_counterpotential_density_mass`
- `Sigma.involution_counterprobability_is_probability`
- `Sigma.involution_counterpotential_pair`
- `Sigma.involution_counterpotential_noncanonical`
- `Sigma.involution_counterpotential_deficit_law_ne`
- `Sigma.canonical_involution_does_not_identify_linked_density`

### final:P5 — Survival, hazard, logistic equation, and causal Green kernel

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L533); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- All survival/hazard/shift/potential formulas; differentiable hazard inverse; global logistic ODE inverse without an assumed range.
- Complete normalized second-order classical ODE inverse and actual independent exponential-sum Gamma law.
- The explicit causal kernels k(t)=1_{[0,∞)}e^{-t} and g(t)=1_{[0,∞)}te^{-t} satisfy the actual whole-line convolution identity k*k=g for every real t, including the zero and negative-time cases.
- The regular distribution defined by integration against the exact whole-line causal kernel g(t)=1_[0,∞)(t)t exp(-t) satisfies (D+1)^2 g=δ₀ with standard distributional differentiation and exact Dirac normalization. It is the unique causal distributional solution: uniqueness is proved on the larger class of all algebraic linear functionals on C∞_c(R) satisfying the support condition and equation. The witness has a proved L1 pairing bound, and the existing whole-line k*k identity is reused.
- Local absolute continuity plus the a.e. hazard ODE derives an everywhere derivative and the anchored survival formula, without a derivative assumption at zero.
- Native probability measures with that local-AC survival and a.e. ODE are identified through actual CDF equality; endpoint continuity is derived from native survival right continuity, and the marked logistic equation transfers to this same inverse.
- The exact native absolutely continuous probability input now suffices: the Radon-Nikodym density yields the actual tail integral and continuity; the actual a.e. hazard and positive tail derive a continuous density representative, tail derivatives and local absolute continuity, and hence equality of the supplied measure with gammaProbability. The marked logistic inverse permits any differentiable marked hazard linked a.e. to the actual Radon-Nikodym density/survival ratio.
- The actual unit-rate Poisson counting process is constructed on the infinite product probability space using the standard iid-Exp(1) interarrival characterization. Its full independent clock family, exponential marginals, cumulative arrival epochs, measurable monotone counts, and almost-sure non-explosion/local finiteness are proved. The actual index-1 (second) arrival is the sum of the first two constructed clocks and has law gammaProbability; the at-most-one-arrival probability has the exact Gamma survival formula.

Mapped Lean declarations:

- `Sigma.gamma_probability_tail`
- `Sigma.gamma_survival_tail_integral`
- `Sigma.gamma_hazard_ratio`
- `Sigma.gamma_self_survival_shift`
- `Sigma.gamma_survival_potential`
- `Sigma.gamma_hazard_unique_differentiable`
- `Sigma.logistic_hazard_unique`
- `Sigma.normalized_second_order_density_unique`
- `Sigma.exponential_pair_convolution`
- `Sigma.causal_unit_exponential_convolution_eq_gamma_green`
- `Sigma.p5DistributionGreenOperator_apply`
- `Sigma.p5_causal_green_pairing_eq_dirac`
- `Sigma.p5_causal_green_distributional_equation`
- `Sigma.p5_causal_distribution_green_unique`
- `Sigma.p5_causal_distribution_green_exists_unique`
- `Sigma.causalGammaGreen_eq_indicator`
- `Sigma.p5_causal_regular_distribution_green_exists_unique`
- `Sigma.p5_causal_regular_distribution_green_representation`
- `Sigma.independent_exponential_pair_gamma`
- `Sigma.poisson_exponential_clock_map`
- `Sigma.poisson_unit_rate_interarrival_law`
- `Sigma.unit_rate_poisson_process_interarrival_law`
- `Sigma.poisson_renewal_arrival_measurable`
- `Sigma.poisson_renewal_arrivals_monotone`
- `Sigma.poisson_renewal_arrivals_tendsto_top_ae`
- `Sigma.unit_rate_poisson_count_le_iff`
- `Sigma.unit_rate_poisson_process_count_measurable`
- `Sigma.unit_rate_poisson_process_count_finite_ae`
- `Sigma.unit_rate_poisson_process_count_monotone`
- `Sigma.unit_rate_poisson_process_exponential_interarrival_construction`
- `Sigma.poisson_renewal_second_arrival_eq`
- `Sigma.poisson_renewal_second_arrival_gamma_law`
- `Sigma.unit_rate_poisson_process_second_arrival_law`
- `Sigma.unit_rate_poisson_at_most_one_event`
- `Sigma.unit_rate_poisson_at_most_one_arrival_probability`
- `Sigma.local_ac_continuous_rhs_hasDerivAt`
- `Sigma.gamma_hazard_local_ac_derivative`
- `Sigma.gamma_hazard_unique_local_ac`
- `Sigma.gamma_probability_local_ac_hazard_inverse`
- `Sigma.gamma_probability_local_ac_logistic_inverse`
- `Sigma.lifetime_density_integrable`
- `Sigma.ac_lifetime_survival_increment`
- `Sigma.ac_lifetime_survival_continuous`
- `Sigma.ac_lifetime_survival_derivative`
- `Sigma.ac_lifetime_survival_local_ac_of_density`
- `Sigma.gamma_probability_native_hazard_inverse`
- `Sigma.gamma_probability_native_marked_logistic_inverse`
- `Sigma.gamma_probability_native_logistic_inverse`

### final:P5-survival-boundaries — Precise survival boundaries and Gamma shift uniqueness

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L599); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual atom-at-zero anchor counterexample, actual logarithmic pushforward hazard/Jacobian distinction.
- Full native Gamma self-survival-shift iff for every positive shape, rate and shift.
- A genuine atomless probability on the native null Cantor set supplies a continuous monotone singular function with derivative zero almost everywhere. Its survival perturbation defines an actual atomless positive-supported probability, distinct from Gamma, with strictly decreasing continuous positive survival, anchor one, limit zero, and exactly the Gamma hazard and logarithmic-derivative equations almost everywhere. Failure of local integral absolute continuity is derived.

Mapped Lean declarations:

- `Sigma.gamma_hazard_anchor_counterexample`
- `Sigma.log_gamma_probability_density`
- `Sigma.log_gamma_actual_hazard`
- `Sigma.log_gamma_hazard_ne_composition`
- `Sigma.gamma_self_shift_iff`
- `Sigma.volume_cantorSet_zero`
- `Sigma.cantor_probability_exists`
- `Sigma.atomless_probability_cdf_continuous`
- `Sigma.singular_shifted_cdf_derivative_zero_ae`
- `Sigma.continuous_singular_function_exists`
- `Sigma.singular_survival_actual_tail`
- `Sigma.singular_survival_not_local_ac`
- `Sigma.gamma_hazard_regularity_counterexample`

### final:P5-stieltjes — Probability Stieltjes transform and its inverse

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L657); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Exact Gamma Stieltjes integral and identification among finite positive supported measures from any nonempty positive open set.
- Smooth complete monotonicity of Laplace transform; exclusion of a general Stieltjes representation allowing infinite representing measure; density and survival fail complete monotonicity.

Mapped Lean declarations:

- `Sigma.gamma_stieltjes_integral_formula`
- `Sigma.expIntegralOne_shift`
- `Sigma.probability_stieltjes_unique_on_open_set`
- `Sigma.probability_stieltjes_unique_on_interval`
- `Sigma.gamma_stieltjes_identifies`
- `Sigma.gamma_laplace_smooth`
- `Sigma.gamma_laplace_completely_monotone`
- `Sigma.gamma_laplace_not_stieltjes`
- `Sigma.intrinsic_density_not_completely_monotone`
- `Sigma.gamma_survival_not_completely_monotone`

### final:P5-transforms — Reverse size bias, equilibrium, and marked tilting

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L707); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual size-biased and equilibrium probabilities with normalization and exact positive-lifetime inverses; real reciprocal means and inverse existence.
- Equilibrium survival ratios recovered pointwise including zero from equality of output laws, without input density; Gamma target identification.
- Actual marked real tilt inverse, Gamma admissible domain including endpoint divergence, native rate change, cumulants, mean and variance.
- Explicit zero-atom boundary witnesses for both lifetime transforms and distinct input rates sharing unmarked tilted output.

Mapped Lean declarations:

- `Sigma.normalized_weight_is_probability`
- `Sigma.positive_size_bias_reciprocal_mean_real`
- `Sigma.positive_size_bias_inverse_exists`
- `Sigma.positive_size_bias_inverse_real`
- `Sigma.gamma_size_bias_identifies_positive_exponential`
- `Sigma.zero_atom_size_bias_counterexample`
- `Sigma.equilibrium_measure_probability`
- `Sigma.lifetime_survival_antitone`
- `Sigma.lifetime_survival_right_continuous`
- `Sigma.equilibrium_equal_survival_ratios`
- `Sigma.equilibrium_positive_inverse`
- `Sigma.gamma_equilibrium_density`
- `Sigma.gamma_equilibrium_identifies`
- `Sigma.equilibrium_atom_zero_counterexample`
- `Sigma.marked_exponential_tilt_inverse_real`
- `Sigma.gamma_rate_tilt_admissible_iff`
- `Sigma.gamma_rate_marked_tilt`
- `Sigma.gamma_tilt_cumulants`
- `Sigma.gamma_tilt_mean_variance`
- `Sigma.gamma_unmarked_tilt_counterexample`

### final:P5-equilibrium-fixed — Equilibrium fixed points

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L784); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Full actual positive-lifetime fixed-point iff native exponential with reciprocal actual mean.
- Continuity and survival equation derived from fixed-point equality, not assumed.

Mapped Lean declarations:

- `Sigma.equilibrium_fixed_integral_equation`
- `Sigma.equilibrium_fixed_survival_continuous`
- `Sigma.equilibrium_fixed_survival_derivative`
- `Sigma.equilibrium_fixed_survival`
- `Sigma.equilibrium_fixed_iff_exponential`
- `Sigma.equilibrium_fixed_points`

### final:P6 — Rooted coefficients, Borel probabilities, and the inverse germ

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L798); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Unique formal rooted series, all power coefficients including n=k, convergence radius e^-1 and two-sided inverse analytic germ.
- Native Borel PMF normalization, marked PGF and functional equation including B(1)=1.
- Every supplied finite family of measurable Borel variables on an arbitrary probability space, with native joint independence and the specified marginal laws, has the constructed forest sum law and the displayed actual event probabilities for n>=k>=1, including n=k.
- Marked inverse scaling and global identity theorem for an analytic density agreeing with the inverse germ on a positive neighborhood.

Mapped Lean declarations:

- `Sigma.rooted_series_exists_unique`
- `Sigma.rooted_power_coefficients`
- `Sigma.rooted_series_coefficients`
- `Sigma.rooted_series_convergence_radius`
- `Sigma.rooted_inverse_analytic_germs`
- `Sigma.borel_coefficient_formula`
- `Sigma.borel_coefficients_sum_one`
- `Sigma.borel_generating_rescaled_rooted`
- `Sigma.borel_generating_fixed_point`
- `Sigma.borel_generating_one`
- `Sigma.marked_borel_inverse_scale`
- `Sigma.borel_inverse_analytic_germs`
- `Sigma.borel_independent_forest_probabilities`
- `Sigma.independent_nat_sum_measure`
- `Sigma.independent_nat_sum_law`
- `Sigma.borel_independent_finset_law`
- `Sigma.borel_independent_sum_probabilities`
- `Sigma.inverse_germ_identifies_analytic_density`

### final:P6-gw — Borel total size identifies a one-ancestor iid GW law

Lean coverage: **partial**. [Paper statement](../paper/sections/probability.tex#L872); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual offspring PMF is Poisson iff its PGF satisfies the Borel conditioning equation.

Mapped Lean declarations:

- `Sigma.native_pgf_identifies_nat_probability`
- `Sigma.offspring_pgf_equation_identifies_poisson`
- `Sigma.poisson_offspring_pgf_equation`
- `Sigma.native_offspring_pgf_characterization`

Remaining Lean formalization:

- Native one-ancestor iid Galton-Watson construction and derivation of the conditioning equation from independence/tree construction.
- Poisson critical extinction/finite total size and identification of its actual total-size law.
- Converse from the observed actual total-size Borel law, and uniqueness of the full tree law within the construction.

### final:P6-boundaries — Tree and continuation boundaries

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L906); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual rooted path/star PMF countermodels have identical Borel size and distinct tree laws.
- Native Stirling asymptotics give the exact Borel PMF leading term (2*pi)^(-1/2)*n^(-3/2). A normalized PMF transfers half of the mass at 2 to 1, remains positive at every positive integer and zero at 0, agrees with Borel for every n >= 3, defines a distinct actual probability measure, and retains the exact same leading tail.
- A nonzero derivative bump supported strictly inside (2,3) gives a genuinely distinct smooth positive probability density with both exact inverse germs, the canonical unique maximum, strict two-branch shape, and both endpoint limits. Zero perturbation integral, positive normalization and all shape bounds are derived; distinction holds up to almost-everywhere equality.
- An actual iid constant-one offspring array has mean one and non-Poisson law. Its usual active-word recursion derives the infinite unary rooted tree with exactly one vertex per generation and one child per active vertex. The actual total-progeny pushforward is the probability mass at infinity, distinct from the native finite Borel law.

Mapped Lean declarations:

- `Sigma.borel_path_size_law`
- `Sigma.borel_star_size_law`
- `Sigma.borel_tree_laws_distinct`
- `Sigma.borel_size_does_not_identify_random_tree`
- `Sigma.borel_coefficient_stirling_ratio`
- `Sigma.borel_coefficient_scaled_limit`
- `Sigma.borel_tail_asymptotic_rpow`
- `Sigma.borel_tail_perturbation_positive`
- `Sigma.borel_tail_perturbation_hasSum`
- `Sigma.borel_tail_perturbation_eq`
- `Sigma.borel_tail_perturbation_distinct`
- `Sigma.borel_tail_perturbation_probability_distinct`
- `Sigma.borel_tail_does_not_identify_probability`
- `Sigma.smooth_inverse_germ_density_boundary`
- `Sigma.criticalLineProbability`
- `Sigma.criticalLineOffspring`
- `Sigma.criticalLineActive`
- `Sigma.critical_line_active_replicate`
- `Sigma.critical_line_one_vertex_each_generation`
- `Sigma.critical_line_one_child`
- `Sigma.criticalLineTotalProgeny`
- `Sigma.critical_line_total_progeny_infinite`
- `Sigma.criticalLineTotalProgenyLaw`
- `Sigma.extendedBorelTotalProgenyLaw`
- `Sigma.critical_iid_galton_watson_boundary`

### final:P7 — The calibrated maximum-entropy characterization

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L942); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Exact mean/log-mean/log-integrability constraints and actual Gamma calibration.
- Extended entropy bound including minus infinity, exact equality iff a.e. canonical density, canonical entropy value, and agreement with the ordinary entropy integral for every finite-extended-entropy candidate; f log f integrability is derived from finite divergence.
- Also supplies a smooth positive calibrated counterdensity, a.e. distinction, and strict entropy inequality.

Mapped Lean declarations:

- `Sigma.gamma_density_calibrated`
- `Sigma.gamma_extended_entropy_value`
- `Sigma.calibrated_gamma_maximum_entropy`
- `Sigma.calibrated_gamma_finite_entropy`
- `Sigma.CalibratedGammaDensity.entropy_integrable_of_divergence_ne_top`
- `Sigma.CalibratedGammaDensity.finite_extended_entropy_formula`
- `Sigma.calibrated_gamma_finite_extended_entropy`
- `Sigma.gamma_density_entropy_integral`
- `Sigma.entropy_counterdensity_calibrated`
- `Sigma.entropy_counterdensity_contDiff`
- `Sigma.entropy_counterdensity_not_ae_gamma`
- `Sigma.entropy_counterdensity_strict_entropy`

### final:P8 — Unique probability convolution completion

Lean coverage: **partial**. [Paper statement](../paper/sections/probability.tex#L977); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual family Gamma(2r,1), including Dirac at r=0, with convolution law and transforms.
- Uniqueness among all nonnegative probability semigroups from the time-one Gamma law without an assumed continuity hypothesis.
- Derived continuity of the actual family in the native ProbabilityMeasure weak topology, including convergence to Dirac zero at time zero.
- Actual finite product increment laws and partial-sum probability laws; uniqueness of every supplied process's finite-dimensional distributions at arbitrary finite observation times, including unordered, repeated, zero and empty observations. Gamma increment laws are derived from the time-one Gamma law and stationary independent nonnegative increments with starting value zero, without a regularity premise.
- Proof-only correlated-process boundary: the actual measurable nonnegative process X_r=rT starts at zero, has Gamma time-one law and stationary increments, but its disjoint unit increments are not independent.

Mapped Lean declarations:

- `Sigma.gammaCompletion`
- `Sigma.gamma_completion_zero`
- `Sigma.gamma_completion_positive`
- `Sigma.gamma_completion_probability`
- `Sigma.gamma_completion_nonnegative`
- `Sigma.gamma_completion_one`
- `Sigma.gamma_completion_laplace_rpow`
- `Sigma.gamma_completion_native_convolution`
- `Sigma.gamma_completion_unique`
- `Sigma.gamma_probability_convolution_completion`
- `Sigma.gammaCompletionProbability`
- `Sigma.normalized_density_tendsto_l1`
- `Sigma.nonnegative_probability_tendsto_dirac`
- `Sigma.gamma_completion_continuousAt_positive`
- `Sigma.gamma_completion_continuousAt_zero`
- `Sigma.gamma_completion_weak_continuous`
- `Sigma.independent_finite_joint_law`
- `Sigma.gammaCompletionFiniteLaw`
- `Sigma.gamma_completion_finite_law_probability`
- `Sigma.gamma_completion_finite_joint_law`
- `Sigma.HasIndependentNonnegativeTimeIncrements`
- `Sigma.stationary_independent_process_gamma_marginals`
- `Sigma.gamma_completion_process_fdd_unique`
- `Sigma.finite_nonnegative_times_ordered_cover`
- `Sigma.process_fdd_eq_of_ordered`
- `Sigma.IsGammaTimeOneProcess`
- `Sigma.gamma_time_one_process_fdd_unique`
- `Sigma.gammaSingleVariableProcess`
- `Sigma.gamma_single_variable_measurable`
- `Sigma.gamma_single_variable_time_one`
- `Sigma.gamma_single_variable_zero`
- `Sigma.gamma_single_variable_nonnegative`
- `Sigma.gamma_single_variable_stationary_increments`
- `Sigma.gamma_coordinate_not_independent_of_itself`
- `Sigma.gamma_single_variable_dependent_unit_increments`
- `Sigma.gamma_single_variable_not_independent_increments`

Remaining Lean formalization:

- Consistency of the prescribed finite-dimensional laws and construction of an actual global stationary independent-increment process starting at zero via a probability extension argument.

### final:P8-levy — Gamma L\'evy measure, drift, and complete Bernstein structure

Lean coverage: **partial**. [Paper statement](../paper/sections/probability.tex#L1021); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual Levy-exponent improper integral, exponential mixture representation of the density, complete-Bernstein scalar rational integral and exponent derivative.
- Actual positive-supported Gamma Levy measure and its Levy integrability; smooth complete monotonicity of its density, complete-Bernstein representation of the exponent, and actual Stieltjes derivative representation by twice the Dirac measure at one.
- The scalar drifted exponent has asymptotic ratio d, so zero drift is equivalent to a zero asymptotic ratio.
- Actual shifted time-one probabilities have support [d,infinity), support infimum d and mean d+2. Probability normalization excludes killing, and the four drift/ratio/support/mean tests are equivalent and identify the whole marginal convolution semigroup.
- Actual distinct nonnegative-drift convolution families have the same actual Levy measure. For supplied stationary independent nonnegative-increment processes, native independence and stationarity derive convolution; the linked Levy representation implies the four tests and canonical marginal family, without assuming a Gamma time-one law.
- Adding deterministic drift to any supplied Gamma process preserves stationary independent increments and gives the actual gammaDriftCompletion marginals, furnishing the conditional process-level drift freedom.

Mapped Lean declarations:

- `Sigma.gamma_levy_exponent_integral`
- `Sigma.gamma_levy_exponent_integrable`
- `Sigma.gamma_levy_complete_monotone_representation`
- `Sigma.log_complete_bernstein_integral`
- `Sigma.gamma_exponent_derivative`
- `Sigma.gammaLevyDerivativeMajorant`
- `Sigma.gamma_levy_derivative_majorant_hasDerivAt`
- `Sigma.gamma_levy_iterated_derivative`
- `Sigma.gamma_levy_density_completely_monotone`
- `Sigma.gamma_levy_density_smooth`
- `Sigma.gamma_levy_completely_monotone`
- `Sigma.gamma_exponent_derivative_stieltjes`
- `Sigma.HasCompleteBernsteinRepresentation`
- `Sigma.gamma_exponent_complete_bernstein`
- `Sigma.gamma_exponent_sublinear`
- `Sigma.gamma_drifted_exponent_ratio`
- `Sigma.gamma_drift_zero_iff_sublinear`
- `Sigma.gammaCompletionLevyMeasure`
- `Sigma.gamma_completion_levy_positive_support`
- `Sigma.gamma_completion_levy_integrability`
- `Sigma.gamma_bernstein_representation_exponent`
- `Sigma.gammaDriftedProbability`
- `Sigma.gamma_drifted_probability_mean`
- `Sigma.gamma_drifted_probability_support`
- `Sigma.gamma_drifted_probability_support_infimum`
- `Sigma.gamma_drifted_probability_laplace`
- `Sigma.gamma_drifted_probability_unique`
- `Sigma.bernstein_probability_excludes_killing`
- `Sigma.probability_with_gamma_levy_is_shifted_gamma`
- `Sigma.gamma_levy_drift_characterization`
- `Sigma.gammaDriftCompletion`
- `Sigma.gamma_drift_completion_zero`
- `Sigma.gamma_drift_completion_one`
- `Sigma.gamma_drift_completion_nonnegative`
- `Sigma.gamma_drift_completion_convolution`
- `Sigma.gammaDriftBernsteinRepresentation`
- `Sigma.gamma_drift_completion_levy_representation`
- `Sigma.gamma_drift_completions_distinct`
- `Sigma.stationary_independent_process_convolution`
- `Sigma.subordinator_gamma_levy_drift_characterization`
- `Sigma.addProcessDrift`
- `Sigma.process_drift_preserves_independence`
- `Sigma.process_drift_preserves_stationarity`
- `Sigma.drifted_gamma_process_witness`

Remaining Lean formalization:

- Nonvacuous global subordinator realization of the Gamma and drifted families, sharing P8's actual process existence/extension dependency; the usual increasing right-continuous realization is not yet constructed.

### final:P8-samples — Complete integer tails identify the Gamma exponent

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L1075); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Gamma specialization of full integer-tail uniqueness in the literal Bernstein representation category, for every natural tail index including zero, with no supplied value at zero; the conclusion includes every nonnegative real argument.
- Actual finite moment measure construction and full killing, drift and Levy measure recovery, with the Gamma target's Levy integrability and representation proved.

Mapped Lean declarations:

- `Sigma.BernsteinRepresentation`
- `Sigma.HasBernsteinRepresentation`
- `Sigma.BernsteinRepresentation.kernel_integrable`
- `Sigma.BernsteinRepresentation.increment_laplace`
- `Sigma.BernsteinRepresentation.integer_tail_data_unique`
- `Sigma.BernsteinRepresentation.integer_tail_unique`
- `Sigma.bernstein_function_integer_tail_unique`
- `Sigma.gammaCompletionLevyMeasure`
- `Sigma.gamma_completion_levy_integrability`
- `Sigma.gamma_bernstein_representation_exponent`
- `Sigma.gamma_laplace_exponent_has_bernstein_representation`
- `Sigma.gamma_bernstein_integer_tail_unique`
- `Sigma.gamma_bernstein_function_integer_tail_unique`

### final:P8-selfdecomposition — Explicit Gamma self-decomposition

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L1091); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- Actual nonnegative residual law, exact rational Laplace transform and zero-atom mass; independent Gamma self-decomposition for 0<c<1 (also endpoints where appropriate).
- For 0<c<=1 the exact displayed candidate jump density 2*(exp(-x)-exp(-x/c))/x is nonnegative on the positive ray, genuinely integrable there, and its integral is -2*log c. Its actual restricted-Lebesgue withDensity measure is finite and has total mass ENNReal.ofReal (-2*log c).
- The actual residual law is the native Poisson mixture of convolution powers of a normalized jump law, and rate times that jump law is exactly the displayed Levy measure.
- Gamma is infinitely divisible, while Gamma(4,1) and Gamma(2,2) each have native convolution roots and independent self-decompositions and differ from the canonical Gamma(2,1).

Mapped Lean declarations:

- `Sigma.gamma_residual_probability`
- `Sigma.gamma_residual_nonnegative`
- `Sigma.gamma_residual_laplace`
- `Sigma.gamma_residual_zero_atom`
- `Sigma.gamma_canonical_self_decomposition`
- `Sigma.gammaResidualLevyDensity`
- `Sigma.gamma_residual_levy_density_factor`
- `Sigma.gamma_residual_levy_density_nonnegative`
- `Sigma.gamma_residual_levy_integrable`
- `Sigma.gamma_residual_levy_integral`
- `Sigma.gammaResidualLevyMeasure`
- `Sigma.gamma_residual_levy_measure_mass`
- `Sigma.gamma_residual_levy_measure_finite`
- `Sigma.poissonConvolutionLaw`
- `Sigma.gamma_residual_compound_poisson`
- `Sigma.gamma_residual_jump_intensity_measure`
- `Sigma.gamma_probability_infinitely_divisible`
- `Sigma.gamma_shape_four_identification`
- `Sigma.gamma_shape_four_infinitely_divisible`
- `Sigma.gamma_shape_four_self_decomposition`
- `Sigma.gamma_shape_four_ne_canonical`
- `Sigma.gamma_rate_two_eq_scaled`
- `Sigma.gamma_rate_two_infinitely_divisible`
- `Sigma.gamma_rate_two_self_decomposition`
- `Sigma.gamma_rate_two_ne_canonical`

### final:P9 — One linked residual determines a law on the entire real line

Lean coverage: **complete**. [Paper statement](../paper/sections/probability.tex#L1134); [independent coverage map](formalization/current-probability-audit.json).

Mathematical content formalized in Lean:

- All three equivalent conditions for arbitrary real-line probabilities, with support and moments not assumed; independent affine sum is an actual product-space pushforward.
- Residual existence from two atom/exponential mixtures, exact transform/characteristic function/zero atom, c=0 included, scale recovered.
- Distinct designated source laws sharing the residual observation and c=1 degeneracy.

Mapped Lean declarations:

- `Sigma.gamma_residual_probability`
- `Sigma.gamma_residual_laplace`
- `Sigma.gamma_residual_zero_atom`
- `Sigma.gamma_residual_characteristic`
- `Sigma.real_line_residual_characterization`
- `Sigma.gamma_residual_scale_identified`
- `Sigma.unlinked_residual_observation_counterexample`
- `Sigma.residual_endpoint_one`
- `Sigma.residual_endpoint_one_every_law`

### final:O1 — The full-line weak Stein characterization

Lean coverage: **complete**. [Paper statement](../paper/sections/operators.tex#L15); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Literal native ContDiff-infinity compact-support test identity on the whole real line iff the actual Borel probability is Gamma(2,1).
- Integrability of the tests follows from finite mass; neither support nor moments nor density regularity is assumed.
- Actual positive-ray withDensity equality, absolute continuity, no nonpositive mass, no atoms, and integrability and values of all ordinary moments are conclusions.

Mapped Lean declarations:

- `Sigma.WeakGammaStein`
- `Sigma.stein_test_integrable`
- `Sigma.gamma_probability_weak_stein`
- `Sigma.weak_stein_characterization`
- `Sigma.weak_stein_density`
- `Sigma.weak_stein_absolutely_continuous`
- `Sigma.weak_stein_positive_support`
- `Sigma.weak_stein_no_atoms`
- `Sigma.weak_stein_moments_integrable`
- `Sigma.weak_stein_factorial_moments`

### final:O1-kernel — The integrable centered Stein kernel

Lean coverage: **complete**. [Paper statement](../paper/sections/operators.tex#L54); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Actual weak derivative, tested against all smooth compactly supported functions with support inside the positive ray, iff tau=t+C exp(t)/t almost everywhere; assumes only local integrability of tau*p.
- Smooth flux representative q+C is derived, unique among continuous representatives, satisfies the derivative/interval FTC and the full epsilon-delta local absolute-continuity property; both endpoint limits equal C.
- Either zero endpoint, genuine probability L1-integrability, genuine finite expectation, or the actual finite centered integral selects the canonical kernel.
- Canonical mean and variance are both two; nonnegativity permits exactly C>=0; every C satisfies the compact-test equation.

Mapped Lean declarations:

- `Sigma.WeakDerivativePositive`
- `Sigma.WeakSteinKernel`
- `Sigma.weak_stein_kernel_iff_family`
- `Sigma.stein_kernel_family_locally_integrable`
- `Sigma.weak_stein_kernel_smooth_flux_representative`
- `Sigma.weak_stein_kernel_continuous_representative_unique`
- `Sigma.stein_flux_representative_absolute_continuity`
- `Sigma.stein_kernel_flux_representative_integral`
- `Sigma.stein_kernel_flux_endpoints`
- `Sigma.zero_endpoint_weak_stein_kernel_unique`
- `Sigma.stein_kernel_flux_integrable_iff`
- `Sigma.weak_stein_kernel_integrable_iff_canonical`
- `Sigma.finite_expectation_weak_stein_kernel_unique`
- `Sigma.centered_integral_weak_stein_kernel_unique`
- `Sigma.steinFlux_integral`
- `Sigma.gamma_probability_mean`
- `Sigma.gamma_probability_variance`
- `Sigma.stein_kernel_family_nonnegative_iff`
- `Sigma.stein_kernel_family_weak`

### final:O2 — Two marked probes and the Pearson realization

Lean coverage: **complete**. [Paper statement](../paper/sections/operators.tex#L97); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Exact two-probe iff, pointwise and almost everywhere, with actual polynomial derivatives.
- Canonical density satisfies the actual Pearson flux derivative.
- A locally absolutely continuous weight satisfying Pearson almost everywhere has a derived everywhere derivative on the positive ray, is a constant multiple of the canonical density, and normalization forces pointwise equality with that density.
- The actual positive-ray withDensity measure equals gammaProbability, identifying the normalized Hilbert weight rather than only a scalar ODE solution.
- Both pointwise and almost-everywhere probe interpretations reconstruct coefficients and the normalized weight; the latter allows arbitrary coefficient representatives and a locally absolutely continuous flux representative.
- The canonical positive normalized density and its flux satisfy the local-AC categories and both probes, establishing the converse realization.

Mapped Lean declarations:

- `Sigma.opExpression_linear`
- `Sigma.opExpression_quadratic`
- `Sigma.operator_two_probe_iff`
- `Sigma.operator_two_probe_ae_iff`
- `Sigma.operator_canonical_probes`
- `Sigma.operator_pearson_flux_derivative`
- `Sigma.LocallyIntegralAbsolutelyContinuousPositive`
- `Sigma.local_integral_ac_continuousOn`
- `Sigma.local_integral_ac_continuousAt`
- `Sigma.local_ac_pearson_hasDerivAt`
- `Sigma.differentiable_pearson_density_family`
- `Sigma.local_ac_pearson_density_unique`
- `Sigma.local_ac_pearson_density_integrable`
- `Sigma.local_ac_pearson_weight_measure`
- `Sigma.ae_equal_positive_derivative_unique`
- `Sigma.local_integral_ac_ae_differentiable`
- `Sigma.local_ac_pearson_ae_coefficients`
- `Sigma.operator_two_probe_pearson_inverse_ae`
- `Sigma.operator_two_probe_pearson_inverse`
- `Sigma.canonical_density_local_integral_ac`
- `Sigma.operator_canonical_pearson_realization`
- `Sigma.HasLocalACPearsonFlux`
- `Sigma.local_ac_pearson_representative_canonical`
- `Sigma.operator_two_probe_pearson_representative_inverse_ae`
- `Sigma.operator_two_probe_pearson_representative_inverse`
- `Sigma.canonical_density_has_local_ac_pearson_flux`

### final:O2-boundaries — The exact limits of the probe and stationary data

Lean coverage: **complete**. [Paper statement](../paper/sections/operators.tex#L132); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Arbitrary diffusion preserves the linear probe; an exact counterfamily preserves quadratic and changes linear when its perturbation is nonzero.
- An explicit rational quadratic-only diffusion is positive on the positive ray.
- Actual globally smooth coefficient witnesses with positive diffusion on the entire positive ray retain either probe and violate the other at t=1.
- Two actual densely defined self-adjoint operators on Gamma-weighted complex L2 agree on the literal constant and both marked probe polynomials but are distinct. The swapped-mode operator has no local second-order coefficient expression, even almost everywhere.
- Native conservative Markov kernel semigroups preserve the positive ray and the actual Gamma probability, satisfy joint-measure detailed balance, and differ at every positive state. Their explicit factor-two time rescaling proves that the invariant density identifies neither dynamics nor time scale.

Mapped Lean declarations:

- `Sigma.operator_linear_probe_arbitrary_diffusion`
- `Sigma.operator_quadratic_probe_counterfamily`
- `Sigma.operator_counterfamily_changes_linear`
- `Sigma.operator_quadratic_positive_counterexample`
- `Sigma.operator_linear_only_smooth_positive_witness`
- `Sigma.operator_quadratic_only_smooth_positive_witness`
- `Sigma.operator_marked_probe_irredundancy`
- `Sigma.marked_functional_calculus_selfAdjoint`
- `Sigma.laguerre_spectral_selfAdjoint`
- `Sigma.actual_selfadjoint_probe_nonidentification`
- `Sigma.swapped_laguerre_no_local_expression`
- `Sigma.gamma_refresh_semigroup`
- `Sigma.gamma_refresh_detailed_balance`
- `Sigma.gamma_refresh_different_rates_at_state`
- `Sigma.gamma_invariant_does_not_identify_reversible_dynamics`

### final:O3 — Essential self-adjointness and the full domain

Lean coverage: **partial**. [Paper statement](../paper/sections/operators.tex#L179); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Actual weighted complex L2 minimal differential operator on exactly the compact-interior smooth test classes; density, nonnegativity and symmetry.
- Its graph closure equals the integer spectral operator and its adjoint, and is the unique self-adjoint extension. Genuine upper and logarithmic lower cutoffs supply graph-norm approximation, without assumed endpoint or mode-domain conditions.
- The actual adjoint eigenspaces at plus and minus i are both zero submodules, so both deficiency indices are zero.

Mapped Lean declarations:

- `Sigma.laguerreMinimalOperator`
- `Sigma.laguerre_minimal_domain`
- `Sigma.laguerre_minimal_test_action`
- `Sigma.laguerre_minimal_formal_adjoint`
- `Sigma.laguerre_minimal_nonnegative`
- `Sigma.laguerre_minimal_dense`
- `Sigma.laguerreCanonicalOperator`
- `Sigma.laguerre_canonical_eq_spectral`
- `Sigma.laguerre_minimal_adjoint_eq_canonical`
- `Sigma.laguerre_canonical_selfAdjoint`
- `Sigma.laguerre_canonical_unique_selfAdjoint_extension`
- `Sigma.partialOperatorEigenspace`
- `Sigma.laguerre_minimal_deficiency_spaces`
- `Sigma.laguerre_minimal_deficiency_indices`

Remaining Lean formalization:

- Both endpoint limit-point classifications.
- Exact maximal locally absolutely continuous domain and both automatic zero-flux endpoint limits.
- Domain does not require a finite value at zero, including a witnessing domain element.

### final:O3-form — The closed form and the conservative semigroup

Lean coverage: **partial**. [Paper statement](../paper/sections/operators.tex#L269); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Every square-root-domain vector has an actual locally absolutely continuous representative with finite literal weighted derivative energy equal to the square-root norm squared. Regularity and integrability are derived, not assumed.
- Actual bounded exponential-calculus operators form a contraction semigroup, including zero time, on the Gamma-weighted Hilbert space.

Mapped Lean declarations:

- `Sigma.PositiveRayLocallyAbsolutelyContinuous`
- `Sigma.laguerre_square_root_regular_representative`
- `Sigma.laguerre_square_root_derivative_energy`
- `Sigma.laguerreHeatOperator`
- `Sigma.laguerre_heat_spectral_domain_top`
- `Sigma.laguerre_heat_spectral_action`
- `Sigma.laguerre_heat_contracts`
- `Sigma.laguerre_heat_zero`
- `Sigma.laguerre_heat_add`

Remaining Lean formalization:

- Reverse inclusion: every locally absolutely continuous weighted-L2 function of finite weighted derivative energy belongs to D(A^(1/2)), with no extra endpoint traces.
- Full sesquilinear closed-form identity on the exact weighted Sobolev domain.
- Native positivity-preserving semigroup, preservation of one and of the probability measure.

### final:O3-spectrum — The Laguerre basis and the exact integer spectrum

Lean coverage: **complete**. [Paper statement](../paper/sections/operators.tex#L321); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Exact marked finite-sum Laguerre polynomials and coefficients, including nonzero leading coefficients and the first three modes.
- Canonical mean orthogonality to the constant for every positive mode.
- Exact marked Rodrigues formula with the actual nth ordinary derivative for every n >= 0 and every nonzero real argument, with a numerator identity also valid at zero. The actual first and second derivatives satisfy the Laguerre equation at every real point, and the canonical differential expression has eigenvalue n on the marked polynomial.
- The actual gamma-weighted complex L2 space contains every complex lift of a real polynomial, each marked Laguerre mode and its native complex differential image. Those modes are nonzero, and the differential-image L2 class equals n times the mode. The exact representatives L_n/sqrt(n+1) likewise belong to L2, are nonzero and satisfy the native differential equation, with their L2 scaling identification proved.
- Actual pairwise Gamma integrals and literal positive-ray density-weighted integrals equal (n+1) times the Kronecker delta for every pair of modes, including zero. The resulting actual complex L2 inner products prove orthonormality and unit norms for the exact square-root-normalized family.
- The orthogonal complement of the actual normalized Laguerre family is zero, its span is dense in the weighted complex L2 space, and the exact modes form a native HilbertBasis. Exponential-envelope moment uniqueness supplies the completeness proof without assuming density.
- The actual compact-test differential closure equals the integer spectral operator. Every normalized mode lies in its domain with eigenvalue n; the full bounded-resolvent spectrum is exactly the nonnegative integers, each eigenspace has dimension one, and positive-shift resolvents are actual compact bounded operators with both inverse identities.
- The actual operator has exactly the n-squared weighted coefficient domain and convergent action series. Its nonnegative self-adjoint spectral square root has exactly the n-weighted domain, squares to A with the exact composition domain, and has squared norm equal to the weighted coefficient energy sum.
- For every square-root-domain vector, an actual Gamma-almost-everywhere representative is derived with literal local absolute continuity, integrable q times the squared norm of its actual derivative, and derivative-energy integral equal to the weighted coefficient sum. Genuine compact form approximants, weighted-gradient completion, local L1 estimates and the almost-everywhere fundamental theorem supply the proof.

Mapped Lean declarations:

- `Sigma.opLaguerre`
- `Sigma.opLaguerreCoefficient`
- `Sigma.opLaguerre_first_three`
- `Sigma.opLaguerre_leading_coefficient`
- `Sigma.opLaguerre_leading_coefficient_ne_zero`
- `Sigma.operator_gamma_laguerre_orthogonality`
- `Sigma.op_laguerre_polynomial_eval`
- `Sigma.op_laguerre_coefficient_recurrence`
- `Sigma.op_laguerre_polynomial_ode`
- `Sigma.op_laguerre_derivative`
- `Sigma.op_laguerre_second_derivative`
- `Sigma.op_laguerre_differential_equation`
- `Sigma.op_laguerre_expression_eigenvalue`
- `Sigma.op_laguerre_rodrigues_numerator`
- `Sigma.op_laguerre_rodrigues`
- `Sigma.gamma_complex_polynomial_mem_l2`
- `Sigma.op_laguerre_complex_mem_l2`
- `Sigma.op_laguerre_expression_complex_mem_l2`
- `Sigma.laguerre_l2_vector_ne_zero`
- `Sigma.laguerre_l2_differential_eigenvalue`
- `Sigma.op_laguerre_native_complex_eigenvalue`
- `Sigma.op_laguerre_native_complex_image_mem_l2`
- `Sigma.laguerre_l2_native_complex_eigenvalue`
- `Sigma.normalized_op_laguerre_native_eigenvalue`
- `Sigma.normalized_op_laguerre_mem_l2`
- `Sigma.normalized_op_laguerre_to_l2`
- `Sigma.normalized_laguerre_l2_vector_ne_zero`
- `Sigma.gamma_polynomial_integral_factorial_moment`
- `Sigma.op_laguerre_polynomial_rodrigues_integral`
- `Sigma.op_laguerre_squared_integral`
- `Sigma.op_laguerre_pair_integral`
- `Sigma.op_laguerre_pair_integrable`
- `Sigma.op_laguerre_weighted_pair_integral`
- `Sigma.laguerre_l2_inner`
- `Sigma.normalized_laguerre_l2_orthonormal`
- `Sigma.normalized_laguerre_l2_norm`
- `Sigma.finite_measure_moments_unique_of_exponential_envelopes`
- `Sigma.laguerre_l2_eq_zero_of_orthogonal`
- `Sigma.normalized_laguerre_l2_dense_span`
- `Sigma.laguerreHilbertBasis`
- `Sigma.laguerre_hilbert_basis_apply`
- `Sigma.laguerre_canonical_eq_spectral`
- `Sigma.laguerre_basis_mem_canonical_domain`
- `Sigma.laguerre_canonical_basis_action`
- `Sigma.laguerre_canonical_domain_iff`
- `Sigma.laguerre_canonical_action_hasSum`
- `Sigma.laguerre_canonical_spectrum_exact`
- `Sigma.laguerre_canonical_compact_resolvent`
- `Sigma.laguerre_canonical_eigenspace_iff`
- `Sigma.laguerre_integer_eigenvalue_simple`
- `Sigma.laguerre_square_root_domain_iff`
- `Sigma.laguerre_square_root_squared`
- `Sigma.laguerre_square_root_image_domain_iff`
- `Sigma.laguerre_square_root_nonnegative`
- `Sigma.laguerre_square_root_energy`
- `Sigma.PositiveRayLocallyAbsolutelyContinuous`
- `Sigma.laguerre_square_root_regular_representative`
- `Sigma.laguerre_square_root_derivative_energy`

### final:O7 — Complete marked Laguerre orthogonality identifies the law

Lean coverage: **complete**. [Paper statement](../paper/sections/operators.tex#L383); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Literal polynomial-integrability candidate class on the entire real line and exact iff between all positive-mode marked Laguerre means zero and the native Gamma measure.
- Triangular finite-sum coefficients recover all factorial moments; actual measure determinacy identifies the law.
- Support in the positive ray is derived, not assumed.

Mapped Lean declarations:

- `Sigma.opLaguerre`
- `Sigma.opLaguerreCoefficient`
- `Sigma.operator_gamma_laguerre_orthogonality`
- `Sigma.operator_laguerre_orthogonality_recovers_moments`
- `Sigma.operator_laguerre_orthogonality_iff_gamma`
- `Sigma.operator_marked_laguerre_characterization`
- `Sigma.operator_marked_laguerre_positive_support`
- `Sigma.operator_full_line_factorial_moment_unique`

### final:O4 — Exact trace domains and reconstruction of the unitary class

Lean coverage: **complete**. [Paper statement](../paper/sections/operators.tex#L420); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Exact heat and shifted-zeta series domains and values identify the actual Laguerre heat and zeta traces, with exact trace-class ranges.
- For any nonnegative self-adjoint operator with an actual compact positive-shift resolvent, a complete eigenbasis is constructed and the eigenvalues are proved nonnegative; eigenvector domain membership is derived.
- Finite weighted spectral measures recover positive eigenvalue multiplicities, including finite and empty index types.
- Heat, real shifted-zeta, and integer shifted-resolvent trace data each recover the full eigenvalue multiset and give a unitary intertwining the native operators on their full domains.

Mapped Lean declarations:

- `Sigma.operator_heat_eigenvalue_hasSum`
- `Sigma.operator_heat_eigenvalue_summable_iff`
- `Sigma.operator_complex_heat_eigenvalue_hasSum`
- `Sigma.operator_complex_heat_eigenvalue_summable_iff`
- `Sigma.operator_complex_zeta_eigenvalue_summable_iff`
- `Sigma.operator_zeta_eigenvalue_hasSum`
- `Sigma.operator_hausdorff_moment_unique`
- `Sigma.integer_eigenbasis_zeta_trace`
- `Sigma.integer_eigenbasis_heat_trace`
- `Sigma.nonnegative_compact_resolvent_eigenbasis`
- `Sigma.spectral_integer_moments_equiv`
- `Sigma.integer_shifted_spectral_data_equiv`
- `Sigma.heat_spectral_data_equiv`
- `Sigma.zeta_spectral_data_equiv`
- `Sigma.eigenbasis_heat_traces_recover_operator`
- `Sigma.eigenbasis_shifted_zeta_traces_recover_operator`
- `Sigma.compact_resolvent_integer_traces_recover_operator`

### final:O4-convergence-boundary — Compact resolvent does not supply finite trace data

Lean coverage: **complete**. [Paper statement](../paper/sections/operators.tex#L496); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- A native diagonal nonnegative self-adjoint operator on the Laguerre weighted Hilbert space, with maximal spectral domain and an actual compact shift-one resolvent satisfying both inverse equations.
- Actual bounded heat and shifted-zeta diagonal operators fail to be trace class for every positive real parameter, by tail lower bounds against the divergent (n+3)^(-1/2) series.

Mapped Lean declarations:

- `Sigma.boundarySpectralFunction`
- `Sigma.boundaryEigenvalue`
- `Sigma.boundary_eigenvalue_nonneg`
- `Sigma.boundary_eigenvalue_tendsto_atTop`
- `Sigma.boundary_heat_eigenvalues_not_summable`
- `Sigma.boundary_zeta_eigenvalues_not_summable`
- `Sigma.boundaryResolventCoefficient`
- `Sigma.boundary_resolvent_coefficient_nonneg`
- `Sigma.boundary_resolvent_coefficient_bound`
- `Sigma.boundary_resolvent_coefficient_antitone`
- `Sigma.boundaryResolvent`
- `Sigma.boundary_resolvent_coordinate`
- `Sigma.boundaryResolventTruncation`
- `Sigma.boundary_resolvent_truncation_compact`
- `Sigma.boundary_resolvent_truncation_coordinate`
- `Sigma.boundary_resolvent_truncation_error`
- `Sigma.boundary_resolvent_truncation_tendsto`
- `Sigma.boundary_resolvent_compact`
- `Sigma.boundaryOperator`
- `Sigma.boundary_operator_selfadjoint`
- `Sigma.boundary_operator_nonnegative`
- `Sigma.boundary_resolvent_denominator_ne_zero`
- `Sigma.boundary_resolvent_mem_domain`
- `Sigma.boundary_resolvent_generator_action`
- `Sigma.boundary_resolvent_right_inverse`
- `Sigma.boundary_resolvent_left_inverse`
- `Sigma.boundary_operator_has_compact_resolvent`
- `Sigma.boundaryHeatCoefficient`
- `Sigma.boundary_heat_coefficient_bound`
- `Sigma.boundaryHeatOperator`
- `Sigma.boundary_heat_operator_basis_action`
- `Sigma.boundary_heat_operator_not_trace_class`
- `Sigma.boundaryZetaCoefficient`
- `Sigma.boundary_zeta_coefficient_bound`
- `Sigma.boundaryZetaOperator`
- `Sigma.boundary_zeta_operator_basis_action`
- `Sigma.boundary_zeta_operator_not_trace_class`
- `Sigma.compact_resolvent_without_positive_traces`

### final:O4-heat-kernel — The complete heat kernel relative to the invariant measure

Lean coverage: **complete**. [Paper statement](../paper/sections/operators.tex#L515); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Kernel of the actual heat operator relative to the invariant probability; Laguerre and Hille-Hardy/Bessel formulas.
- Local uniform and weighted product-L2 convergence.
- Positivity, symmetry, row normalization, large-time limit one, and the corresponding Lebesgue transition density.

Mapped Lean declarations:

- `Sigma.modifiedBesselI1`
- `Sigma.laguerreHeatKernel`
- `Sigma.laguerre_heat_kernel_integral_eq_operator`
- `Sigma.laguerre_heat_kernel_eq_spectral`
- `Sigma.laguerre_heat_series_locally_uniform`
- `Sigma.laguerre_heat_kernel_product_l2_eq_spectral`
- `Sigma.laguerre_heat_kernel_pos`
- `Sigma.laguerre_heat_kernel_symm`
- `Sigma.laguerre_heat_kernel_row_mass`
- `Sigma.laguerre_heat_kernel_tendsto_one`
- `Sigma.laguerre_heat_kernel_lebesgue_integral`

### final:O4-resolvents — Resolvents, their kernels, and the operator inverse

Lean coverage: **partial**. [Paper statement](../paper/sections/operators.tex#L583); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- A common bounded resolvent satisfying its actual two inverse equations determines a native partially defined linear operator and domain; range and action formulas proved.
- Exact scalar first/squared/shifted resolvent summability thresholds.
- The actual canonical positive-shift resolvent satisfies the inverse equations and identifies its native generator. A full marked canonical heat operator at any positive time reconstructs that generator and its exact domain using the logarithms of its actual marked coefficients; positive coefficients may accumulate at zero.

Mapped Lean declarations:

- `Sigma.OpIsResolvent`
- `Sigma.operator_resolvent_domain`
- `Sigma.operator_resolvent_action`
- `Sigma.operator_resolvent_injective`
- `Sigma.operator_full_resolvent_unique`
- `Sigma.operator_first_resolvent_eigenvalues_not_summable`
- `Sigma.operator_squared_resolvent_eigenvalues_summable`
- `Sigma.operator_shifted_real_eigenvalue_summable_iff`
- `Sigma.laguerre_canonical_positive_shift_resolvent`
- `Sigma.laguerre_complete_resolvent_identifies`
- `Sigma.laguerre_heat_spectral_action`
- `Sigma.laguerre_heat_injective`
- `Sigma.laguerre_heat_samples_positive`
- `Sigma.laguerre_heat_samples_tendsto_zero`
- `Sigma.laguerre_marked_heat_inverse`
- `Sigma.laguerre_marked_heat_inverse_domain`

Remaining Lean formalization:

- Actual heat-kernel Laplace formulas as weighted L2 resolvent kernels, finite almost everywhere.
- Hilbert-Schmidt/not-trace-class first resolvent, trace-class square and actual Hurwitz-zeta trace.
- Trace-class resolvent difference and actual digamma trace formula.

### final:O4-determinants — Zeta and Fredholm determinants with their conventions

Lean coverage: **missing**. [Paper statement](../paper/sections/operators.tex#L650); [independent coverage map](formalization/current-operator-audit.json).

Remaining Lean formalization:

- Actual zeta determinants with Hurwitz continuation and zero-mode conventions, including both sqrt(2pi) values.
- Native Fredholm and Hilbert-Schmidt regularized determinants with both entire product/Gamma/sinh formulas.
- Branch-independent sqrt quotient and value at zero.
- Eigenvalue multiset recovery from zeros with multiplicities in the indicated nonnegative shifted determinant categories.

### final:O4-finite-countermodels — Finite familiar spectral invariants do not determine the spectrum

Lean coverage: **missing**. [Paper statement](../paper/sections/operators.tex#L708); [independent coverage map](formalization/current-operator-audit.json).

Remaining Lean formalization:

- Nonconstant local family of actual nonnegative diagonal self-adjoint operators varying finitely many positive eigenvalues.
- Preservation of any finite prescribed real regular zeta values, optional finite part at one and determinant, together with every pole/principal part/value at zero.
- Proof that the spectrum changes, not merely its ordering.

### final:O5 — Existence and uniqueness of the linked mixing measure

Lean coverage: **partial**. [Paper statement](../paper/sections/operators.tex#L773); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Scalar Gamma mixing integral for every nonnegative spectral value.
- Actual full-real-line finite-positive measure characterization from all integer exponential samples; integrability, mass, positive support and no atom at zero follow.
- Actual positive finite nonnegative-ray measure uniqueness from integer Laplace values.
- Actual native signed and complex measures on the closed nonnegative ray are uniquely determined by all integer Laplace samples. Integrability follows from bounded kernels and finite Jordan parts; sample zero is exactly the total mass. The canonical complex Gamma measure is explicitly constructed, its real-line pushforward is gammaProbability, and its integer samples characterize it in both directions.

Mapped Lean declarations:

- `Sigma.operator_gamma_mixing_integral`
- `Sigma.operator_gamma_mixing_integer_integral`
- `Sigma.operator_nonnegative_mixing_measure_unique`
- `Sigma.operator_full_line_mixing_characterization`
- `Sigma.operator_full_line_mixing_iff`
- `Sigma.operator_integer_samples_integrable`
- `Sigma.operator_integer_samples_positive_support`
- `Sigma.operator_integer_samples_ae_pos`
- `Sigma.signed_total_variation_finite`
- `Sigma.complex_measure_norm_le_control`
- `Sigma.nonnegative_laplace_test_integrable`
- `Sigma.operator_signed_mixing_measure_unique`
- `Sigma.operator_complex_mixing_measure_unique`
- `Sigma.signed_integer_sample_zero_mass`
- `Sigma.complex_integer_sample_zero_mass`
- `Sigma.nonnegative_gamma_mixing_on_real_line`
- `Sigma.nonnegative_gamma_complex_integer_samples`
- `Sigma.operator_complex_gamma_mixing_characterization`
- `Sigma.operator_complex_gamma_mixing_iff`
- `Sigma.nonnegative_gamma_complex_measure_apply`

Remaining Lean formalization:

- Strong-operator mixing identity for every nonnegative self-adjoint B.
- Extraction of scalar samples from each integer eigenvector in that actual operator identity.

### final:O6 — A Bernstein function is determined by every integer tail

Lean coverage: **complete**. [Paper statement](../paper/sections/operators.tex#L841); [independent coverage map](formalization/current-operator-audit.json).

Mathematical content formalized in Lean:

- Actual finite compact Hausdorff moment uniqueness, an ingredient.
- The actual scalar integral with density 2 exp(-s)/s equals 2 log(1+lambda), including integrability for nonnegative lambda.
- For Bernstein representation candidates, construction of the finite moment measure and recovery of full killing, drift and actual Levy measure from arbitrary integer tails, including tail index zero and the conclusion at zero without assuming it.
- Gamma target's actual Levy integrability and representation identification, including killing and drift zero.
- An independently constructed native complex sequence-l2 diagonal LinearPMap has the exact weighted-square-summability domain; its action on every coordinate eigenvector is f(n)e_n, and equality of these actions extracts every scalar sample.
- A distinct smooth nonnegative non-Bernstein perturbation agrees with the Gamma exponent at every nonnegative integer and yields exactly the same diagonal sequence-l2 LinearPMap, including its domain.
- The proved complete Laguerre representation intertwines the actual differential closure A, including its full domain. Its self-adjoint functional calculus has the exact weighted coefficient domain and convergent action series; it is uniquely characterized among self-adjoint operators by those marked basis actions.
- Actual weighted-L2 operator actions on any integer tail extract the scalar samples and recover the full Bernstein function and killing, drift and native Levy measure, including the Gamma target and zero endpoint. The explicit distinct smooth nonnegative non-Bernstein perturbation has exactly the same full actual weighted-L2 operator, including domain.

Mapped Lean declarations:

- `Sigma.operator_hausdorff_moment_unique`
- `Sigma.gamma_levy_exponent_integral`
- `Sigma.gamma_levy_exponent_integrable`
- `Sigma.BernsteinRepresentation`
- `Sigma.HasBernsteinRepresentation`
- `Sigma.BernsteinRepresentation.kernel_integrable`
- `Sigma.BernsteinRepresentation.increment_laplace`
- `Sigma.BernsteinRepresentation.integer_tail_data_unique`
- `Sigma.BernsteinRepresentation.integer_tail_unique`
- `Sigma.bernstein_function_integer_tail_unique`
- `Sigma.gammaCompletionLevyMeasure`
- `Sigma.gamma_completion_levy_integrability`
- `Sigma.gamma_bernstein_representation_exponent`
- `Sigma.gamma_laplace_exponent_has_bernstein_representation`
- `Sigma.gamma_bernstein_integer_tail_unique`
- `Sigma.gamma_bernstein_function_integer_tail_unique`
- `Sigma.smooth_integer_invisible_exponent_boundary`
- `Sigma.markedFunctionalCalculus`
- `Sigma.markedFunctionalCalculus_eigenvector_action`
- `Sigma.marked_samples_of_eigenvector_actions`
- `Sigma.markedFunctionalCalculus_congr`
- `Sigma.smooth_integer_invisible_marked_functional_calculus`
- `Sigma.laguerre_canonical_eq_spectral`
- `Sigma.laguerre_canonical_repr`
- `Sigma.laguerre_canonical_repr_domain`
- `Sigma.laguerre_spectral_domain_iff`
- `Sigma.laguerre_spectral_action_hasSum`
- `Sigma.laguerre_selfAdjoint_eq_spectral_of_basis`
- `Sigma.laguerre_spectral_congr`
- `Sigma.laguerre_samples_of_tail_actions`
- `Sigma.laguerre_bernstein_tail_actions_unique`
- `Sigma.laguerre_bernstein_tail_actions_data_unique`
- `Sigma.laguerre_gamma_tail_actions_unique`
- `Sigma.smooth_integer_invisible_canonical_calculus`

### final:O6-functional-calculus — Two different functional-calculus inverse questions

Lean coverage: **missing**. [Paper statement](../paper/sections/operators.tex#L919); [independent coverage map](formalization/current-operator-audit.json).

Remaining Lean formalization:

- Known strictly increasing Bernstein function's Borel inverse recovers a native nonnegative self-adjoint B from f(B), with exact domains/endpoints.
- Equivalence between actual 2 log(Id+A) and J(A)=(Id+A)^-2 via unbounded logarithmic functional calculus.

### final:O5-isospectral-boundary — The Gamma shapes two and three retain all spectral and mixing data

Lean coverage: **missing**. [Paper statement](../paper/sections/operators.tex#L943); [independent coverage map](formalization/current-operator-audit.json).

Remaining Lean formalization:

- Both actual Gamma-shape-two and shape-three weighted L2 self-adjoint closures with limit-point endpoints.
- Complete simple integer eigenbases and intertwining unitary fixing one.
- Agreement of every listed spectral invariant with conventions/domains and common unique mixing measure.
- Distinct invariant coordinate probabilities with respective means two and three, inside those linked realizations.

### final:O5-canonical-versus-identification — Canonical mixing construction is not unmarked coordinate recovery

Lean coverage: **missing**. [Paper statement](../paper/sections/operators.tex#L1011); [independent coverage map](formalization/current-operator-audit.json).

Remaining Lean formalization:

- Canonical Gamma mixing existence for arbitrary nonnegative self-adjoint operators and integer-eigenvalue mixing uniqueness as actual operator facts.
- Actual stationary-coordinate nonidentification witness even retaining all spectral/mixing data and the constant.
- Identification under explicit mixing/coordinate linkage or the locally AC Pearson realization.

### final:F1 — The normalized Todd tower and all its twists

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L15); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Actual exponential quotient, normalized tower existence and uniqueness over every characteristic-zero field
- Degree-zero equation equivalence
- Polynomial twist identity, arbitrary field parameter, empty product and negative integer specializations
- Counterexample after deletion of each positive tower degree
- Twist and tower identities over commutative rational algebras
- Unnormalized unit-parameter family

Mapped Lean declarations:

- `Sigma.exponential_quotient_todd_exists_unique`
- `Sigma.normalized_todd_tower_iff_exponential_quotient`
- `Sigma.all_degree_todd_tower_iff_exponential_quotient`
- `Sigma.formal_twisted_todd_coeff`
- `Sigma.todd_twist_polynomial_identity`
- `Sigma.formal_twisted_todd_coeff_nat`
- `Sigma.formal_todd_omitted_degree`
- `Sigma.formal_twisted_todd_coeff_over_Q_algebra`
- `Sigma.todd_tower_iff_exponential_quotient_over_Q_algebra`
- `Sigma.unnormalized_todd_family_over_Q_algebra_exists_unique`

### final:F2 — Reversible characteristic-series formulas

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L96); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Actual normalized characteristic quotient series
- Marked mutually inverse Todd/Ahat/L/chi formulas and exponential recovery
- Normalized square-root existence, uniqueness and reconstruction
- Exceptional y=-1 specialization and noninjectivity
- Multiplicative unit inversion
- General rational-algebra unit-parameter reconstruction and polynomial localization

Mapped Lean declarations:

- `Sigma.formal_ahat_constant`
- `Sigma.formal_L_constant`
- `Sigma.formal_chi_constant`
- `Sigma.formal_ahat_quotient`
- `Sigma.formal_L_quotient`
- `Sigma.formal_ahat_to_todd`
- `Sigma.formal_todd_to_L`
- `Sigma.formal_L_to_todd`
- `Sigma.formal_todd_recovers_exponential`
- `Sigma.formal_L_recovers_exponential`
- `Sigma.formal_chi_recovers_todd`
- `Sigma.formal_ahat_square_root_exists_unique`
- `Sigma.formal_ahat_recovers_todd_from_any_normalized_root`
- `Sigma.characteristic_chi_minus_one_noninjective`
- `Sigma.formal_chi_minus_one_standard`
- `Sigma.standard_characteristic_inverse_reconstruction`
- `Sigma.formal_chi_over_recovers_todd`
- `Sigma.standard_characteristic_units_inverse_reconstruction`
- `Sigma.formal_chi_polynomial_localization_reconstruction`

### final:F3 — Formal, analytic, and global recovery

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L144); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Formal exponential recovery
- Normalized rational formal logarithm and uniqueness for its differential equation
- Smooth strictly convex global nonidentification witness with unchanged germ and all jets at one but different value at three eighths
- Derived positive perturbation-size threshold preserving strict convexity for every compactly supported smooth perturbation
- Actual formal exponential-minus-one and formal logarithm are two-sided compositional inverses, with uniqueness over characteristic-zero fields and arbitrary commutative rational algebras, including rings with zero divisors
- The recovered logarithm and entropy formal series have literal convergent real sums to log(1+z) and H(1+z) on the open unit disc
- Actual standard real Todd/Ahat/L/chi quotients extend analytically through zero with value one and are analytic at every real argument, with all displayed real reconstruction identities and the positive Ahat square-root branch
- Independently supplied analytic functions with the same germ agree on their common connected domain
- Actual normalized complex Todd/Ahat/L quotients have genuine simple meromorphic poles precisely at their nonzero imaginary lattices, with nearest poles exactly plus/minus 2pi i for Todd/Ahat and plus/minus pi i for L
- Multiplicative inverse real representatives are analytic on their exact nonvanishing domains, inverse reversal holds, and all exponential-recovery denominators are nonzero
- Actual native analytic power-series germs have exactly the existing formal Todd/Ahat/L/chi coefficients and reciprocal coefficients, for every real marked chi parameter including minus one
- Equality of these actual formal germs implies equality of independently supplied analytic representatives on their common connected domain containing zero
- Native complex Taylor germs exist with exact radii 2pi for Todd/Ahat and pi for L; their sums recover the same real representatives on the real portions of those discs
- Explicit real points lie outside each finite Taylor disc although the real representatives are analytic on their full real domains

Mapped Lean declarations:

- `Sigma.formal_todd_recovers_exponential`
- `Sigma.formal_L_recovers_exponential`
- `SigmaPresentations.formalLog_ode`
- `SigmaPresentations.normalized_formal_log_ode_reconstruction`
- `Sigma.compact_smooth_perturbation_strictConvex`
- `Sigma.smooth_potential_extension_counterexample`
- `Sigma.formalLogarithm`
- `Sigma.formal_logarithm_ode`
- `Sigma.formal_logarithm_unique`
- `Sigma.formal_exp_log_inverse`
- `Sigma.formal_log_exp_inverse`
- `Sigma.formal_exp_inverse_unique`
- `Sigma.formal_logarithm_rational`
- `Sigma.formalComposeOver`
- `Sigma.formal_compose_over_injective`
- `Sigma.formalLogarithmOver`
- `Sigma.formal_exp_log_over_inverse`
- `Sigma.formal_log_exp_over_inverse`
- `Sigma.formal_log_exp_over_inverse_unique`
- `Sigma.formal_logarithm_over_field`
- `Sigma.formal_logarithm_real_hasSum`
- `Sigma.formalEntropyGerm`
- `Sigma.formal_entropy_germ_hasSum`
- `Sigma.formal_entropy_germ_intrinsic`
- `Sigma.realTodd`
- `Sigma.realAhat`
- `Sigma.realLgenus`
- `Sigma.realChi`
- `Sigma.real_todd_zero`
- `Sigma.real_characteristic_zero`
- `Sigma.real_todd_analytic`
- `Sigma.real_ahat_analytic`
- `Sigma.real_lgenus_analytic`
- `Sigma.real_chi_analytic`
- `Sigma.real_todd_quotient`
- `Sigma.real_ahat_quotient`
- `Sigma.real_lgenus_quotient`
- `Sigma.real_todd_recovers_real_exponential`
- `Sigma.real_lgenus_recovers_exponential`
- `Sigma.real_ahat_recovers_todd`
- `Sigma.real_lgenus_todd_inverse`
- `Sigma.real_chi_inverse`
- `Sigma.real_chi_minus_one`
- `Sigma.real_ahat_square_root`
- `Sigma.real_ahat_square_root_reconstructs_todd`
- `Sigma.real_analytic_global_recovery`
- `Sigma.complexTodd`
- `Sigma.complexAhat`
- `Sigma.complexLgenus`
- `Sigma.complex_characteristic_analytic_zero`
- `Sigma.complex_todd_quotient`
- `Sigma.complex_ahat_quotient`
- `Sigma.complex_lgenus_quotient`
- `Sigma.analytic_quotient_simple_pole`
- `Sigma.complex_todd_poles_iff`
- `Sigma.complex_ahat_poles_iff`
- `Sigma.complex_lgenus_poles_iff`
- `Sigma.complex_todd_ahat_nearest_poles`
- `Sigma.complex_lgenus_nearest_poles`
- `Sigma.complex_characteristic_boundary_poles`
- `Sigma.simple_complex_pole_not_analytic`
- `Sigma.real_characteristic_recovery_denominators`
- `Sigma.real_characteristic_inverses_analytic`
- `Sigma.real_characteristic_inverse_reversal`
- `Sigma.HasRealFormalGerm`
- `Sigma.real_formal_germ_iff`
- `Sigma.real_formal_germ_unique`
- `Sigma.real_formal_germ_mul`
- `Sigma.real_formal_germ_sub`
- `Sigma.real_formal_germ_rescale`
- `Sigma.real_formal_germ_exp`
- `Sigma.real_formal_germ_dslope`
- `Sigma.real_formal_germ_inv`
- `Sigma.real_todd_denominator_formal_germ`
- `Sigma.real_todd_formal_germ`
- `Sigma.real_ahat_formal_germ`
- `Sigma.real_lgenus_formal_germ`
- `Sigma.real_chi_formal_germ`
- `Sigma.real_characteristic_inverse_formal_germs`
- `Sigma.real_formal_germ_global_recovery`
- `Sigma.quotient_taylor_radius_le`
- `Sigma.analytic_disk_le_taylor_radius`
- `Sigma.complex_characteristic_on_reals`
- `Sigma.complex_todd_analytic_disk`
- `Sigma.complex_ahat_analytic_disk`
- `Sigma.complex_lgenus_analytic_disk`
- `Sigma.complex_todd_taylor_radius`
- `Sigma.complex_ahat_taylor_radius`
- `Sigma.complex_lgenus_taylor_radius`
- `Sigma.characteristic_taylor_series_exist`
- `Sigma.complex_todd_taylor_on_reals`
- `Sigma.complex_ahat_taylor_on_reals`
- `Sigma.complex_lgenus_taylor_on_reals`
- `Sigma.characteristic_taylor_discs_do_not_cover_reals`

### final:F4 — The universal Thom correction, conditional on topology

Lean coverage: **partial**. [Paper statement](../paper/sections/series-realizations.tex#L178); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Cancellation of multiplication by the formal variable in rational power series
- Inversion injectivity for complete formal units
- Actual finite coefficient evaluation at a nilpotent class is independent of every sufficiently large cutoff and agrees with native polynomial evaluation
- Adding X^(N+1)R at u^(N+1)=0 changes no evaluation; the explicit distinct rational series F+X^(N+1) preserves the constant term and all sufficiently large cutoff evaluations

Mapped Lean declarations:

- `Sigma.universal_line_correction_unique`
- `Sigma.universal_unit_inverse_reconstruction`
- `Sigma.finiteSeriesEvaluation`
- `Sigma.finite_series_evaluation_sum`
- `Sigma.nilpotent_series_evaluation_stable`
- `Sigma.nilpotent_series_evaluation_polynomial`
- `Sigma.nilpotent_series_evaluation_tail`
- `Sigma.nilpotent_complete_series_nonidentification`

Remaining Lean formalization:

- Actual supplied K-theory/cohomology Thom comparison and existence/uniqueness of its correction
- Universal-line compatibility and inverse-limit correction identity
- Multiplicative splitting-principle descent to actual bundles
- Collapse/Gysin Riemann--Roch identity for oriented proper maps and virtual tangent bundles

### final:F5 — Rational characteristic data lose integral data

Lean coverage: **missing**. [Paper statement](../paper/sections/series-realizations.tex#L251); [independent coverage map](formalization/current-realizations-audit.json).

Remaining Lean formalization:

- Actual complexification of the tautological real line on RP2
- Nontriviality of that bundle and of its class relative to the trivial line in complex K0
- Its rational Chern character equals one
- Resulting fixed-base nonreconstruction witness

### final:M1 — The unique scalar-block spectral lift

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L295); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Uniqueness for actual positive-rank SPD matrix families without regularity
- Spectral sum equals trace minus log determinant minus rank
- Nonnegativity
- Full arbitrary-block additivity
- Actual orthogonal congruence invariance
- Nonnegative scalar-seeded full-block-additive family which fails orthogonal invariance at explicit SPD and rational orthogonal matrices
- Nonnegative scalar-seeded orthogonally invariant family which fails scalar-block recursion at identity scalar blocks

Mapped Lean declarations:

- `Sigma.spd_positive_rank_lift_unique`
- `Sigma.matrixPotential_spectral`
- `Sigma.matrixPotential_nonnegative`
- `Sigma.matrixPotential_similarity`
- `Sigma.matrixPotential_block_additivity`
- `Sigma.matrixPotential_orthogonal_congruence`
- `Sigma.matrix_basis_lift_nonnegative`
- `Sigma.matrix_basis_lift_seed`
- `Sigma.matrix_basis_lift_blocks`
- `Sigma.matrix_basis_lift_invariance_failure`
- `Sigma.matrix_rank_shift_nonnegative`
- `Sigma.matrix_rank_shift_seed`
- `Sigma.matrix_rank_shift_invariant`
- `Sigma.matrix_rank_shift_recursion_failure`
- `Sigma.positive_definite_congruence`

### final:M2 — Derivatives, divergence, duality, and determinant bounds

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L339); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Actual Frechet differential and second derivative of the matrix potential
- Actual differential Bregman formula
- Strict positivity on nonzero symmetric tangent matrices
- Divergence nonnegativity and equality exactly at identical matrices
- Congruence invariance of divergence and metric
- Inversion isometry and directed-divergence reversal
- Exponential determinant bound and identity equality case
- Arithmetic-mean determinant bound and exact scalar-matrix equality case in every positive rank
- Strict concavity of log determinant on the actual convex SPD cone
- Literal extended-real supremum conjugate with exact finite domain and infinite boundary for symmetric dual matrices
- Unique finite-domain optimizer and both Legendre coordinate inverse identities
- Actual SPD spectral witnesses making the dual objective arbitrarily large whenever a dual-complement eigenvalue is nonpositive, including zero
- Actual differential of the finite dual potential and Bregman duality with reversed Legendre coordinates

Mapped Lean declarations:

- `Sigma.matrixPotential_fderiv`
- `Sigma.matrixPotential_second_fderiv`
- `Sigma.matrix_hessian_metric`
- `Sigma.matrix_actual_bregman`
- `Sigma.matrixDivergence_nonnegative`
- `Sigma.matrixDivergence_eq_zero_iff`
- `Sigma.matrixDivergence_congruence`
- `Sigma.matrix_precision_reversal`
- `Sigma.precisionMetric_positive`
- `Sigma.hessianMetric_congruence`
- `Sigma.hessianMetric_inversion`
- `Sigma.spd_determinant_exponential_bound`
- `Sigma.spd_determinant_exponential_equality`
- `Sigma.spd_determinant_arithmetic_mean_bound`
- `Sigma.spd_determinant_arithmetic_mean_equality`
- `Sigma.positive_definite_trace_positive`
- `Sigma.positive_definite_convex`
- `Sigma.matrix_logdet_strictConcave`
- `Sigma.matrix_fenchel_conjugate_formula`
- `Sigma.matrix_fenchel_conjugate_finite`
- `Sigma.matrix_fenchel_conjugate_infinite`
- `Sigma.matrix_fenchel_unbounded`
- `Sigma.matrix_fenchel_equality_iff`
- `Sigma.matrix_legendre_coordinate_inverse`
- `Sigma.matrix_legendre_inverse_coordinate`
- `Sigma.matrix_dual_potential_fderiv`
- `Sigma.matrix_bregman_legendre_duality`

### final:M3 — Geodesics, distance, and the symmetrization boundary

Lean coverage: **partial**. [Paper statement](../paper/sections/series-realizations.tex#L435); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Relative spectral symmetrization of the actual SPD matrix divergence using eigenvalues of X inverse-square-root times Y times X inverse-square-root
- Native positive-definite relative matrix, inverse-square-root whitening, and trace of the inverse as the sum of reciprocal positive eigenvalues
- Symmetric spectral matrix logarithm whose native matrix exponential is the original SPD matrix
- The displayed native matrix exponential path is SPD at every parameter and has exactly the specified endpoints
- The canonical full-rank path belongs to the actual finite-piece admissible class, and its exact Hessian path length is an explicit variational competitor
- Actual first and second derivatives of the path, continuous first derivative, and the displayed differential equation gamma''=gamma' gamma-inverse gamma'
- Actual Hessian-metric speed is constant and its interval-integral path length equals the Frobenius norm of the relative logarithm
- Rank-one native SPD-matrix path-length infimum over both C1 and finite-piece C1 paths equals the absolute logarithmic endpoint difference, with an attained exponential path and zero self-distance
- Exact equality of the rank-one C1 and piecewise-C1 infima, allowing corners and one-sided endpoints
- Native rank-one matrix divergence symmetrization equals four times sinh squared of half the piecewise-C1 variational distance
- Unique rank-one constant-speed minimizing C1 and piecewise-C1 paths, with a.e. constant speed allowed in the piecewise category and coincident endpoints included
- Exact equality of the unique rank-one interpolation with the canonical spectral square-root/exponential/logarithm curve, its piecewise-C1 admissibility, constant speed and minimizing length
- Rank-one piecewise-C1 variational distance equals the Frobenius norm of the actual relative matrix logarithm, and every a.e. constant-speed minimizer equals that spectral curve on the full closed interval
- Native all-rank piecewise-C1 Hessian path-length infimum, metric Cauchy-Schwarz, and log-coordinate/log-determinant lower bounds for every admissible SPD path
- Exact distances from identity to single-log-coordinate and isotropic diagonal exponential endpoints, proved by all-path lower bounds and attaining paths
- Actual equal-distance unequal-symmetrization SPD witnesses in every rank at least two, hence no scalar function of the path distance recovers symmetrized divergence

Mapped Lean declarations:

- `Sigma.matrixRelativeSPD`
- `Sigma.matrix_relative_spd_positive`
- `Sigma.matrix_inverse_sqrt_whitens`
- `Sigma.matrix_symmetrization_relative`
- `Sigma.matrix_trace_inverse_eigenvalues`
- `Sigma.positive_eigenvalue_hyperbolic_symmetrization`
- `Sigma.matrix_potential_symmetrization_spectral`
- `Sigma.matrix_divergence_relative_symmetrization`
- `Sigma.matrixSPDLog`
- `Sigma.matrix_spd_log_symmetric`
- `Sigma.matrix_exp_spd_log`
- `Sigma.matrix_exp_symmetric_positive`
- `Sigma.matrixExponentialCurve`
- `Sigma.matrix_exponential_curve_positive`
- `Sigma.matrix_exponential_curve_hasDerivAt`
- `Sigma.matrix_exponential_velocity_hasDerivAt`
- `Sigma.matrix_exponential_curve_metric_square`
- `Sigma.matrix_symmetric_frobenius_norm_square`
- `Sigma.matrix_sqrt_inverse`
- `Sigma.matrix_relative_spd_reconstruct`
- `Sigma.matrixSPDGeodesic`
- `Sigma.matrix_spd_geodesic_positive`
- `Sigma.matrix_spd_geodesic_zero`
- `Sigma.matrix_spd_geodesic_one`
- `Sigma.matrixHessianSpeed`
- `Sigma.matrixHessianPathLength`
- `Sigma.matrix_exponential_curve_constant_speed`
- `Sigma.matrix_spd_geodesic_length`
- `Sigma.matrix_spd_geodesic_admissible`
- `Sigma.matrix_spd_geodesic_is_admissible_with_exact_length`
- `Sigma.matrix_exponential_curve_deriv`
- `Sigma.matrix_exponential_curve_continuous_deriv`
- `Sigma.matrix_exponential_curve_native_geodesic_equation`
- `Sigma.rankOneMatrix_metric`
- `Sigma.rankOneMatrix_speed`
- `Sigma.rank_one_hessian_length_lower_bound`
- `Sigma.rank_one_exponential_path_admissible`
- `Sigma.rank_one_exponential_path_length`
- `Sigma.rankOneHessianDistance`
- `Sigma.rank_one_hessian_distance`
- `Sigma.rank_one_hessian_distance_self`
- `Sigma.RankOneMatrixAdmissiblePath`
- `Sigma.rank_one_native_path_scalar_admissible`
- `Sigma.rank_one_native_path_length_lower_bound`
- `Sigma.rank_one_exponential_native_path_admissible`
- `Sigma.rankOneMatrixHessianDistance`
- `Sigma.rank_one_native_hessian_distance`
- `Sigma.rank_one_native_distance_divergence_symmetrization`
- `Sigma.rank_one_segment_speed_integrable_and_bound`
- `Sigma.RankOnePiecewiseAdmissiblePath`
- `Sigma.rank_one_piecewise_path_length_lower_bound`
- `Sigma.rank_one_c1_path_piecewise_admissible`
- `Sigma.rankOnePiecewiseHessianDistance`
- `Sigma.rank_one_piecewise_hessian_distance`
- `Sigma.rank_one_piecewise_distance_eq_c1_distance`
- `Sigma.rank_one_piecewise_distance_divergence_symmetrization`
- `Sigma.rank_one_log_path_rigid`
- `Sigma.rank_one_native_speed_bound_rigid`
- `Sigma.rank_one_native_constant_speed_minimizer_unique`
- `Sigma.rank_one_piecewise_subinterval_length_lower_bound`
- `Sigma.rank_one_piecewise_constant_speed_minimizer_unique`
- `Sigma.matrix_exp_rankOneMatrix`
- `Sigma.rank_one_matrix_spd_log_entry`
- `Sigma.rank_one_matrix_relative_entry`
- `Sigma.rank_one_canonical_matrix_geodesic`
- `Sigma.rank_one_matrix_geodesic_piecewise_admissible`
- `Sigma.rank_one_matrix_geodesic_minimizing`
- `Sigma.rank_one_matrix_geodesic_constant_speed`
- `Sigma.rank_one_piecewise_distance_matrix_log_norm`
- `Sigma.rank_one_matrix_geodesic_unique_piecewise_minimizer`
- `Sigma.precisionMetric_cauchy_schwarz`
- `Sigma.matrix_logdet_velocity_bound`
- `Sigma.matrix_diagonal_log_velocity_bound`
- `Sigma.matrix_spd_path_velocity_symmetric`
- `Sigma.matrix_segment_speed_integrable`
- `Sigma.MatrixPiecewiseAdmissiblePath`
- `Sigma.matrix_piecewise_rank_one_iff`
- `Sigma.matrix_piecewise_diagonal_log_length_bound`
- `Sigma.matrix_piecewise_logdet_length_bound`
- `Sigma.matrixPiecewiseHessianDistance`
- `Sigma.matrix_piecewise_distance_rank_one`
- `Sigma.matrixHessianPathLength_nonnegative`
- `Sigma.matrixDiagonalExpPath`
- `Sigma.matrix_diagonal_exp_path_admissible`
- `Sigma.matrix_diagonal_exp_path_length`
- `Sigma.matrix_single_log_distance`
- `Sigma.matrix_isotropic_log_distance`
- `Sigma.matrix_diagonal_exp_symmetrization`
- `Sigma.matrix_equal_distance_divergence_counterexample`
- `Sigma.matrix_symmetrized_divergence_not_distance_function`

Remaining Lean formalization:

- Metric-geodesic interpretation, higher-rank global length minimality among admissible SPD paths and actual metric distance formula
- Higher-rank unique constant-speed minimizing curve in the full piecewise-C1 category, including X=Y

### final:M4 — The supplied Gaussian and Wishart sampling model

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L499); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Actual centered covariance-X multivariate Gaussian probability, constructed from independent native standard Gaussians by the invertible SPD square root, with derived normalized density, mean and covariance.
- Actual iid joint/sample and Wishart scatter pushforward laws, including arbitrary measurable independent samples on a supplied probability space; exact normalized log likelihood and its scatter factorization.
- Statistical sufficiency: one native Markov kernel is a regular conditional law of the full sample given its scatter simultaneously for every SPD covariance. The full joint-law disintegration identity is proved from the density tilt, not assumed as a factorization interpretation.
- For every symmetric Theta, the actual extended Wishart exponential expectation has the stated determinant formula exactly on the SPD domain, and equals infinity otherwise, including zero eigenvalues. Positive sample count is retained where required.
- The actual sample and Wishart scatter are positive definite almost surely exactly when m>=n. Independent absolutely continuous samples avoid proper subspaces by Haar-nullity and product induction; generic position is a conclusion, not a premise.
- The actual sample density has unique MLE C when C is SPD, exact negative-log-likelihood excess (m/2)D(C,X), and no MLE for singular observed covariance in the open cone.
- Actual native Radon-Nikodym log-ratio integrability and oriented Gaussian relative entropy KL(X||Y)=D(X,Y)/2, with the exact m-fold independent-copy factor.

Mapped Lean declarations:

- `Sigma.matrixScatterNegLogLikelihood`
- `Sigma.matrixCovarianceNegLogLikelihood`
- `Sigma.matrix_sample_scatter_gram`
- `Sigma.matrix_sample_scatter_posSemidef`
- `Sigma.matrixGaussianMeasure`
- `Sigma.matrix_gaussian_measure_density`
- `Sigma.matrix_gaussian_coordinate_mean`
- `Sigma.matrix_gaussian_coordinate_pair_moment`
- `Sigma.matrixGaussianSampleMeasure`
- `Sigma.matrixWishartMeasure`
- `Sigma.matrix_gaussian_iid_joint_law`
- `Sigma.matrix_gaussian_iid_scatter_law`
- `Sigma.matrix_gaussian_sample_measure_density`
- `Sigma.matrix_gaussian_sample_log_density`
- `Sigma.matrix_gaussian_sample_density_factorization`
- `Sigma.HasCommonStatisticKernel`
- `Sigma.common_statistic_kernel_of_tilts`
- `Sigma.matrix_gaussian_scatter_sufficient`
- `Sigma.matrixWishartExponentialMoment`
- `Sigma.matrixWishartDomain`
- `Sigma.matrix_wishart_moment_formula`
- `Sigma.matrix_wishart_moment_finite_iff`
- `Sigma.matrix_wishart_moment_infinite`
- `Sigma.matrix_sample_scatter_rank`
- `Sigma.matrix_gaussian_sample_scatter_ae_posDef_iff`
- `Sigma.matrix_wishart_ae_posDef_iff`
- `Sigma.matrix_gaussian_log_likelihood_gap`
- `Sigma.matrix_gaussian_sample_unique_mle`
- `Sigma.matrix_gaussian_singular_sample_no_mle`
- `Sigma.matrix_gaussian_relative_entropy_integrable`
- `Sigma.matrix_gaussian_relative_entropy`
- `Sigma.matrix_gaussian_sample_relative_entropy_integrable`
- `Sigma.matrix_gaussian_sample_relative_entropy_divergence`

### final:R1 — The isotropic four-dimensional Gaussian realization

Lean coverage: **partial**. [Paper statement](../paper/sections/series-realizations.tex#L573); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Equality of the scalar drift coefficients D/2-t and 2-t for all t iff D=4
- Actual Frechet gradient, coordinate second derivatives, Euclidean Laplacian and OU differential-expression identity, with an origin-inclusive version for profiles differentiable at nonnegative energies and an off-origin version requiring differentiability only at positive energies
- Two genuine probabilities on native four-dimensional Euclidean space, constructed by opposite unit-vector lifts of the Gamma radius, have the exact same energy pushforward gammaProbability and are distinct: a measurable coordinate halfspace has mass one for one and zero for the other

Mapped Lean declarations:

- `Sigma.radial_OU_dimension`
- `Sigma.radial_energy_hasFDerivAt`
- `Sigma.radial_energy_gradient`
- `Sigma.radial_energy_direction_second_derivative`
- `Sigma.radial_energy_euclidean_laplacian`
- `Sigma.radial_energy_OU_generator`
- `Sigma.radial_energy_direction_second_derivative_of_eventually`
- `Sigma.radial_energy_direction_second_derivative_positive`
- `Sigma.radial_energy_euclidean_laplacian_positive`
- `Sigma.radial_energy_OU_generator_positive`
- `Sigma.radial_four_positive_lift_energy`
- `Sigma.radial_four_negative_lift_energy`
- `Sigma.radial_four_positive_law_energy`
- `Sigma.radial_four_negative_law_energy`
- `Sigma.radial_four_positive_law_halfspace`
- `Sigma.radial_four_negative_law_halfspace`
- `Sigma.radial_four_laws_distinct`
- `Sigma.gamma_radial_energy_does_not_identify_vector_law`

Remaining Lean formalization:

- Actual four-dimensional Gaussian radial pushforward
- Independent uniform S3-angle inverse and orthogonal-invariance uniqueness
- Actual OU process and Ito radial SDE with normalized one-dimensional Brownian motion

### final:R2 — Nonnegative orthogonal additivity without regularity

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L650); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Full no-regularity quadratic iff on arbitrary real inner-product spaces of cardinal dimension at least two
- Full exponential-star iff with nonnegativity
- Positive scale from nontriviality and scale calibration
- Dimension-one quartic and nonnegative-assumption linear-functional omission witnesses

Mapped Lean declarations:

- `Sigma.nonnegative_orthogonal_quadratic_iff`
- `Sigma.nonnegative_orthogonal_star_iff`
- `Sigma.quadratic_nontrivial_scale_positive`
- `Sigma.quadratic_scale_calibration`
- `Sigma.quadratic_scale_calibration_nonzero`
- `Sigma.line_quartic_orthogonal_additive`
- `Sigma.line_quartic_not_quadratic`
- `Sigma.linear_profile_orthogonally_additive`
- `Sigma.linear_profile_negative_at_neg_unit`
- `Sigma.linear_profile_not_quadratic`

### final:R3 — The profile-independent radial residual

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L717); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Actual second-derivative quotient identity on the positive ray
- Conjugated radial differential expression without nonvanishing assumption
- Cancellation iff dimension is one or three and selection of three when dimension is at least two
- Different constant profile with the same cancellation
- Actual Euclidean Laplacian radial formula from the sum of coordinate second derivatives along any finite orthonormal basis, at every nonzero point

Mapped Lean declarations:

- `Sigma.radialWeight_eq_rpow`
- `Sigma.weighted_profile_second_deriv`
- `Sigma.radial_residual`
- `Sigma.radial_laplacian_conjugation`
- `Sigma.radial_residual_cancellation`
- `Sigma.radial_residual_dimension_three`
- `Sigma.constant_profile_radial_residual_three`
- `Sigma.constant_profile_differs_from_H_on_positive_ray`
- `Sigma.euclideanLaplacian`
- `Sigma.norm_line_hasDerivAt`
- `Sigma.radial_direction_second_derivative`
- `Sigma.radial_euclidean_laplacian`

### final:R4 — Spatial countermodels retaining the complete intrinsic structure

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L754); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Squared norm is orthogonally additive
- Quartic norm fails orthogonal additivity on the designated plane
- Every packet satisfying the intrinsic scalar, probability, operator, characteristic-series, and canonical-Gaussian facts has three independent spatial extensions retaining the identical packet and all five families of facts
- Explicit dimension-two quartic, dimension-two squared-norm, and dimension-one squared-norm extension witnesses
- The dimension-two residual coefficient is exactly -1/(4x^2) and nonzero on the positive ray
- The dimension-one residual coefficient vanishes

Mapped Lean declarations:

- `Sigma.norm_square_orthogonal_additive`
- `Sigma.quartic_not_orthogonal_additive_of_pair`
- `Sigma.radial_residual_cancellation`
- `Sigma.Closure.CompleteIntrinsicContextAt`
- `Sigma.Closure.planeQuarticPacket`
- `Sigma.Closure.planeSquaredNormPacket`
- `Sigma.Closure.lineSquaredNormPacket`
- `Sigma.Closure.spatial_countermodels_retain_context`
- `Sigma.Closure.dimension_two_radial_residual_coefficient`
- `Sigma.Closure.dimension_one_radial_residual_coefficient`

### final:B1 — Rational trees, Euclidean decoding, and the matrix monoid

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L796); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Every positive rational has exactly one Calkin--Wilf word
- Positive reduced fractions and forced parent steps
- Native nonnegative integral determinant-one matrices are exactly the free word products of the displayed native generators, with append mapped to matrix multiplication and the identity included
- Actual Stern-Brocot column matrices evolve by right multiplication, with positive reduced mediants, determinant-one adjacency, correctly ordered upper/lower endpoints and initial infinity/zero represented without totalized division at infinity
- Chronological Calkin-Wilf paths apply the first letter first, and the actual Stern-Brocot mediant equals the chronological Calkin-Wilf value of the reversed word; complete enumeration and the distinct LR examples hold
- Ordinary finite continued-fraction evaluation with exactly the paper's intrinsic canonical digit conditions, unique existence for every positive rational and root expansion [1]
- Actual two-sided equivalences between canonical continued fractions, complete tree paths and intrinsically normalized oriented runs, not restricted to an encoder image
- Actual parent subtraction along every word reaches the root; maximal nonterminal runs in both orientations have the Euclidean quotient length and the true remainder state
- For reduced terminal fractions both orientations have quotient-minus-one run length, with zero run at the root; terminal digit one is removed by the ordinary continued-fraction identity

Mapped Lean declarations:

- `Sigma.cwValue_positive`
- `Sigma.cwValue_injective`
- `Sigma.cw_positive_rational_exists_unique`
- `Sigma.cw_parent_below`
- `Sigma.cw_parent_above`
- `Sigma.rationalTreeGenerator`
- `Sigma.rationalTreeMatrix`
- `Sigma.rational_tree_matrix_append`
- `Sigma.rational_tree_matrix_determinant`
- `Sigma.rational_tree_matrix_exists_unique`
- `Sigma.nonnegative_integer_matrix_exists_unique`
- `Sigma.rational_tree_matrix_positive_rows`
- `Sigma.rational_tree_matrix_mediant`
- `Sigma.chronologicalCwValue`
- `Sigma.chronological_cw_left`
- `Sigma.chronological_cw_right`
- `Sigma.sternBrocotMatrix`
- `Sigma.stern_brocot_right_step`
- `Sigma.stern_brocot_left_columns`
- `Sigma.stern_brocot_right_columns`
- `Sigma.stern_brocot_cw_reversal`
- `Sigma.chronological_cw_LR`
- `Sigma.stern_brocot_LR`
- `Sigma.stern_brocot_enumeration`
- `Sigma.stern_brocot_mediant_reduced`
- `Sigma.sternBrocotLower`
- `Sigma.sternBrocotUpper`
- `Sigma.stern_brocot_ordered_endpoints`
- `Sigma.stern_brocot_initial_endpoints`
- `Sigma.finiteCFValue`
- `Sigma.CanonicalPositiveCF`
- `Sigma.canonical_positive_cf_iff_digits`
- `Sigma.canonical_cf_exists_fraction`
- `Sigma.canonical_cf_exists_unique`
- `Sigma.canonical_cf_injective`
- `Sigma.canonical_cf_head_floor`
- `Sigma.canonical_cf_euclidean_head`
- `Sigma.cw_path_canonical_cf`
- `Sigma.canonical_cf_cw_path`
- `Sigma.canonical_cf_root`
- `Sigma.NormalOrientedRuns`
- `Sigma.orientedRunEquiv`
- `Sigma.expand_oriented_runs`
- `Sigma.oriented_runs_expand`
- `Sigma.canonicalCFPathEquiv`
- `Sigma.canonical_cf_path_value`
- `Sigma.canonicalCFRunEquiv`
- `Sigma.cw_subtraction_step`
- `Sigma.cw_subtraction_orientation`
- `Sigma.cw_subtract_prefix`
- `Sigma.cw_subtract_to_root`
- `Sigma.rational_subtraction_right_fraction`
- `Sigma.rational_subtraction_left_fraction`
- `Sigma.euclidean_right_nonterminal_run`
- `Sigma.euclidean_left_nonterminal_run`
- `Sigma.euclidean_terminal_reduced`
- `Sigma.euclidean_terminal_left_reduced`
- `Sigma.euclidean_root_zero_run`
- `Sigma.finite_cf_remove_terminal_one`

### final:B2 — Marked Farey branches and full-domain scalar recovery

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L889); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Both marked inverse formulas, including the common endpoint where both forward formulas equal one
- Exact closed-interval branch images including endpoints
- Increasing and decreasing branch orientations
- Full-domain actual interval integral recovery of I for every t>0, including 0<t<1 and t=1
- Same generator action for every nonnegative real input, hence every positive rational input, but different smooth strictly convex potential counterexample
- Identification of arbitrary child-map candidates from the complete numerically labelled tree
- Three-point Mobius identification and full rational extension of both canonical child maps from all positive-rational data
- Connected real analytic extension from positive-rational data on the whole interval (-1,infinity), with analyticity of the canonical Farey map proved
- Same abstract binary tree admits distinct injective positive numerical labelings, witnessing failure to recover numerical markings

Mapped Lean declarations:

- `Sigma.farey_left_inverse`
- `Sigma.farey_right_inverse`
- `Sigma.farey_left_strictMono`
- `Sigma.farey_right_strictAnti`
- `Sigma.farey_left_surjective`
- `Sigma.farey_right_surjective`
- `Sigma.farey_left_integral`
- `Sigma.compact_smooth_perturbation_strictConvex`
- `Sigma.smooth_potential_extension_counterexample`
- `SigmaBase.potential_hasDerivAt`
- `Sigma.cw_labelled_child_maps_identify`
- `Sigma.mobius_left_three_point_extension`
- `Sigma.mobius_right_three_point_extension`
- `Sigma.mobius_left_positive_rational_extension`
- `Sigma.mobius_right_positive_rational_extension`
- `Sigma.analytic_extension_from_positive_rationals`
- `Sigma.analytic_farey_left_extension`
- `Sigma.unlabelled_binary_tree_distinct_numerical_labels`

### final:B3 — Exact collisions and complete labelled arithmetic transport

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L953); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Exact collision criterion
- Every collision breaks multiplication after any dilation greater than one
- Intrinsic alternative code injectivity
- Generic injective-image multiplication, unit, associativity, commutativity and divisibility
- Existence of the prescribed image operation iff injectivity on the exact n>=2 carrier
- A genuinely separate abstract unit and labelled multiplicative-monoid isomorphism from positive integers preserving the original code at every n>=2
- Exact shifted placement sampling identity with the fixed additive level, for all natural indices
- Unique finite factorization into marked numerical-prime labels through two actual prime-multiset inverse maps
- Actual divisibility iff prime-multiset inclusion, valuation maximum including zero and the unit, and additive valuation under multiplication
- Transported gcd and lcm with actual divisibility universal properties and valuation min/max formulas
- Bijection of actual monoid divisors with submultisets of the finite prime factorization, preserving the divisibility order
- Every numerical-prime permutation induces a multiplicative automorphism; the explicit two/three swap changes numerical prime names and fails addition
- Native irreducibles are exactly the marked numerical primes, with the adjoined unit excluded
- Total and distinct factor counts are finite and have the exact valuation-sum and positive-support cardinality formulas
- Actual finite enumeration of all native divisors and the exact product of valuation-plus-one divisor-count formula
- The actual divisor lattice is bijective to the finite Cartesian product of exponent intervals, with coordinate equal to each valuation and native divisibility iff componentwise order, including the empty support of the unit
- Labelled totient has the exact prime-power factorization formula, unit value and coprime-residue counts both below n and on 1 through n; the prime-swap automorphism changes its value
- Original nonunital reflexive divisibility is exactly equality or multiplication by another original element, and the coprime labels two and three have the separately adjoined unit as gcd
- Actual label-preserving monoid equivalences between distinct injective analytic linear and square encodings, and between different additive levels in the same injective placed log-affine family, witness real-embedding and analytic-shape nonidentification
- Actual finite-divisor Dirichlet convolution over arbitrary commutative coefficient rings, with derived quotient identity, associativity, commutativity and delta identity
- Actual valuation-based Mobius formula, unit value, divisor-sum delta identity and Mobius inversion in both directions
- Within the original positive-parameter placed family, an explicitly injective code on n>=2 whose numerical index-one value collides with the value at two
- Every arbitrary prescription at marked prime powers of positive exponent extends uniquely to a normalized multiplicative function, with exact finite product over actual valuation support and intrinsic gcd-one coprimality
- Over every field the unnormalized coprime-multiplicativity equation holds exactly for the zero function or a normalized multiplicative function; zero is not normalized

Mapped Lean declarations:

- `Sigma.placed_collision_iff`
- `Sigma.every_placed_collision_breaks_multiplication`
- `Sigma.intrinsic_alternative_injective`
- `Sigma.transportedProduct_encode`
- `Sigma.transportedProduct_assoc`
- `Sigma.transportedProduct_comm`
- `Sigma.transportedUnit_mul`
- `Sigma.transported_divisibility`
- `Sigma.IntegerCodeIndex`
- `Sigma.placedIntegerCode`
- `Sigma.placed_integer_operation_iff`
- `Sigma.integerCodeToPositive`
- `Sigma.integer_code_unit_extension_bijective`
- `Sigma.integerCodeUnitEquiv`
- `Sigma.labelledImageEquiv`
- `Sigma.labelled_image_unit_separate`
- `Sigma.labelled_image_encode`
- `Sigma.placed_shifted_integer_sampling`
- `Sigma.labelledFactors`
- `Sigma.labelledValuation`
- `Sigma.labelled_factorization_inverse`
- `Sigma.labelled_factorization_unique`
- `Sigma.labelled_factors_mul`
- `Sigma.labelled_dvd_iff`
- `Sigma.labelled_dvd_iff_factors`
- `Sigma.labelled_valuation_maximum`
- `Sigma.labelled_valuation_mul`
- `Sigma.labelledGcd`
- `Sigma.labelledLcm`
- `Sigma.labelled_gcd_universal`
- `Sigma.labelled_lcm_universal`
- `Sigma.labelled_valuation_gcd`
- `Sigma.labelled_valuation_lcm`
- `Sigma.labelledDivisorEquiv`
- `Sigma.labelled_divisor_order`
- `Sigma.primePermutationMonoid`
- `Sigma.prime_permutation_on_prime`
- `Sigma.swap_two_three_two`
- `Sigma.swap_two_three_not_additive`
- `Sigma.pnat_isUnit_iff_one`
- `Sigma.pnat_irreducible_iff_prime`
- `Sigma.labelled_irreducible_iff`
- `Sigma.labelledOmega`
- `Sigma.labelledLittleOmega`
- `Sigma.labelled_factor_count`
- `Sigma.labelled_valuation_support`
- `Sigma.labelled_distinct_factor_count`
- `Sigma.labelledDivisors`
- `Sigma.mem_labelled_divisors`
- `Sigma.labelled_divisor_count`
- `Sigma.FactorBox`
- `Sigma.factorsFromBox`
- `Sigma.count_factors_from_box`
- `Sigma.count_factors_from_box_outside`
- `Sigma.factorBoxEquiv`
- `Sigma.factor_box_order`
- `Sigma.labelledDivisorBoxEquiv`
- `Sigma.labelled_divisor_box_coordinate`
- `Sigma.labelled_divisor_box_order`
- `Sigma.labelledTotient`
- `Sigma.labelled_totient_one`
- `Sigma.labelled_totient_formula`
- `Sigma.labelled_totient_residue_count`
- `Sigma.labelled_totient_positive_residue_count`
- `Sigma.prime_swap_changes_totient`
- `Sigma.original_image_reflexive_divisibility`
- `Sigma.labelled_coprime_gcd_is_unit`
- `Sigma.labelledImageChangeEquiv`
- `Sigma.labelled_image_change_preserves_labels`
- `Sigma.linear_integer_code_injective`
- `Sigma.square_integer_code_injective`
- `Sigma.analyticCodeCounterexampleEquiv`
- `Sigma.analytic_code_counterexample_shapes`
- `Sigma.placed_unit_parameters_injective`
- `Sigma.placedLevelCounterexampleEquiv`
- `Sigma.placed_level_counterexample_values`
- `Sigma.labelledArithmeticEquiv`
- `Sigma.labelled_quotient_mul`
- `Sigma.labelled_quotient_index`
- `Sigma.labelled_convolution_sum`
- `Sigma.labelled_convolution_assoc`
- `Sigma.labelled_convolution_comm`
- `Sigma.labelled_convolution_one_left`
- `Sigma.labelled_convolution_one_right`
- `Sigma.labelled_moebius_one`
- `Sigma.labelled_moebius_formula`
- `Sigma.labelled_moebius_convolution`
- `Sigma.labelled_sum_moebius`
- `Sigma.labelled_moebius_inversion`
- `Sigma.labelled_moebius_inversion_iff`
- `Sigma.unit_collision_parameter_bound`
- `Sigma.unit_collision_code_strictAnti`
- `Sigma.unit_collision_original_injective`
- `Sigma.unit_collision_at_one`
- `Sigma.placed_unit_collision_witness`
- `Sigma.LabelledCoprime`
- `Sigma.IsLabelledMultiplicative`
- `Sigma.labelled_arithmetic_multiplicative_iff`
- `Sigma.labelledPrimePowerExtension`
- `Sigma.labelled_prime_power_extension_multiplicative`
- `Sigma.labelled_prime_power_extension_prescribed`
- `Sigma.labelled_multiplicative_unique`
- `Sigma.labelled_prime_power_values_exists_unique`
- `Sigma.labelled_coprime_iff_gcd_one`
- `Sigma.labelled_valuation_native_factorization`
- `Sigma.labelled_multiplicative_product`
- `Sigma.labelled_prime_power_extension_injective`
- `Sigma.labelled_nonzero_multiplicative_normalized`
- `Sigma.labelled_unnormalized_multiplicative_dichotomy`
- `Sigma.labelled_unnormalized_multiplicative_iff`
- `Sigma.labelled_zero_not_normalized`

### final:B4 — Numerical Euler products and the full multiset inverse

Lean coverage: **complete**. [Paper statement](../paper/sections/series-realizations.tex#L1106); [independent coverage map](formalization/current-realizations-audit.json).

Mathematical content formalized in Lean:

- Actual complex numerical zeta series and its absolute-summability half-plane
- Actual convergent HasProd over native positive-integer primes equals the numerical zeta series for every complex s with Re(s)>1, by reuse of Mathlib's native Euler product
- For an arbitrary real generator set q>1 with positive integer multiplicities, convergence of the actual Euler product to a positive value at one positive real argument derives the logarithmic sum, finiteness below every real bound, countability and a least generator when nonempty, without assuming any of these properties
- At every positive argument with a positive convergent product, its value is one exactly when the generator set is empty; a nonempty product is strictly greater than one
- Removing any generator removes its entire multiplicity factor and derives a genuine convergent residual HasProd with value Z divided by that factor and strictly positive value; no multiplicative independence is assumed
- For the supplied arbitrary native self-adjoint operator with complete integer eigenbasis, the exact maximal weighted domain and diagonal action are derived. Its actual complex power is nuclear/trace-class iff Re(s)>1 for every complex parameter, including exclusion of unbounded powers. Its actual basis-independent operator trace is native riemannZeta; power one is the genuine two-sided bounded inverse of 1+A
- Both literal least-generator and multiplicity limits follow from terminal-ray positive convergence. Full-factor erasure and finite-predecessor induction derive equality of the numerical multiplicity functions at every real argument, without multiplicative independence. The constructed reconstruction map is a left inverse on the stated raw presentation class

Mapped Lean declarations:

- `Sigma.operator_complex_zeta_eigenvalue_summable_iff`
- `Sigma.operator_zeta_eigenvalue_hasSum`
- `Sigma.numerical_zeta_series_euler_product`
- `Sigma.numerical_zeta_euler_product_identity`
- `Sigma.real_euler_product_log_hasSum`
- `Sigma.real_euler_generators_bounded_finite`
- `Sigma.real_euler_generators_countable`
- `Sigma.real_euler_generators_least`
- `Sigma.real_euler_product_gt_one`
- `Sigma.real_euler_product_eq_one_iff_empty`
- `Sigma.real_euler_product_remove_generator`
- `Sigma.IsNuclearOperator`
- `Sigma.nuclear_trace_basis_independent`
- `Sigma.diagonal_operator_nuclear_iff`
- `Sigma.integer_eigenbasis_operator_eq`
- `Sigma.integer_eigenbasis_domain_iff`
- `Sigma.integer_eigenbasis_shift_inverse`
- `Sigma.integer_zeta_operator_nuclear_iff`
- `Sigma.integer_zeta_operator_trace`
- `Sigma.integer_zeta_trace_any_basis`
- `Sigma.integer_eigenbasis_zeta_trace`
- `Sigma.real_euler_multiset_recovery_limits`
- `Sigma.real_euler_remove_generator_terminal_convergence`
- `Sigma.RealEulerPresentation.multiplicityAt_eq_of_same_tail`
- `Sigma.RealEulerPresentation.generators_eq_of_same_tail`
- `Sigma.real_euler_reconstruction_left_inverse`
- `Sigma.real_euler_reconstruction_generators`

### final:identification — Identification and a retained context

Lean coverage: **definition**. [Paper statement](../paper/sections/closure.tex#L10); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Generic encoding/decoding through equivalences and dependent context recipes represent portions of the definition.

Mapped Lean declarations:

- `Sigma.presentationEquivalence`
- `Sigma.Closure.lossEquivalence`
- `Sigma.Closure.densityEquivalence`
- `Sigma.Closure.canonical_realization_fibre`

### final:global-A — Intrinsic uniqueness and reconstruction closure

Lean coverage: **partial**. [Paper statement](../paper/sections/closure.tex#L74); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Exact differential subgraph and intrinsic H/I/p inverses; generic transport and uniqueness for already supplied equivalences.
- Composition, uniqueness and round trips once native presentation equivalences are given.

Mapped Lean declarations:

- `Sigma.differential_core_iff`
- `Sigma.differential_core_identifies`
- `Sigma.Closure.intrinsic_loss_reconstruction`
- `Sigma.Closure.intrinsic_density_reconstruction`
- `Sigma.Closure.intrinsic_density_inverse`
- `Sigma.Closure.presentation_intrinsic_unique`
- `Sigma.presentationEquivalence_roundtrip`
- `Sigma.Closure.presentation_transport_composes`
- `Sigma.presentationEquivalence`

Remaining Lean formalization:

- Construct the full typed E_Sigma collection with each actual candidate class and observation.
- Instantiate each node's encoding and identifying inverse, with both round trips on its stated solution class.
- Supply the native missing local inverses identified by the probability, operator and realization audits before claiming global closure.
- Instantiate mutual reconstruction through the same calibrated intrinsic object for every E_Sigma node with all candidate classes and marks retained.

### final:global-E — Canonical realization fibres

Lean coverage: **partial**. [Paper statement](../paper/sections/closure.tex#L139); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Generic context-dependent recipe bookkeeping; genuine matrix uniqueness components; native offspring PGF identification components.

Mapped Lean declarations:

- `Sigma.Closure.canonical_realization_fibre`
- `Sigma.matrixPotential_spectral`
- `Sigma.spd_scalar_block_lift_unique`
- `Sigma.spd_positive_rank_lift_unique`
- `Sigma.native_offspring_pgf_characterization`

Remaining Lean formalization:

- The six fixed-context existence/uniqueness and reverse-observation assertions must be assembled from actual native context theorems.
- In particular generic unique y satisfying y=recipe(c,s) is not uniqueness among candidates meeting identifying observations; it supplies none of the missing actual convolution, self-adjoint operator, Gaussian radial, iid branching-tree or universal Thom content.

### final:global-C — Relative irredundancy and its deletion witnesses

Lean coverage: **partial**. [Paper statement](../paper/sections/closure.tex#L173); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Intrinsic component equivalences and exact admissible placement inverse; both concrete placement deletions; analytic independent perturbations, anchors, unit curvature and uniform strict-convexity neighborhood.
- Placement and spatial deletion witnesses, retained-context decoder obstruction, actual path/star Borel-size probability-law witness, analytic perturbation groundwork.

Mapped Lean declarations:

- `Sigma.Closure.intrinsic_loss_reconstruction`
- `Sigma.Closure.intrinsic_density_reconstruction`
- `Sigma.Closure.intrinsic_density_inverse`
- `Sigma.Closure.placementEquivalence`
- `Sigma.Closure.placement_exact_reconstruction`
- `Sigma.Closure.placed_candidate_exact_reconstruction`
- `Sigma.Closure.placement_scale_deletion`
- `Sigma.Closure.placement_offset_deletion`
- `Sigma.Closure.perturbed_intrinsic_analytic`
- `Sigma.Closure.perturbed_intrinsic_anchors`
- `Sigma.Closure.perturbed_intrinsic_identical_iff`
- `Sigma.Closure.perturbed_intrinsic_strictConvex_near_zero`
- `Sigma.Closure.retained_context_deletion`
- `Sigma.Closure.no_placement_decoder_without_scale`
- `Sigma.Closure.no_placement_decoder_without_offset`
- `Sigma.Closure.plane_composition_deletion`
- `Sigma.Closure.plane_scale_deletion`
- `Sigma.Closure.spatial_dimension_deletion`
- `Sigma.borel_size_does_not_identify_random_tree`
- `Sigma.Closure.perturbations_independent`

Remaining Lean formalization:

- A nonzero perturbation with exact integral normalization and stated endpoint behavior in the relaxed deletion universe.
- Complete native external packet deletion witnesses and their independent expansion with other packets fixed.
- Global sufficient decomposition depends on full global-A/B and global-E.
- Normalized nontrivial intrinsic deletion witness including endpoint behavior.
- Native coordinate relabelling, Gamma shape-two/three isospectral stationary-law, uniform-angle/fixed-direction vector-law, Gamma-subordinator/time-scaled-variable process, spectral matrix perturbation, RP2 complex-line, and prime-generator permutation witnesses wherever not supplied in their local sections.
- Assembly preserving every other retained packet and changing each named target.

### final:global-F — Boundary of scalar reconstruction

Lean coverage: **partial**. [Paper statement](../paper/sections/closure.tex#L246); [independent coverage map](formalization/current-core-closure-audit.json).

Mathematical content formalized in Lean:

- Placement, tree-size and spatial non-identification components; nonnegative global orthogonal-additivity rigidity; exact radial differential-expression cancellation iff D=1 or 3 and D>=2 selection; different profile cancellation.

Mapped Lean declarations:

- `Sigma.Closure.no_placement_decoder_without_scale`
- `Sigma.Closure.no_placement_decoder_without_offset`
- `Sigma.Closure.no_spatial_observable_decoder`
- `Sigma.Closure.no_spatial_dimension_decoder`
- `Sigma.Closure.spatial_observable_reconstruction`
- `Sigma.Closure.spatial_radial_cancellation`
- `Sigma.Closure.spatial_radial_dimension_three`
- `Sigma.Closure.radial_cancellation_does_not_identify_profile`
- `Sigma.borel_size_does_not_identify_random_tree`

Remaining Lean formalization:

- Full scalar non-reconstruction list requires the remaining actual stationary/vector/process/matrix/topological/arithmetic witnesses and retained-packet assembly.

## Labelled equations

Equations within named statements are component-level checks of those statements, not separate paper results.

### final:todd-twists

Parent named statement: **final:F1**. Lean coverage: **complete**.

- `Sigma.formal_twisted_todd_coeff`
- `Sigma.todd_twist_polynomial_identity`
- `Sigma.formal_twisted_todd_coeff_over_Q_algebra`

### final:todd-arbitrary-power

Parent named statement: **none (standalone equation)**. Lean coverage: **complete**.

- `Sigma.formalBinomialPower`
- `Sigma.scalarFallingFactorial`
- `Sigma.formal_binomial_power_nat`
- `Sigma.normalized_sub_one_power_coefficient_zero`
- `Sigma.positiveDegreeMultiplicities`
- `Sigma.mem_positiveDegreeMultiplicities`
- `Sigma.formal_binomial_power_exact_multiplicities`
- `Sigma.todd_arbitrary_power_coefficient`
- `Sigma.formalBinomialPowerOver`
- `Sigma.scalar_falling_factorial_nat_inverse_over`
- `Sigma.formal_binomial_power_over_nat`
- `Sigma.multinomial_factorial_inverse_over`
- `Sigma.formal_binomial_power_over_exact_multiplicities`
- `Sigma.todd_arbitrary_power_coefficient_over_Q_algebra`
- `Sigma.formal_binomial_power_over_field`
- `Sigma.formal_todd_over_constant`
- `Sigma.formal_todd_over_denominator`

### final:TAL

Parent named statement: **final:F2**. Lean coverage: **complete**.

- `Sigma.formal_ahat_to_todd`
- `Sigma.formal_todd_to_L`
- `Sigma.formal_L_to_todd`

### final:exponential-recovery

Parent named statement: **final:F2**. Lean coverage: **complete**.

- `Sigma.formal_todd_recovers_exponential`
- `Sigma.formal_L_recovers_exponential`

### final:chi-inverse

Parent named statement: **final:F2**. Lean coverage: **complete**.

- `Sigma.formal_chi_recovers_todd`
- `Sigma.formal_chi_over_recovers_todd`

### final:Thom-comparison

Parent named statement: **final:F4**. Lean coverage: **missing**.

- Remaining Lean formalization: Actual uniquely defined Thom correction

### final:RR

Parent named statement: **final:F4**. Lean coverage: **missing**.

- Remaining Lean formalization: Actual Riemann--Roch Gysin comparison

### final:matrix-potential

Parent named statement: **final:M1**. Lean coverage: **complete**.

- `Sigma.matrixPotential_spectral`
- `Sigma.spd_positive_rank_lift_unique`

### final:matrix-gradient

Parent named statement: **final:M2**. Lean coverage: **complete**.

- `Sigma.matrixPotential_fderiv`

### final:matrix-hessian

Parent named statement: **final:M2**. Lean coverage: **complete**.

- `Sigma.matrixPotential_second_fderiv`
- `Sigma.matrix_hessian_metric`

### final:matrix-divergence

Parent named statement: **final:M2**. Lean coverage: **complete**.

- `Sigma.matrix_actual_bregman`

### final:matrix-conjugate

Parent named statement: **final:M2**. Lean coverage: **complete**.

- `Sigma.matrix_fenchel_conjugate_formula`
- `Sigma.matrix_fenchel_conjugate_finite`
- `Sigma.matrix_fenchel_conjugate_infinite`
- `Sigma.matrix_fenchel_equality_iff`

### final:radial-residual

Parent named statement: **final:R3**. Lean coverage: **complete**.

- `Sigma.radial_residual`

### final:tree-integral

Parent named statement: **final:B2**. Lean coverage: **complete**.

- `Sigma.farey_left_integral`

### final:integer-collision

Parent named statement: **final:B3**. Lean coverage: **complete**.

- `Sigma.placed_collision_iff`

## Preserved excluded experiment

The pre-existing local `lean/SigmaProbCumulantCalibration.lean` experiment is not imported or credited. It remains preserved as local work; the completed P4 cumulant formalization is mapped to the other verified modules.
