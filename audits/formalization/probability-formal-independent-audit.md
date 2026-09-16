# Independent statement audit: P3, P4, and P9

This audit compares `probability.tex` with the actual Lean declarations and their proof dependencies. It is a statement audit, separate from the parent agent's aggregate compilation and axiom audit. No probability proof was edited during this review. All declaration names below belong to `SigmaFinal` unless another namespace is shown.

The review found no hidden regularity or source-support premise in the Gumbel inverse or in the independent-residual inverse. The displayed P3 and P9 statements are now fully covered. Two P4 interface obligations identified during review were resolved by new compiled wrappers, which were independently re-read; P4's cumulant alternative and explicit Lambert-W target formulas remain separate obligations.

## P3: two marked max laws

Draft location: `probability.tex`, `final:P3`.
Formal source: `../lean/SigmaFinalProbGumbel.lean`.

The draft starts with a CDF on the whole real line, assumes the two max identities at scales 2 and 3 and the value at zero, and identifies the complete Gumbel CDF. It explicitly does not assume density, smoothness, strict monotonicity, or full support.

The decisive Lean declaration is:

```lean
gumbel_two_max_laws_unique (F : Real -> Real) (hmono : Monotone F)
  (h2 : forall x, F (x + Real.log 2) ^ 2 = F x)
  (h3 : forall x, F (x + Real.log 3) ^ 3 = F x)
  (hzero : F 0 = Real.exp (-1)) : F = gumbelCDF
```

Here and in the other displayed signatures, `Real`, `forall`, and `->` are ASCII transcriptions of Lean's notation; the checked declarations are in the cited source.

This is stronger than the draft inverse: only monotonicity from the CDF assumptions is used. `max_two_anchor_bounds` derives `0 < F x` and `F x < 1` for every real `x` from monotonicity, the scale-2 law, and the anchor. These bounds are not supplied as premises. The logarithmic density argument is proved using `log_two_three_dense` and `antitone_two_scale_rigidity`; it does not ask for continuity, measurability, differentiability, or a dense-set conclusion as an assumption.

The converse observations are proved by `gumbel_cdf_anchor`, `gumbel_max_two`, and `gumbel_max_three`. `gumbel_max_law` proves the displayed law for every positive natural number. Positivity, the strict upper bound, and monotonicity of the displayed function are separately proved.

The author subsequently added compiled analytic packaging, which I independently inspected: `gumbel_cdf_continuous`, `gumbel_cdf_tendsto_atTop`, and `gumbel_cdf_tendsto_atBot` give continuity and the exact CDF endpoint limits; `gumbel_cdf_derivative` gives the actual derivative `exp(-x-exp(-x))`; `gumbel_density_intrinsic` identifies it as `p(exp(-x))`; and `gumbel_density_reconstructs` supplies the inverse marked-coordinate formula. These are conclusions about the canonical function, not new premises on the unknown candidate.

The later compiled module `../lean/SigmaFinalProbCDF.lean` closes the native measure packaging as well. I independently inspected its actual Stieltjes construction, probability instance, `gumbel_probability_cdf`, and `gumbel_probability_density`. The last theorem proves equality of the Stieltjes probability with Lebesgue measure weighted by the displayed density; it does not assume that density representation. `gumbel_two_max_probability_unique` starts with an arbitrary real-line Borel probability and only the two CDF max identities and anchor, then identifies the actual measure. Its continuity and monotonicity requirements come from the native CDF API or from the already proved canonical function.

**Verdict:** all claims in the displayed `final:P3` statement are now covered: the exact inverse, canonical probability/CDF, density, and every positive-integer max identity. The explanatory identification of the power of a CDF with the CDF of independent maxima is not separately instantiated in these files; it is standard interpretation in the draft's proof prose, not an additional premise or a gap in the displayed identities.

## P4: the linked deficit and its coordinate pairing

Draft location: `probability.tex`, `final:P4`.
Formal source: `../lean/SigmaFinalProbDeficit.lean`.

The draft candidate is a continuous function on the positive ray, anchored at 1, with strict opposite monotonicities on its two branches and divergence at the two endpoints. Its density is specifically `exp(-1-J(t))`. The observation is the pushforward of that same density by that same potential, together with the pairing of equal-level roots in the same coordinate.

The formal weighted law is literally

```lean
Measure.map J
  ((volume.restrict (Ioi 0)).withDensity (deficitWeight o J))
```

where `deficitWeight v = ENNReal.ofReal (Real.exp (-1-v))` and `o` here denotes function composition. Thus the proof retains the original density--potential linkage. It does not replace the observation by an independent arbitrary level measure, a prescribed width function, or a conclusion disguised as an assumption.

`linked_deficit_law_recovers_level_measure` removes the known strictly positive finite level weight by reciprocal weighting. `linked_deficit_law_recovers_width` then evaluates the recovered pushforwards on sublevel sets. The main theorem derives the required roots and sublevel-interval identity from the strict-branch candidate class using the intermediate value theorem. They are assumptions only in intermediate lemmas, not in the main inverse.

The structure `TwoBranchPotential J` supplies continuity on `Ioi 0`, the anchor, the two strict branch conditions, the two endpoint limits, and global measurability of the real-line representative. `TwoBranchPotential.nonnegative` derives nonnegativity on the positive ray, which the draft includes in the codomain. No differentiability or density of the deficit law is assumed. Integral-one normalization is not an extra formal premise: the inverse is proved for the linked weighted measures without it, which is stronger than uniqueness restricted to normalized candidates.

`linked_deficit_and_involution_unique` identifies any two such candidates pointwise on the positive ray from their equal linked pushforwards and a common upper-to-lower root pairing. `canonical_linked_deficit_identifies_I` specializes the target to `SigmaAudit.potential`; `intrinsic_potential_two_branch` proves that this particular potential belongs to the candidate class.

### Interface findings at the initial review

1. Global `Measurable J` is an extra condition on an arbitrary real-line extension, whereas the draft only gives a function on `Ioi 0`. Positive-ray continuity permits a canonical measurable extension, but a formal wrapper is needed to discharge this condition instead of attributing it to the draft.
2. The common pairing is supplied with `StrictAntiOn j (Ici 1)`. This follows from either candidate's strict branch conditions and the pairing equations; it is not an independent draft hypothesis. A wrapper should derive it.

Both findings were sent to the probability author and parent and have now been resolved:

- `TwoBranchPotential.pair_strictAnti` derives the pairing's strict antitonicity from the existing two-branch and equal-level assumptions.
- `RayPotential` contains only the positive-ray continuity, anchor, strict branches, and endpoint limits. It places no regularity requirement on off-ray values.
- `RayPotential.extension` proves that the function agreeing with `J` on `Ioi 0` and equal to zero elsewhere is a globally measurable `TwoBranchPotential`.
- `linked_deficit_and_involution_unique_on_positive_ray` uses only `RayPotential` inputs, the common root-pairing equations, and equality of the actual linked weighted laws of those canonical extensions. It derives the antitonicity needed internally and concludes `J t = K t` for every `t > 0`.

The new wrapper is an accurate real-line representation of the draft's positive-ray domain: values outside that domain are canonicalized and cannot affect a law built from `volume.restrict (Ioi 0)`. It assumes neither a derivative nor global measurability of the supplied representative. I independently inspected these declarations after the author reported successful compilation and verified that `work/final-SigmaFinalProbDeficit.log` contains no errors.

**Verdict for the linked-law inverse:** the general candidate-pair uniqueness theorem now matches the draft's assumption strength, with normalization and nonnegativity unnecessary as additional premises. The initial interface discrepancies are closed.

### Remaining theorem-group components

The canonical target and its explicit Lambert-W/CDF formulas were subsequently constructed and independently reviewed, as recorded below. The explicitly calibrated full-cumulant alternative remains an unfinished P4 component. Its measure-determinacy bridge and the standard algebraic cumulant-to-moment recurrence are now proved separately, as reviewed below; the stated zeta/Euler target calibration is still required before the draft alternative is counted as covered. The equality of potentials gives equality of the displayed densities by substitution, but a separate native statement of that density equality should be counted only if present. None of these omissions invalidates the linked-law inverse already proved.

### Independently reviewed local-MGF bridge

I also read the complete compiled `../lean/SigmaFinalProbMGFUnique.lean`. Its `finite_measure_local_mgf_unique` assumes arbitrary finite real-line measures and equality and integrability of their actual MGFs for every real parameter in a common interval `|s| < a`, with `a > 0`. It derives an absolute-exponential dominating function from the MGFs at `a/2` and `-a/2`, proves holomorphicity on the corresponding complex strip using dominated differentiation, and applies the analytic identity theorem to a real sequence accumulating at zero. The imaginary axis then supplies equal actual characteristic integrals, and the independently checked finite-measure Fourier uniqueness theorem finishes the proof. No source support, density, moment, or hidden identification premise is added. This is the exact usual local-MGF determinacy statement. It does not by itself prove that equality of all cumulants gives equality of those MGFs.

I subsequently inspected the complete `../lean/SigmaFinalProbMomentUnique.lean`. `gamma_deficit_moments_identify_real_line_probability` assumes only that the candidate is an actual real-line probability with finite ordinary moments equal to the actual target moments. Its exponential envelope is derived from the even-moment cosh series and the target envelope; there is no additional candidate support or exponential-integrability premise. The standard algebraic moment-cumulant recurrence is represented by `AlgebraicCumulantRecurrence`. Equality of a common recurrence gives equality of all probability moments by induction. Accordingly `gamma_deficit_algebraic_cumulants_identify` is a valid inverse conditional on that recurrence for both candidate and target. Its target recurrence is explicitly assumed, so this declaration does not yet evaluate the target cumulants as the draft's zeta/Euler constants. This remaining calibration has not been replaced by an assumption advertised as a proof.

The separately compiled `../lean/SigmaFinalProbDeficitDomain.lean` proves `gamma_deficit_mgf_integrable_iff`: the actual target MGF integrand is integrable exactly for `s < 1`. Its declaration matches the sharp domain without an extra endpoint or positivity assumption.

## P9: an explicit independent residual on the whole real line

Draft location: `probability.tex`, `final:P9`.
Formal sources: `../lean/SigmaFinalProbCharacteristic.lean`, `../lean/SigmaFinalProbContraction.lean`, `../lean/SigmaFinalProbResidual.lean`, and `../lean/SigmaFinalProbGamma.lean`. The law-level uniqueness step also uses `operator_full_line_mixing_characterization` from `../lean/SigmaFinalOpMixing.lean`.

### The actual residual and the linked original law

The construction is native measure theory:

```lean
unitExpProbability = gammaMeasure 1 1
atomExpMixture c = ENNReal.ofReal c * dirac 0
                + ENNReal.ofReal (1-c) * unitExpProbability
independentAffineSum mu nu c =
  Measure.map (fun z => c * z.1 + z.2) (mu.prod nu)
gammaResidualProbability c =
  independentAffineSum (atomExpMixture c) (atomExpMixture c) 1
```

The `*` in the mixture transcription is measure scalar multiplication. The actual definition uses Lean's scalar-action notation. The repeated mixture in the product measure explicitly encodes two independent, identically distributed summands.

The source proves that the exponential, mixture, and residual are probability measures for the required coefficient ranges, proves their nonnegative support, and computes the residual Laplace transform and zero atom. `gamma_residual_zero_atom` gives the value `ENNReal.ofReal (c^2)`. `gamma_residual_scale_identified` then identifies any two parameters in `[0,1]` whose actual residual measures coincide.

The main law-level inverse is:

```lean
canonical_residual_identifies_gamma
  (mu : Measure Real) [IsProbabilityMeasure mu]
  (c : Real) (hc0 : 0 <= c) (hc1 : c < 1)
  (hdecomp : independentAffineSum mu (gammaResidualProbability c) c = mu) :
  mu = gammaProbability
```

The same `mu` appears as the first product marginal and as the resulting law. This is precisely the required source-law linkage. Independence is encoded by `mu.prod nu`, rather than inferred from a marginal observation or imposed on an unrelated source.

There is no source support, density, moment, or transform hypothesis in this declaration. `independent_contraction_positive_support` first derives nonnegative source support from the independent affine stationarity equation, nonnegative residual, and `0 <= c < 1`. Its proof uses an explicitly bounded continuous detector of the negative ray, so it introduces no integrability assumption on the source. The general residual theorem takes nonnegative support and the residual Laplace formula as premises for the residual alone; the explicit canonical wrapper supplies both by preceding theorems about the actual constructed measure.

Only after source support has been derived does the proof use bounded Laplace integrands, dominated convergence at zero, and telescoping. The final call to `operator_full_line_mixing_characterization` requires only a finite positive real-line measure and the proved integer Laplace observations; it does not reintroduce a source support or moment premise.

`gamma_canonical_self_decomposition` proves the actual converse measure identity, even for `0 <= c <= 1`. Consequently draft clauses 1 and 2 are proved at the product-law level, including `c=0`. An additional random-variable wrapper spelling out the coordinate variables and their independence would be a presentation bridge; the product-space construction already supplies the concrete joint law and both marginals.

**Verdict for the explicit independent-decomposition inverse:** exact input strength and exact law conclusion. The residual is constructed, its relevant properties are derived, and the original law is linked correctly. No assumption of the desired source law was found.

### The characteristic alternative and the completed uniqueness bridge

`probabilityCharacteristic` is the actual complex characteristic integral. `probability_characteristic_continuous` proves its continuity for every finite measure, and `probability_characteristic_zero` proves its value at zero for a probability. Neither property is an extra premise in the probability-valued theorem.

`linked_probability_characteristic` assumes exactly the draft's factorization for that actual characteristic integral and proves its equality to the function `gammaCharacteristic`, defined as `(1-i*x)^(-2)`. Its abstract engine, `linked_characteristic_rigidity`, assumes continuity only at zero and normalization there; these facts are discharged in the measure-valued wrapper. `independent_affine_sum_characteristic` proves actual factorization for the product construction.

The subsequently compiled `../lean/SigmaFinalProbFourier.lean` closes the two actual transform evaluations. I independently inspected `gamma_probability_characteristic` and `gamma_residual_characteristic`: they evaluate the characteristic integrals of the constructed measures rather than assume those evaluations. The exponential integral is computed first; the actual independent exponential pair is identified with Gamma using the proved Laplace inverse; independence then gives the Gamma formula. The residual computation uses the explicit mixture and its product construction, with only `0 <= c <= 1` as the parameter restriction.

`canonical_decomposition_characteristic_equation` now gives clause 2 to clause 3 for the explicit residual, with an arbitrary probability `mu` and the same linked product-law equality as in the draft. It adds no source support, regularity, or moment assumption. `gamma_characteristic_equation` gives clause 1 to clause 3.

The final characteristic-to-law bridge is now compiled in `../lean/SigmaFinalProbFourierUnique.lean`. I independently read its full proof and signature. `finite_measure_characteristic_unique` takes arbitrary finite Borel measures on the entire real line and equality of their actual characteristic integrals, and concludes equality of measures. It adds no support, density, moments, or regularity premise. Its proof uses native density of Fourier monomials on the compact circle, equality of all scaled circle pushforwards, and decoding maps which eventually agree exactly with the identity at each real point. Dominated convergence for bounded measurable tests then identifies integrals; indicator tests identify every measurable set. The proof does not assume measure identification or invoke a circular probability-uniqueness conclusion.

I also inspected the compiled `../lean/SigmaFinalProbInverse.lean`. Its `real_line_residual_characterization` has exactly the draft inputs: an arbitrary real-line probability and `0 <= c < 1`. Its conclusion conjoins the equivalence of Gamma with the actual independent product-law fixed point and the equivalence of Gamma with the displayed actual characteristic equation. The helper `linked_characteristic_identifies_real_line_probability` obtains the previously proved rational transform and applies the new native uniqueness theorem through `gamma_characteristic_identifies_real_line_measure`. This completes the exact three-way equivalence.

`endpoint_one_does_not_restrict` proves the characteristic equation at `c=1` is tautological. The compiled `../lean/SigmaFinalProbBoundaries.lean` also proves `residual_endpoint_one`, identifying the actual constructed residual with `dirac 0`, and `residual_endpoint_one_every_law`, proving the independent stationarity equation at that endpoint for every real-line probability. I independently inspected both declarations. Finally `unlinked_residual_observation_counterexample` in `SigmaFinalProbInverse.lean` supplies two distinct designated source measures, Gamma and `dirac 0`, with the same retained residual observation. Both are native probabilities; their distinction is proved using Gamma's absence of atoms. This is an exact counterexample to identification after forgetting linkage, using a different pair of source laws from the illustrative pair in the draft's proof prose.

**Verdict for the displayed P9 theorem:** complete. The exact equivalence, residual construction, zero atom, parameter recovery, characteristic evaluations, absence of extra source assumptions, endpoint failure, and loss-of-linkage counterexample are covered by the inspected compiled declarations.

## Review record

The findings above were communicated to `/root/latex_probability` and `/root`. The probability author resolved the P4 interface obligations and subsequently closed the P3 measure packaging and P9 characteristic-law bridge. Compilation and axiom status are supplied by the aggregate formal build. This audit confirms the displayed P3 and P9 statements and the general linked-law P4 inverse; it makes no claim that the complete probability draft, including the P4 cumulant alternative, has been formalized.

## Additional bounded review: P1 calibration and P7 ordinary entropy

I independently read the complete compiled `SigmaFinalProbEuler.lean` and `SigmaFinalProbCumulants.lean`. The former derives the Gamma derivatives at one and two using the native Euler--Mascheroni constant, then identifies the actual Gamma logarithmic integral and proves logarithmic integrability. The conclusion `gamma_probability_expected_log = 1 - Real.eulerMascheroniConstant` is a calibrated native integral, with no unnamed constant or target integral assumed. The latter defines cumulants as actual iterated derivatives of the logarithm of the actual MGF. It proves the CGF on the open domain `s < 1`, its successive derivatives there, and hence every positive-order Gamma cumulant `2*n!` at order `n+1`. No extra source assumption or replacement factorial sequence appears. These two additions close the expected-log and cumulant components inspected here; the earlier audit remains scoped to its listed statements.

I also read the complete `SigmaFinalProbEntropyIntegral.lean`. Its calibrated candidate structure contains the actual mass, first-moment, and logarithmic-moment constraints. Mass and first-moment integrability are derived from their nonzero integral values; logarithmic integrability is explicit. The proof derives integrable cross entropy. `CalibratedGammaDensity.finite_entropy_formula` then equates the defined extended entropy with the ordinary negative integral of `f*log f` under the explicit additional assumption that this latter integrand is integrable. Thus it proves the finite-entropy agreement claimed, without silently asserting ordinary finite entropy for every candidate. Concrete Euler-calibrated P7 wrappers were not part of this file and must be assessed separately. No signature mismatch was found in these three reviewed modules.

I then inspected the complete compiled `SigmaFinalProbEntropyCalibration.lean`. It constructs the actual Gamma density with the precise Euler-calibrated constraints, proves its ordinary entropy integral and integrability, and specializes the extended bound and almost-everywhere equality characterization to `1 + Real.eulerMascheroniConstant`. `calibrated_gamma_finite_entropy` connects that same concrete bound to ordinary entropy under exactly the finite-integrand assumption already reviewed. These wrappers cover the displayed P7 bound, equality case, calibration, and finite-entropy agreement. The additional smooth constraint-preserving perturbation example in the proof prose remains separate and is not claimed by these declarations. No additional hypothesis mismatch was found.

## Work-only continuation review during the aggregate freeze

I inspected the complete `work/SigmaFinalProbLogMoments.lean` and `work/SigmaFinalProbEntropyCounterexample.lean` after the author reported compilation. The first derives the needed Gamma logarithmic moments by the actual Gamma derivative recurrence and native differentiated Gamma integral. The counterexample is the explicit density `p(t)*(1+(t^3-10*t^2+24*t-12)/2024)`. Its polynomial has a proved lower bound `-1012` on the positive ray, so the multiplier stays positive. Actual factorial and calibrated logarithmic integrals show that its perturbations of mass, first moment, and logarithmic moment are zero; integrability is proved for each step. Global smoothness is derived from the explicit expression. If the resulting density equaled Gamma almost everywhere on the positive ray, continuity and the native full-support open-set lemma would force equality at one, contradicting its explicit value there. Thus `calibrated_moments_do_not_identify_gamma` is an actual smooth positive normalized counterdensity with the stated calibrated moments, not a formal signed perturbation. This proves the P7 non-identification assertion by an alternative to compact bumps; it does not assert compact support of the perturbation.

I also inspected `work/SigmaFinalProbDeficitDensity.lean`. Its endpoint-aware CDF and derivative arguments prove integrability, mass one, every half-line integral, and finally equality of the actual deficit probability with `volume.withDensity` of the displayed density. The singular endpoint is handled through right continuity of the native CDF and integration on the positive ray, not by assuming differentiability at zero. The density bridge is exact conditional only on the earlier proved CDF derivative declarations. These work-only modules were deliberately outside the frozen aggregate snapshot at this review; their promotion and clean aggregate check remain the parent build responsibility.


## Canonical P4 target and Lambert branches

I independently read the full compiled `SigmaFinalProbCanonicalPair.lean` and `SigmaFinalProbLambert.lean`. The canonical roots are constructed from the actual intrinsic potential by its proved two-branch inverse theorem. The involution is defined from these roots, and its anchor, branch ranges, involutivity, unique fixed point, strict antitonicity, and density preservation are proved. `canonical_deficit_pair_identifies_on_positive_ray` requires the candidate's ray-only hypotheses, preservation of this constructed pairing, and equality of the actual linked candidate pushforward with the native Gamma deficit law. It concludes both equality of potentials and equality of displayed densities on the positive ray. No separately assumed target root data, off-ray measurability, or pairing monotonicity remains in this wrapper.

The negative Lambert branches are defined semantically on `-exp(-1) <= z < 0`: the principal root lies in `[-1,0)` and the lower root in `(-infinity,-1]`, with both satisfying `w*exp(w)=z`. Existence follows from the constructed potential roots and uniqueness from their proved branch monotonicities. Only after these facts are established does the file prove the canonical-root formulas, the actual deficit CDF formula, and both involution formulas. The branch point is included and zero is correctly excluded from the lower negative branch domain. These declarations close the explicit Lambert/CDF target-data gap identified in the initial review. They do not claim the separate smoothness, derivative-at-one, density asymptotics, or calibrated deficit-cumulant formulas. No mismatch was found.


I subsequently read the complete work-only `SigmaFinalProbDeficitSmooth.lean` and `SigmaFinalProbDeficitAsymptotic.lean`, including the native `Asymptotics.IsEquivalent` wrapper. The double divided slope is an actual analytic quadratic factor of the intrinsic potential, and its value `1/2` at one is derived by differentiation. The signed normal coordinate has a proved derivative one. The native analytic inverse function theorem then derives analyticity of the canonical pairing and its derivative `-1` at the branch point; these conclusions are not assumptions. Away from one the nonvanishing potential derivative supplies the local inverse. The asymptotic proof establishes the actual root limits at zero, rewrites the positive-level density times its square root exactly through the quadratic factor, and derives the constant `sqrt(2)/exp(1)`. The final equivalence includes the needed nonzero comparison function on the punctured positive ray. These modules close the reviewed smoothness, branch-point derivative, and density-asymptotic components of P4-data, pending their post-freeze promotion and aggregate build. No mismatch was found.


I also read the complete work-only `SigmaFinalProbDeficitTruncation.lean`. `upperIncompleteGamma` is defined by the actual upper-ray integral. The change-of-scale identity is proved by a native set-integral substitution, then applied to the linked original Gamma density and intrinsic potential. The conditional distribution is the native `ProbabilityTheory.cond gammaProbability (Ici a)`; its normalization is proved from the strictly positive actual Gamma tail. For `a > 0` and `s < 1`, the file proves integrability and the displayed transform with that same tail denominator. No arbitrary truncation law or target transform is assumed. This closes the reviewed conditional-transform component, pending post-freeze promotion and clean build.


## Work-only P2 native relative-entropy review

I independently read the complete `work/SigmaFinalProbRelativeEntropy.lean` and `work/SigmaFinalProbExpEntropy.lean` and their error-free development logs. The definition `finiteRelativeEntropy` is the ordinary real integral of the logarithm of the actual native Radon--Nikodym derivative, taken under its first measure. It is not a universal extended-real KL definition; the displayed uses are justified by separately proved absolute continuity and integrability.

The density lemma identifies the native Radon--Nikodym derivative of two actual weighted measures with the density ratio almost everywhere under the numerator measure. It derives the required sigma-finiteness for the finite-valued numerator density and transfers the equality through absolute continuity. The separate positive-density lemma proves the stated absolute continuity directly. Neither lemma assumes a likelihood ratio or an entropy value.

For Poisson laws, the file proves their native counting-measure densities, all-rate recurrence, actual mean and first-moment integrability. Strictly positive parameters give strictly positive masses at every natural number. The logarithm of the native Radon--Nikodym derivative is then proved equal almost everywhere to `b-a+n*log(a/b)`, and its integrability follows from the actual mean. Taking the integral gives exactly `a*I(b/a)` with the draft's orientation. Both directions of absolute continuity are proved. The use of nonnegative-real parameter types plus strict positivity is equivalent to the draft's positive-real parameter domain.

For exponential laws, `rateExpProbability r` is the actual native `gammaMeasure 1 r`, so the parameter is a rate. The source proves its density relative to Lebesgue measure restricted to the positive ray, its probability normalization for `r>0`, mean `1/r`, and first-moment integrability. The native log derivative is identified almost everywhere as `log(a/b)+(b-a)*t`, with its integrability and mutual absolute continuity proved. Its actual integral is `I(b/a)`, again with the exact draft orientation. Endpoint values outside the positive ray do not affect the restricted density or the native measures.

No extra candidate premise, assumed target transform, or entropy conclusion was found in these two modules. They cover the actual Poisson and exponential KL evaluations and their finite-integral meaning. This review does not yet cover the Gaussian KL formula, tilting, or the complete P2 theorem. These sources remain outside the frozen aggregate record pending the next snapshot.


I next read the complete work-only `SigmaFinalProbGaussianEntropy.lean`, `SigmaFinalProbPoissonTilt.lean`, and `SigmaFinalProbPoissonConjugate.lean`, together with their error-free development logs.

For Gaussian KL, the native distribution is `gaussianReal 0 v`, whose parameter is variance. Its second moment is derived from an actual Gaussian-kernel integration-by-parts identity and the native density normalization; it is not supplied as an extra hypothesis. Square integrability is then proved. The actual source-measure almost-everywhere log Radon--Nikodym derivative, its integrability, and mutual absolute continuity are established. The integral yields exactly `2*D(N(0,a)||N(0,b))=I(a/b)` for strictly positive variances, with the factor two and the reversed ratio relative to the Poisson/Exp formulas intact.

For Poisson tilting, the factorial second moment, ordinary second moment, and centered-square integral are all actual native Poisson integrals or their equivalent summable PMF series; required integrability is proved. The natural rate is explicitly `exp(u)`. The score theorem differentiates the logarithm of the actual native Poisson mass and obtains `n-exp(u)`. Its squared-score integral is proved equal to `exp(u)` using the actual variance. The exponential tilt is defined by weighting the original Poisson(1) measure by `exp(n*u)` and dividing by its actual lintegral. That normalizer is evaluated as `exp(exp(u)-1)`, and singleton measure extensionality identifies the normalized law with native Poisson(exp(u)). There is no assumed tilted target law.

For the Legendre transform, `poissonCenteredConjugate` is literally the `EReal` supremum over all real `u` of `u*z-Lambda(u)`. The interior branch has both a global upper bound and an attained optimizer `log(1+z)`. At `z=-1`, the proof bounds all values by one and derives the matching limit as `u` tends to negative infinity. For `z<-1`, actual unbounded growth of the objective gives `EReal.top`. The complete piecewise theorem therefore proves all three displayed branches, including genuine positive infinity outside the domain. It does not encode the target piecewise formula as the definition.

No assumption-strength, normalization, parameterization, or orientation mismatch was found in these three modules. These findings concern the reviewed P2 components; the separate short slice/boundary wrappers and the previously existing CGF identification declarations require their own recorded scope. The three additions remain work-only pending the next aggregate snapshot.


### P2 completion interface finding (resolved)

I also inspected `SigmaFinalProbKLBoundaries.lean` and the existing compiled `SigmaFinalProbPoisson.lean` and `SigmaFinalProbPoissonInverse.lean`. The short wrappers correctly instantiate all three native entropy slices, all reversed slices, and concrete unequal values at two. The existing shifted Poisson laws use actual shifted means and actual centered CGFs; they are distinct by their proved means. The local CGF inverse applies to arbitrary real-line probability measures, assumes only the finiteness implicit in an ordinary CGF on the supplied neighborhood, derives positivity of the actual exponential integral, and concludes the native (marked centered or uncentered) Poisson law. Integer support is not an extra candidate premise.

One small exact-statement bridge remained at this read: `poisson_relative_entropy_bregman` supplies `Real.log` as the derivative argument of the algebraic Bregman expression, but neither that wrapper nor the baseline `PhaseIV.poisson_mean_bregman` proves the derivative of `Psi(t)=t*log(t)-t+1`. A checked derivative lemma and a wrapper containing `deriv Psi` are required before the draft's derivative-based identity is counted literally. In addition, the map's referenced `PhaseIV.centeredCGF_recovers_exp` proves `1+Lambda'=exp`, rather than the displayed scalar substitution `Lambda(u)=I(exp(u))` and `I(t)=Lambda(log(t))`; explicit substitution wrappers should record those claims. These findings were sent to the probability author. They are elementary missing presentation bridges, not faults in the reviewed native KL or CGF-identification proofs. The subsequent resolution is recorded immediately below.


The probability author resolved both P2 interface findings in the compiled work-only `SigmaFinalProbKLBoundaries.lean`. I inspected the exact new proofs and confirmed the source bytes match the compiled stage. `poisson_potential_derivative` proves `HasDerivAt Psi (log t) t` for `t>0` by differentiating the actual function. `poisson_relative_entropy_actual_bregman` now contains the literal `deriv Psi b` in the displayed native-entropy identity and rewrites it using that derivative theorem. `centered_poisson_potential_in_log_coordinate` proves `Lambda(u)=I(exp(u))` for every real `u`, and `centered_poisson_reconstructs_potential` proves `I(t)=Lambda(log(t))` for every `t>0`. Both previously identified presentation gaps are therefore closed. Together with the reviewed prior Poisson recurrence/CGF inverse and the new KL, conjugate, tilting, and boundary modules, the inspected development declarations cover the displayed P2 and P2-boundaries statements. The final clean snapshot and axiom record remain separate build requirements.

I also inspected the appended `entropy_counterdensity_strict_entropy` and confirmed its source matches the compiled stage. It applies the concrete calibrated Gamma maximum-entropy bound and equality characterization to the already proved calibrated counterdensity, then excludes equality using the previously proved failure of almost-everywhere equality with Gamma. Thus its conclusion is the actual strict `EReal` entropy inequality below `1+EulerGamma`. It makes no unproved assertion of ordinary finite entropy for every candidate. This closes the explicit strict-entropy consequence for the reviewed P7 counterexample.
