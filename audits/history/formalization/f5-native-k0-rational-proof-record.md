# F5 native K⁰ and rational characteristic proof record

> **Historical record.** Statuses, counts, commands and local paths below describe
> the recorded stage, not the current checkout. See [current coverage](../../lean-coverage.md)
> and the [archive guide](../README.md).

Date: 2026-09-30

Scope: the whole statement of `final:F5` on the fixed native real projective
plane. The rational conclusion uses a stronger additive torsion argument,
so a comparison between the chart Čech complex and singular cohomology is
not needed for this proof.

## Native integral side

`SigmaNativeComplexKTheory.lean` constructs the Whitney-sum monoid of
isomorphism classes of actual finite-dimensional complex vector bundles.
Isomorphisms retain fiberwise complex linearity and continuity in both
directions over the identity of the base. Its Grothendieck group is the
additive localization at the whole monoid. The theorem
`FiniteComplexBundle.kClass_eq_iff` proves that equality of bundle classes
supplies an actual common finite-dimensional bundle stabilizer.

`SigmaNativeComplexBundleModel.lean` transports model coordinates while
preserving the actual bundle topology. Consequently the arbitrary model of
that stabilizer can be put in the finite-coordinate form required by the
previous determinant obstruction. This proves the literal native inequality
`real_projective_complex_k0_class_ne_one` in `SigmaRealProjectiveKTheory.lean`.
The imported complexification, no-section, determinant and tensor-square
modules already establish that this is the actual complexification of the
real tautological line, that it is nontrivial, and that its tensor square is
trivial.

## A concrete additive order-two relation

`SigmaRealProjectiveDoubleTriviality.lean` proves an actual isomorphism
`L ⊕ L ≅ 1 ⊕ 1`. In the incidence model its forward map sends vectors
`u, v` in the complexified real line to

```
(u₀ + i u₁ + v₂, -u₂ + v₀ - i v₁).
```

If `P` is the continuous rank-one orthogonal projector onto that line,
the inverse sends `(x, y)` to the pair of incidence vectors with coordinates

```
uₖ = Pₖ₀ x - i Pₖ₁ x - Pₖ₂ y,
vₖ = Pₖ₂ x + Pₖ₀ y + i Pₖ₁ y.
```

Both inverse equations are proved using the actual projective representative
and its positive squared norm. Forward continuity follows from the incidence
homeomorphism; inverse continuity follows from the projector entries. Thus
the K⁰ equation is not inferred from a dimension or classification claim.
The nonzero reduced class has additive order two.

## Rational characteristics and the ordinary Chern character

`SigmaRealProjectiveRationalCharacteristic.lean` proves that **every additive
map from this native K⁰ group into any rational module** has the same value
on `L` and the trivial line. Applying the map to the native doubling relation
and multiplying by one half proves the equality.

For any supplied rational cohomology ring, the usual Chern character is such
an additive map. Its defining trivial-line normalization gives `ch(L) = 1`
through `real_projective_normalized_rational_characteristic_one`. Neither
the value of `ch(L)`, a vanishing cohomology group, nor an RP²-specific
characteristic identity is an input. This theorem is universal in the target
and therefore also covers a product of rational additive observations.

As in the supplied-theory interpretation of F4, this does not claim to
construct the ordinary cohomology functor or the general Chern character
from scratch. Only their elementary defining additivity and unit
normalization are used. The proved torsion equation holds before any such
theory is supplied.

`real_projective_scalar_rational_data_no_k0_decoder` retains an arbitrary
entire scalar object and every other common packet while proving that the
rational observation cannot decode the actual K⁰ class. In particular the
scalar object can be the complete characteristic power series.

The scalar-boundary integral-characteristic clause also exposes the usual
supplied classification of complex lines by their integral first Chern
class. Its hypothesis is the general identifying law for every pair of
native rank-one bundles. Native nontriviality then proves the two integral
classes differ; no RP²-specific class value is supplied.

## Independent chart calculation

The three-chart Čech modules additionally compute continuous logarithms of
the genuine transition functions, their integral Chern cocycle, an explicit
rational primitive, and surjectivity of the rational degree-two differential
using the four connected sign components of the triple overlap. These are
actual chart-cohomology results. They are not relabelled as singular
cohomology. Their comparison with another cohomology construction is not
used by the completed additive torsion proof above.

## Principal declarations

- `Sigma.realProjectiveDoubleTrivialization`
- `Sigma.real_projective_complex_k0_class_ne_one`
- `Sigma.real_projective_k0_double_eq`
- `Sigma.real_projective_reduced_k0_two_torsion`
- `Sigma.real_projective_rational_additive_characteristic_eq`
- `Sigma.real_projective_normalized_rational_characteristic_one`
- `Sigma.real_projective_fixed_base_integral_rational_witness`
- `Sigma.real_projective_scalar_rational_data_no_k0_decoder`

## Validation

All new modules and the `Sigma` umbrella compile with the pinned toolchain.
Targeted axiom checks report only `propext`, `Classical.choice`, and
`Quot.sound`. The repository source audit finds no admissions or project
axioms. The subsequent full `python3 Verify.py` run on commit `8869f70`
also passed the full library build and all 2537 distinct declarations in
`SigmaAxioms.lean`, with no missing reports or unexpected axioms. See
[the full-project axiom audit](full-project-axiom-audit-2026-09-30.json).
