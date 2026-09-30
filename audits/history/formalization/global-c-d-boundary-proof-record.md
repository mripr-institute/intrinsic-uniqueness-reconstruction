# Global C/D and scalar boundary proof record

> **Historical record.** Statuses, counts, commands and local paths below describe
> the recorded stage, not the current checkout. See [current coverage](../../lean-coverage.md)
> and the [archive guide](../README.md).

Date: 2026-09-30

Scope: `final:global-C`, its alias `final:global-D`, and the resulting
`final:global-F` scalar boundary assembly. R1 is not used or changed.

## Sufficient decomposition

`SigmaClosureCompleteBoundary.lean` constructs `sufficientDecomposition`
for every member of the completed Global A/B enumeration. It is an actual
equivalence from one complete certificate, optional placement and selected
packets to the intrinsic object, optional marked placed function and those
same packets. Both round trips are proved. `ExternalSelection` explicitly
bundles a carrier with its selected object; an arbitrary packet type can
also contain dependent base/bundle or sample-space/process records.

The intrinsic H/I/p inverses and exact two-coordinate placement equivalence
are reused. The six native canonical-context existence and uniqueness
clauses are already proved by `fixed_context_native_closure` in
`SigmaClosureThom.lean`, including their independently supplied geometric
foundations. Its existing Global E completion remains valid.

## Normalized intrinsic deletion

`SigmaClosureNormalizedPerturbation.lean` completes the paper's perturbation
`J = I + εg + δh`, with `g(t) = (t-1)^4 exp(-t)` and
`h(t) = (t-1)^4 exp(-2t)`.

Bounded perturbations dominate the actual Gamma probability integral and
prove continuity of its mass in both parameters. For positive ε the mass
at δ = 0 is strictly below one. For negative δ the mass at ε = 0 is
strictly above one. For any prescribed small neighborhood, continuity
preserves the second inequality at a sufficiently small positive ε. The
intermediate-value theorem then selects a small δ with exactly unit mass.
This gives the required existence without needing an implicit-function
parameterization.

The existing uniform positive-curvature neighborhood proves strict
convexity. All three anchors, real analyticity and both endpoint
divergences are retained. Linear independence and ε > 0 prove a genuine
change on the positive ray. The exact Gamma integral is then rewritten as
the paper's Lebesgue integral of `exp(-1-J)` over `(0,∞)`.

`intrinsic_packet_no_decoder` applies this witness in the declared relaxed
class, with an arbitrary common retained context and no alternative
complete intrinsic certificate.

## External deletion assembly

`CompleteScalarBoundary` extends the earlier native packet assembly and
retains an arbitrary common context for every decoder obstruction:

| Deleted information | Native witness |
| --- | --- |
| Intrinsic certificate | Distinct normalized analytic strictly convex perturbation |
| Placement scale or offset | The exact two pairs of admissible placed functions |
| Coordinate marking | Identity and doubled positive coordinate |
| Stationary coordinate law | Gamma shapes two and three, with the same integer spectrum and both actual common mixing identities |
| Vector angle | Uniform sphere angle and fixed direction with the same Gamma radius |
| Process increments | Native Gamma subordinator and time-scaled Gamma variable, with the same time-one law |
| Tree law | Path and star laws with the same Borel order law |
| Matrix extension | Spectral perturbation retaining the rank-one seed |
| Integral bundle/K⁰ data | The actual RP² line and trivial line, distinct in native K⁰ and equal under every rational additive characteristic |
| Numerical arithmetic labels | Prime-generator permutation on the same multiplication carrier |
| Spatial dimension | The native distinct-dimensional spatial packets |
| Orthogonal composition | Squared norm and fourth power of norm on the same plane |
| Remaining radius scale | Squared norm and twice squared norm within the additive class |

The native bundle nonisomorphism is retained separately. The assembly also
retains dimension-at-least-two orthogonal-additivity rigidity, exact radial
cancellation in dimensions one or three, selection of three when dimension
is at least two, and the different-profile cancellation witness. Thus the
positive reconstruction boundaries and their hypotheses accompany the
nonidentification statements.

The rational F5 clause is the universal native K⁰ theorem documented in
`f5-native-k0-rational-proof-record.md`. It requires no unproved RP²
cohomology vanishing input. General cohomology/Chern-character foundations
have the same supplied-theory status as in the paper; no reconstruction of
those foundational functors from scratch is asserted.
The integral first-Chern-class clause explicitly retains the usual general
classification of rank-one complex bundles as a supplied foundation. It
derives unequal integral classes from the actual bundle obstruction, rather
than assuming a nonzero RP² class.

## Principal declarations and validation

- `Sigma.Closure.normalized_intrinsic_deletion_witness`
- `Sigma.Closure.sufficient_decomposition_roundtrips`
- `Sigma.Closure.intrinsic_packet_no_decoder`
- `Sigma.Closure.complete_scalar_boundary`
- `Sigma.Closure.global_relative_irredundancy`

The new modules and full `Sigma` umbrella compile with the pinned toolchain.
The source audit finds no admissions or project axioms. Targeted axiom checks
report only `propext`, `Classical.choice`, and `Quot.sound`.
