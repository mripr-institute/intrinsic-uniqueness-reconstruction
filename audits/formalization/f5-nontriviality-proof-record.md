# F5 nontriviality proof record

Paper target: `final:F5`, first clause: the complexification of the tautological
real line on the actual quotient-topological `RP²` is nontrivial.

Formalization: `Sigma.real_projective_complexification_has_no_nonvanishing_section`
proves that the actual incidence line admits no continuous nowhere-zero section.
`Sigma.real_projective_complex_bundle_not_trivial` then rules out a global
bundle trivialization: such a trivialization supplies a continuous fiberwise
linear equivalence to the product line, and its inverse image of the constant
unit vector is a nowhere-zero section. Both statements use the existing
`Sigma.realProjectiveComplexLine` chart bundle and its incidence total-space
homeomorphism; the section is not a scalar surrogate.

The no-section proof follows the paper's obstruction route. A hypothetical
section induces the actual normalized odd phase on the unit sphere. The
northern hemisphere is identified with a closed Euclidean disk. A continuous
unit-circle-valued map on that disk is lifted to a continuous real angle by
the radial null homotopy, compact uniform continuity, finite subdivision, and
local branches of `Complex.arg`. On the equator, antipodal oddness forces the
continuous angle difference to be an odd integral multiple of `π`; connectedness
makes it constant, while the antipodal involution negates it, a contradiction.
No global angle lift is assumed.

Verification for this component: targeted Lean compilation and the full
`SigmaFormalization` build pass; `Verify.py` reports no source proof escapes.
The public declarations are included in `SigmaAxioms.lean`; its transitive
axiom output contains only the accepted Lean foundations. An independent
adversarial review compared the no-section theorem with the paper's
hemisphere/angle obstruction and returned AUDIT PASS for this component.

This record does not claim the entire `final:F5` proposition complete. The
stable complex `K⁰` distinction (including determinant cancellation for an
arbitrary stabilizer), the rational Chern-character computation, and the
resulting fixed-base nonreconstruction witness remain to be formalized.
