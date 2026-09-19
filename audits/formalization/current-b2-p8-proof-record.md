# Farey recovery, smooth boundaries, and the Gamma convolution family

Parent milestone: `1b4be3d`, pushed to main.

B2 is now complete. Arbitrary numerically labelled child maps are identified
on every positive rational. Three observations determine each real Möbius
extension, with nonzero denominators derived from the observations. Analytic
extension is proved on the full connected domain by density and the analytic
identity theorem. The existing integral and two closed inverse branches retain
their endpoints. An actual second injective positive labelling witnesses the
failure of identification from the abstract binary tree alone.

The F3/B2 smooth boundary uses an actual nonzero compactly supported bump.
The exported potential is smooth and strictly convex on the positive ray, has
the same germ and every jet at one, and has the same derivative on all inputs
at least one, but differs at three eighths. The allowed perturbation size is
derived from compactness, not assumed. F3 retains its separate formal and
analytic recovery obligations.

The M2 adjacent dual-Bregman identity now uses the actual Fréchet derivative of
the dual potential and the correctly reversed Legendre arguments. This does
not erase the other outstanding adjacent matrix claims.

P8 now has an actual probability-measure convolution family with Dirac zero,
the prescribed time-one marginal, Gamma marginals, and equality for native
measure convolution. Uniqueness covers arbitrary nonnegative probability
families without assuming continuity. Weak continuity in the native
ProbabilityMeasure topology is derived, including time zero. P8 remains
partial: a global process construction and finite-dimensional uniqueness are
not claimed by this milestone. P8-samples remains missing.

Independent bounded coverage reviews: B2 and dual-Bregman AUDIT PASS;
smooth F3/B2 boundary AUDIT PASS; P8 family and derived continuity AUDIT PASS.
Aggregate SigmaFormalization build PASS with no project-owned warnings.
Source proof-escape audit PASS; focused material axiom checks PASS with only
propext, Classical.choice and Quot.sound. The preceding full Verify.py run
also completed successfully. New material declarations are in SigmaAxioms.

Named-statement totals: 80 = 2 definitions + 34 complete + 32 partial +
12 missing. These are residual counts, not a full-completion claim.
The ongoing process file is excluded from the milestone and coverage credit.
