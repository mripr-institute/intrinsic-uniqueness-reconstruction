# Global A/B reconstruction closure proof record

Date: 2026-09-30

Scope: `final:global-A` and its alias `final:global-B`, including the complete
presentation table in `paper/sections/closure.tex`.

## Declarations

`lean/SigmaClosureCompletePresentations.lean` extends the actual candidate and
observation records in `lean/SigmaClosurePresentations.lean`. Its public assembly is:

- `Sigma.Closure.CompletePresentation`
- `Sigma.Closure.completePresentation`
- `Sigma.Closure.complete_presentation_unique`
- `Sigma.Closure.calibrated_intrinsic_analytic`
- `Sigma.Closure.global_reconstruction_closure`
- `Sigma.Closure.complete_intrinsic_roundtrips`
- `Sigma.Closure.complete_reconstruction_roundtrip`

Every constructor resolves to an instantiated `IdentifiedNode`. Its local
existence and identifying inverse are proved before the generic assembly is
applied. The candidate record contains its native regularity and domain;
observed values are separate fields. No identifying conclusion is inserted as
an admissibility assumption. Equality to complete supplied data is the
observation for the full-law, full-function and full-series presentations.

## Table coverage

Names below lie in `Sigma.Closure`; existing nodes enter through the
`CompletePresentation.available` constructor.

| Paper presentation family | Instantiated nodes |
| --- | --- |
| Intrinsic entries | `intrinsicHNode`, `intrinsicINode`, `intrinsicDensityNode` |
| Differential core | `calibratedCurvatureNode`, `calibratedRiccatiNode`, `exactFlowNode`, `recenteringNode`, `differentialCoreNode` |
| Group core | `groupLogNode`, `groupCocycleNode`, `typedCompletionNode` with either value or slope anchor |
| Convex/projective core | `scaleBregmanNode`, `symmetricBregmanNode`, `exactLegendreNode`, `selfConcordanceNode` with signed or unsigned equality, `hessianMetricNode`, `projectiveCrossRatioNode`, `projectiveSchwarzianNode`, `projectivePrimitiveNode` |
| Gamma transforms | `gammaLawNode`, `gammaLaplaceNode`, `gammaMomentsNode`, `gammaMellinNode`, `gammaCharacteristicNode`, `entropyMaximizerNode` |
| Poisson | `poissonRecurrenceNode`, `centeredPoissonLocalCGFNode`, `orientedPoissonKLNode`; the other P2 slices are distinct `orientedExponentialKLNode` and `orientedGaussianKLNode` entries |
| Gumbel/Haar | `gumbelMaxNode`, `markedHaarDensityNode` |
| Linked deficit | `linkedDeficitNode` |
| Other exact probability nodes | `nativeSurvivalNode`, `nativeLogisticNode`, `secondOrderDensityNode`, `causalGreenNode`, `gammaStieltjesNode`, `positiveSizeBiasNode`, `positiveEquilibriumNode` |
| Formal/analytic series | `fieldToddTowerNode`, `fieldFormalSeriesNode`, `fieldAhatNode`, `fieldLNode`, `fieldChiNode`, the four `connected*Node` series presentations and their four `connectedInverse*Node` versions |
| Tree inverse | `rootedSeriesNode`, `borelSeriesNode`, `borelPGFNode`, `rootedInverseNode`, `borelInverseNode`, `positiveTreeInverseNode` with either rooted or Borel normalization |
| Marked rational presentation | `markedRationalNode`, `analyticMarkedRationalNode` |
| Measure/operator observations | `gammaSteinNode`, `linkedOperatorMixingNode`, `gammaLaguerreNode`, `bernsteinIntegerTailNode` and `bernsteinRepresentationNode` for every supplied tail threshold |

## Retained classes and marks

- The intrinsic object is proved real analytic on the marked positive ray.
  Both intrinsic round trips and every pairwise reconstruction follow for the
  whole enumeration.
- Typed completion retains differentiability, the derivative range in
  `(-1, infinity)`, the typed equation, and each permitted anchor separately.
- The Legendre candidate retains the paper's disjunction: lower
  semicontinuity on the positive ray **or** extended convexity.
- Self-concordance retains the whole positive ray, all three calibrations,
  positive curvature and `C3` regularity. Signed and unsigned observations
  remain distinct. The Hessian node records the coefficient in the marked
  coordinate and both affine anchors. Projective primitives retain the
  derivative link to the observed projective function.
- The entropy candidate is the actual measure of a calibrated density.
  Almost-everywhere equality identifies that measure, rather than asserting
  pointwise equality of arbitrary density representatives. Mass, first moment
  and logarithmic moment are retained.
- Poisson KL uses actual relative entropy with `Poisson(1)` as the first
  argument and the marked rate as the second.
- Native survival uses the actual Radon--Nikodym hazard. The logistic node
  links the same probability to its marked hazard representative. The ODE
  node retains `C2`, the continuous endpoint extension, zero endpoint and
  unit integral. All four identifying clauses of `final:P5` are instantiated.
- The causal Green candidate admits **all causal linear functionals** on
  compact smooth tests. The proved inverse therefore also applies to the
  paper's distributions, without imposing the stronger global `L1` bound
  found in `P5RegularDistribution`.
- Formal nodes are parameterized by an arbitrary field of characteristic
  zero, rather than only rational coefficients. The chi parameter and
  `y != -1` mark are retained; complete multiplicative inverse series have
  their own constructors.
- Complete Todd, A-hat, L and chi observations include literal equality of
  entire power series. The additional A-hat/L/chi-to-Todd observations also
  compare complete series, not a finite set of coefficients. The Todd tower
  observes every positive degree and retains its constant coefficient.
- Analytic candidates are functions on the supplied connected domain,
  with an analytic representative and its actual formal germ. Equality is
  concluded on that domain only. Inverse chi retains the nonvanishing
  domain condition. The tree inverse is observed through actual local
  composition with the rooted EGF or Borel PGF.
- The separate positive-ray tree inverse node requires analyticity only on
  `(0, infinity)`, exactly as in P6's global density converse. Its observed
  germ is one-sided; no analytic continuation through zero is assumed.
  The Borel version divides its inverse germ by the marked factor `exp(1)`.
- Numerical rational labels are bundled with the declared full-domain
  Möbius or analytic extension. Neither a bare unlabelled tree nor an
  unrestricted continuation is listed as a complete presentation.
  `marked_rational_scalar_recovery` and
  `analytic_marked_rational_scalar_recovery` additionally prove the actual
  integral formula for every positive `t`, including `t < 1`.
- The Bernstein constructor retains an arbitrary threshold `N`, observing
  every integer at or above it in the native representation class.
  A separate representation constructor recovers the actual killing, drift
  and Levy measure, as well as their exponent.

## Skeptical whole-statement review

The completed implementation was compared again with every table row and the
referenced identifying clauses before coverage integration. This review found
and corrected two interfaces:

1. The initial tree inverse continuation nodes retained a domain containing
   zero. P6 also permits a global density analytic only on the open positive
   ray; `positiveTreeInverseNode` now instantiates that exact class.
2. The initial full Laplace node observed the larger domain `s > -1`. P1's
   identifying input requires only `s >= 0`; `gammaLaplaceData` now uses that
   domain and retains a probability supported on the nonnegative ray.

The review also made the other two oriented P2 divergence slices, complete
direct characteristic-series observations, and actual Bernstein representation
data explicit. Causal functionals were checked to admit every causal
distribution, and complete observations were checked independently from
candidate admissibility. No identifying conclusion was found among the native
candidate assumptions. With these corrections, every Global A/B presentation
family and both directions of reconstruction are covered.

## Validation

The new module was compiled with the repository's Lean 4.14.0 toolchain and
pinned mathlib. The existing `SigmaClosurePresentations` import and its missing
coordinate-recovery dependencies were rebuilt first. No admitted proof or
custom axiom was introduced.

The six principal assembly and rational-recovery theorems were checked with
`#print axioms`; their dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`.

Aggregate imports, the lake root, the axiom ledger and coverage status are
integrated by the coordinating agent. This record does not assert completion
of F5, Global C/D/F, or R1.
