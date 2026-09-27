# O5 mixing support and Gamma-three components: bounded independent audit

**AUDIT PASS for the stated partial components only.**

Scope: `SigmaOpGammaShapeThree.lean` against the corresponding Gamma-three
clauses in `final:O5-isospectral-boundary`, and
`SigmaOpMixingStrong.lean` against the corresponding strong-mixing and
integer-eigenvector clauses in `final:O5`, in
`paper/sections/operators.tex`. Neither complete theorem is claimed.

## Gamma-three standalone components

- `gammaShapeThreeProbability` is the actual native measure `gammaMeasure 3 1`,
  proved to be a probability. Its real density is exactly
  `1_(0,∞) t² exp(-t)/2`, up to the immaterial zero endpoint. The integral
  identity, every polynomial moment, and the mean three concern this actual
  measure; integrability is proved. The unequal mean gives an actual
  inequality with the existing Gamma-two coordinate law.
- The polynomials defined as `-(L_(n+1)^(1))'` have the standard degree-n
  Gamma-three Laguerre normalization. Their native ordinary first and second
  derivatives satisfy `-t f''-(3-t)f' = n f`. Degree bounds, nonzero leading
  coefficient and the zero polynomial mode `L_0^(2)=1` are proved.
- Orthogonality is an actual integral against Gamma-three probability, with
  exactly the paper's squared norm `(n+1)(n+2)/2`. The auxiliary factorial
  moment functional is bridged to these actual measure integrals; it is not
  the final claimed content.
- `GammaShapeThreeWeightedHilbert` is the actual complex `Lp` space for that
  measure. The polynomial vectors have proved `Memℒp` membership, their
  actual L2 inner products have the displayed norms, and normalization gives
  an `Orthonormal` family, including index zero.

These support partial coverage of `final:O5-isospectral-boundary`. They do
not prove completeness, eigenvectors of a closed Gamma-three operator,
the literal compact-test graph closure, endpoint limit-point statements,
native self-adjointness, a constant-preserving intertwining unitary,
agreement of spectral invariants, mixing, or stationarity of the coordinate
law. Those residuals must remain explicit in the coverage map. In
particular, the formalized law is a coordinate probability, not yet a
proved invariant law of the unconstructed Gamma-three closure.

## Conditional strong-mixing support

- `OpContractionEvolution B S` asks for zero-time identity, contraction,
  continuous vector orbits, and the generator derivative on the full domain,
  including the right derivative at zero. It does not assume a mixing
  identity or the eigenvector evolution formula. `OpIsResolvent B 1 R` is the
  actual native two-sided shift-inverse interface with image-domain
  membership, not only scalar resolvent values.
- From these explicit supplied objects,
  `op_evolution_strong_gamma_mixing` proves the actual vector-valued Bochner
  identity `∫_(0,∞) s exp(-s) S(s)x ds = R(Rx)` for every vector. Norm
  domination proves integrability, and the primitive's zero-time and
  infinite-time endpoints are established. This is stronger than a scalar
  transform identity but remains conditional on the evolution and native
  resolvent inputs.
- Integer-eigenvector evolution and resolvent actions are derived from
  those native differential and two-sided inverse equations. They are not
  inserted as hypotheses of the evolution interface.
- Strong integration against a genuine native `ComplexMeasure` is defined
  by the real and imaginary Jordan-part Bochner integrals. Finite-measure
  orbit integrability follows from contraction. The existing native signed
  and complex measure infrastructure covers finite total variation, without
  positivity or a density hypothesis on the unknown measure.
- `op_evolution_complex_mixing_integer_sample` obtains every integer scalar
  sample, including `n=0`, from the actual vector equation on a nonzero
  eigenvector. `op_evolution_complex_mixing_unique` needs just one nonzero
  eigenvector at each integer, with neither completeness nor multiplicity
  conditions, and concludes equality of the original native complex measure
  with the Gamma-two mixing measure on the full closed nonnegative ray.

No scalar surrogate, lost endpoint, strengthened eigenvector requirement,
or hidden target mixing identity was found in these conditional results.
The unknown-measure equation itself is appropriately an input to the
uniqueness theorem, matching the paper's inverse question.

The construction of the evolution `S` and resolvent `R` from an arbitrary
nonnegative self-adjoint `B` remains unproved here. Consequently no
unconditional residual of `final:O5` is closed by this support module, and
the whole row must remain partial. The module's opening comment and the
proposed conditional coverage description correctly state that limitation.

## Verification evidence

The proving agent supplied PASS results for targeted compilation of both
new modules. This audit independently inspected their signatures,
definitions, proofs and the immediately relevant native measure/operator
infrastructure. Integration build, source audit and selected transitive
axiom checks are the parent agent's responsibility and are not represented
here as independently rerun checks. No other paper rows or unrelated WIP
were audited.
