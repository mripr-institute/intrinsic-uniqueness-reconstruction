# Probability transformations: proof record

Completed paper targets: Proposition 3.16 (`final:P5-transforms`) and
Corollary 3.17 (`final:P5-equilibrium-fixed`).

## Authoritative sources

- `lean/SigmaProbEquilibrium.lean`: actual equilibrium measures; normalization
  by tail integration; exact positive-lifetime inverse and Gamma identification;
  the atom-at-zero counterexample with actual rescaled means; the full exponential
  fixed-point equivalence without a candidate-density assumption.
- `lean/SigmaProbGammaTilts.lean`: exact weighting and normalization of native
  Gamma measures; the complete admissible range including endpoint divergence;
  rate change; actual log-MGF derivative cumulants; actual moments, mean and
  variance; the counterexample when the input tilt mark is omitted.
- `lean/SigmaProbWeightsReal.lean`: translation of nonnegative normalizers into
  the displayed real integrals; size-bias reciprocal mean, inverse existence and
  uniqueness through the existing inverse; the real-integral marked-tilt inverse.

The existing size-bias, normalized-weight, exponential, and Gamma lemmas are
reused. Their definitions and statements are unchanged. The new modules are
imported by `SigmaProbability`, and their principal declarations are registered
in `SigmaAxioms`.

## Essential proof steps

Equality of equilibrium laws gives equality of their interval primitives.
Right-hand differentiation recovers the canonical survival ratios everywhere,
including at zero. Positive lifetimes fix the mean there, and the entire
survival then identifies the measure.

Fixed-point equality first supplies the survival integral equation. This proves
continuity rather than assuming it. The integrating factor proves exponential
survival, and the existing native Gamma shape-one theorem supplies the converse.

Gamma tilting is proved as equality of actual weighted measures. The normalizer
is their total mass. Beyond the admissible endpoint, a positive lower bound on
an infinite ray forces the normalizer to be infinite. Cumulants are derivatives
of the actual log-MGF; mean and variance are also computed as actual integrals.

## Validation

The new declarations were checked with Lean 4.14.0 against the existing pinned
mathlib cache. Temporary local check files contained the exact new declarations
and the exact required existing helper definitions and proofs. All checks exited
zero. No assumed result, admitted proof, or custom axiom was used. The principal
inverse, counterexample, cumulant, admissibility, and fixed-point declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

This validates the new proofs locally. It is not a fresh aggregate verification
of the renamed module import graph: the user requested no dependency rebuild,
umbrella build, or complete axiom audit. Those were not run.

Next probability target: the remaining rooted-tree/forest enumeration and
branching-process components of Theorems 3.18 and 3.19. Their already proved
formal-series and scalar probability components must be reused.
