# Stieltjes proposition proof record

Completed target: Proposition 3.15, `final:P5-stieltjes`.

Authoritative source: `lean/SigmaProbStieltjes.lean`.

The existing explicit transform formula, derivative tower, and density/survival
counterexamples are retained. The added proofs establish:

- Integrability and differentiation of every positive reciprocal moment for
  arbitrary finite measures supported on the nonnegative ray.
- Recovery of those moments from equality of Stieltjes transforms on any
  nonempty open subset of the positive ray.
- Exact measure recovery using the existing Hausdorff moment-uniqueness theorem,
  the coordinate `x / (t + x)`, and the positive weight `1 / (t + x)`.
  Both the coordinate and weight are inverted explicitly. No density or
  probability normalization is imposed on the candidate finite measure.
- The full-transform and open-interval inverse, and its Gamma-target instance.
- Failure of a Stieltjes representation for the Gamma Laplace transform.
  Every such representation makes `x * f(x)` nondecreasing for `x >= 1`;
  the Gamma transform contradicts this at 1 and 2. The representation allows
  an infinite positive measure with integrable reciprocal weight.
- Smoothness of the Gamma Laplace transform on the positive ray.

## Local validation

The public source tree has no compiled cache for the renamed modules. Following
the instruction not to rebuild dependencies or the umbrella, new proof sections
were checked in temporary standalone Lean files against the existing pinned
mathlib cache. These contain the exact new declarations and the necessary
existing compact-moment theorem and Gamma definitions; they introduce no
assumed uniqueness theorem or other placeholder. The local checks exited zero.

The inverse, Gamma-target inverse, smoothness theorem, and non-Stieltjes theorem
have only the standard kernel axiom dependencies `propext`, `Classical.choice`,
and `Quot.sound`. No admitted proof or custom axiom is introduced.

This is local proof validation, not a fresh verification of the renamed
repository's complete import graph. The complete umbrella and axiom audit were
not run. The new audit entries in `SigmaAxioms.lean` are ready for the next
authorized aggregate verification.

Subsequently completed in this batch: Proposition 3.16 and Corollary 3.17; see
`probability-transforms-proof-record.md`. Other whole-paper obligations remain in
the component maps; their older entries are not a newly verified current total.
