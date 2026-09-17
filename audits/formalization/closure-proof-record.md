# Section 9 proof record

Priority: paper Theorems 9.2--9.4 and Corollary 9.5. These four results are
**not yet fully covered** by the Lean development. No unproved local result is
inserted as an assumption to make a global completion theorem.

## Exact components

`lean/SigmaClosure.lean`:

- 9.2: explicit reversible intrinsic loss/density coordinates on the positive
  ray, including the actual `H`, `I`, and `p` values; composition and uniqueness
  for already established typed equivalences. This is not an instantiation of
  every entry of the paper's identifying-presentation table.
- 9.3: the elementary uniqueness statement for the output of a fixed dependent
  recipe. This is bookkeeping only; it does not prove the six native realization
  theorems or identify arbitrary objects outside the recipe's graph.
- 9.4: the exact parameter domain `mu > 0`, `0 < a < 1`; a bijection with its
  actual placed-function image; the paper's two scale witnesses and two offset
  witnesses; failure of a decoder after either deletion, retaining all other
  context. The dependent spatial packet stores the selected function together
  with the dimension of its domain.
- 9.4--9.5: concrete Euclidean-plane squared-norm/quartic and squared-norm/twice-
  squared-norm witnesses; actual dimension-two/dimension-three packets; decoder
  impossibility with arbitrary fixed retained data, including the whole scalar
  component. The spatial rigidity conclusion reuses the existing theorem with
  its original arbitrary-dimensional candidate class and also proves uniqueness
  of the coefficient. Radial cancellation is stated for the actual differential
  expression, with both admissible dimensions and the dimension-at-least-two
  restriction. The existing constant-profile counterexample is retained.

`lean/SigmaClosurePerturbation.lean`:

- The paper's exact functions `(t-1)^4 exp(-t)` and `(t-1)^4 exp(-2t)`.
- Their analyticity, first and second derivatives, and linear independence on
  the positive ray.
- The actual perturbed intrinsic function, its analyticity, its value and first
  derivative at one, and its unit second derivative there.
- Equality with the intrinsic function occurs exactly at zero parameters.
- Exponential decay and a bound for each weighted second derivative on the
  whole positive ray; a uniform parameter neighborhood preserving strict
  convexity.

`lean/SigmaRealOrthogonal.lean` has an elaboration-only correction specifying
the finite index order for the existing Gram--Schmidt invocation. Its theorem
statement and mathematical argument are unchanged.

## Still required for the full numbered results

1. **9.2:** instantiate the complete table of identifying presentations using
   actual native local inverse theorems. Generic equivalence composition alone
   does not constitute this result.
2. **9.3:** assemble all six native fixed-context existence/uniqueness results
   and their stated reverse observations. A recipe's graph is not a replacement
   for these results.
3. **9.4, intrinsic deletion:** select nonzero perturbation parameters preserving
   the exact integral normalization; establish the stated endpoint behavior;
   combine these with the analyticity, anchors, strict convexity and distinctness
   results above. No normalization premise may replace this existence proof.
4. **9.4, other external packets:** finish and assemble the stationary law,
   vector law, increments, tree law, matrix extension, topology and arithmetic
   countermodels in their actual stated candidate universes. Reuse the native
   countermodels already available rather than replacing them by free labels.
5. **9.5:** assemble the complete scalar non-identification list from those
   concrete witnesses. Its spatial subclaims alone do not finish the corollary.

Next target: the exact mass-preserving parameter selection in 9.4.

## Local validation

Both new modules and the corrected orthogonal-rigidity proof were checked with
Lean 4.14.0 against the existing pinned mathlib cache. Temporary local check
files included the exact required existing helper definitions and proofs, not
assumed helper statements. Both checks exited zero; the checked principal
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
No admitted proof or custom axiom was introduced. There is an informational
`ring_nf` suggestion in the perturbation check, with no proof failure.

The modules are imported by `Sigma.lean` and registered in `SigmaAxioms.lean`.
As requested, no full build, umbrella rebuild, or complete axiom audit was run.
This local validation is not a fresh aggregate check of the renamed import graph.
