# Complete C8 derivative and local-data boundaries

Parent milestone: `81f9e27a991c7dc304467451667592b11568a025`, pushed to main.

The final two residuals of C8 are now proved:

- On a nonempty convex open domain, equality of nth derivatives is equivalent
  to the difference being a finite polynomial sum with powers below n. The
  proof assumes existence of each successive derivative, not a stronger
  continuous-differentiability hypothesis. Both directions and n=0 are covered.
- `SigmaSmoothGerm` constructs a different positive, normalized smooth density
  agreeing with the intrinsic density on an arbitrary bounded observed region
  and on a final tail. Two disjoint weighted smooth bumps have exactly
  cancelling integrals; a derived positive scale preserves positivity. The
  exported theorem proves equality of the observed germ and every derivative,
  equality near the mode and zero endpoint and at infinity, and disagreement
  at an explicit positive point. It does not pretend the perturbation is analytic.

Existing C8 components were reused. The independent core auditor rechecked the
whole statement and returned AUDIT PASS, promoted C8 to complete, and emptied
its residual list. The new module is imported by Sigma and registered in Lake.

Validation: aggregate SigmaFormalization build PASS, project warnings zero;
source proof-escape audit PASS; six new material axiom checks PASS, depending
only on propext, Classical.choice and Quot.sound; coverage declaration checks
PASS. Upstream Mathlib warnings are unchanged. Full-paper completion is not
claimed: totals are 2 definitions, 32 complete, 33 partial, 13 missing.
