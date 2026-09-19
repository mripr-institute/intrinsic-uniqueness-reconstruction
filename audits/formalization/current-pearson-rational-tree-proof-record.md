# Pearson identification and rational-tree decoding

Terminology: this record concerns Lean formalization of proofs supplied in the paper. Coverage gaps refer to Lean, not to unproved mathematical results.

## Verified milestone

B1 and O2 have been independently compared with their complete current paper
statements and actual Lean signatures. Both received **AUDIT PASS** from the
independent coverage auditor. Their section maps now classify them as complete,
with no remaining Lean formalization components.

- B1: 59 mapped declarations, including the nonnegative determinant-one matrix
  monoid, Stern–Brocot/Calkin–Wilf reversal, unique canonical continued fractions,
  oriented runs, subtractive Euclidean decoding, root and terminal cases.
- O2: 26 mapped declarations, including local absolutely continuous Pearson flux,
  actual weight-measure identification, almost-everywhere and representative-level
  two-probe inverse statements.
- O2-boundaries: marked-probe irredundancy is proved; self-adjoint and time-scale
  boundary obligations remain explicitly partial.

## Checks

- `lake build SigmaFormalization`: PASS; no project-owned warnings.
- `python3 scripts/rebuild_coverage.py --check --lean`: PASS, 1013 declaration checks.
- `Verify.source_audit()`: PASS.
- Kernel axiom checks for all 28 newly added public audit entries: PASS; only
  `propext`, `Classical.choice`, and `Quot.sound` occurred.
- Independent whole-statement audit: PASS for B1 and O2.
- `git diff --check`: PASS.

Coverage after this milestone: 80 named items; 2 definitions, 40 complete,
28 partial, 10 missing. Ongoing F3 work is excluded from this milestone and its
coverage assessments.
