# Local baseline and coverage reconstruction

Terminology: this record concerns Lean formalization of proofs supplied in the paper. Coverage gaps refer to Lean, not to unproved mathematical results.

This document preserves the starting baseline, not the latest totals. For the
current audited status, use [the live coverage ledger](../lean-coverage.md) and
[its machine-readable source](../lean-coverage.json). Milestone proof records
likewise retain the counts at their own verification milestone.

Starting commit: `5260a8cb433815e9ef20015a2396865b3c6b2582` on `main`.
Configured remote: `https://github.com/mripr-institute/intrinsic-uniqueness-reconstruction.git`.
The initial status reported `main` up to date with `origin/main`.

Pre-existing local state, preserved:

- `lean/lakefile.lean`: five additional existing modules registered as roots:
  SigmaClosure, SigmaClosurePerturbation, SigmaProbEquilibrium,
  SigmaProbGammaTilts, SigmaProbWeightsReal.
- `lean/lean-toolchain`: no trailing newline; content still Lean 4.14.0.
- `lean/lake-manifest.json`: untracked dependency manifest matching the pinned
  Mathlib commit `4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84`.
- No staged changes; no other initial changes.

The initial `lake build SigmaFormalization`, `python3 Verify.py`, and explicit
`lake env lean SigmaAxioms.lean` all passed (exit 0). The initial verifier source
audit found no `sorry`, `admit`, or `sorryAx`.
The initial build emitted 62 project-owned warnings across 27 source files,
plus upstream Mathlib doc-string warnings. No dependency files were changed.

## Fresh initial Lean coverage, before further formalization

80 named mathematical environments in the current five paper sections:
2 definitions, 28 complete, 37 partial, 13 missing. Labels global-A/global-B
and global-C/global-D are paired labels of single theorem environments.
The Formalization remark is software-status prose and is audited separately;
it currently overstates completion. Standalone labelled equations are retained
in the detailed section audits, including the then-unformalized arbitrary-power Todd
coefficient formula. They are not silently counted as complete named theorems.

The old top-level ledger had 78 pending exact matches. Those were unclassified,
not 78 missing mathematical proofs. The new ledger credits existing Lean proofs and lists only
their exact remaining clauses. Both the complete-coverage claim and the
assumption that the entire remainder is small are contradicted by source
inspection: the unbounded operator and topological developments are substantive
remaining Lean formalization work.

Examples recovered from stale mappings: the full real-parameter Z4 density
family; P2 actual entropy/divergence and Poisson clauses; P2 orientation
witnesses; P4-data's smooth involution, density and asymptotic; rooted/Borel
formal, analytic and probability components; matrix block additivity, genuine
matrix calculus and metric isometries; Farey branch ranges; actual Stieltjes,
equilibrium and marked-tilt inverses. Core curvature, completion, Fenchel,
self-concordance, projective and weak Stein results already have exact proofs.

Independent section audits and a second adversarial review identified two
additional gaps in otherwise substantial results: P6 needs the arbitrary
independent-variable interface to its canonical sum law; P7 needs entropy
integrability derived from finite extended entropy. These were recorded before
implementing a fix. Complete compilation alone was not used as coverage evidence.

The residual inventory is maintained in the `unproved_components` entries in
the four `current-*-audit.json` artifacts, rendered in `audits/lean-coverage.md`;
these are live records and no longer reproduce the initial inventory unchanged.
Subsequent verified changes are recorded in milestone proof records. No paper
statement has been weakened and no proof obligation has been removed.
