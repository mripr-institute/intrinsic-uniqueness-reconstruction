# Formal/analytic recovery and probability clauses

This milestone follows `39eebbbd8dab7ae599c6d59be512d618018201f9`.

## Exact coverage and independent review

- **F3: whole-statement AUDIT PASS**, including both formal exp/log inverses
  over rational algebras, the convergent entropy germ, exact coefficient-level
  identification with the real characteristic functions, full-real reconstruction,
  reciprocal domains, independent analytic global uniqueness, the existing smooth
  nonidentification witness, genuine complex poles, and actual Taylor radii
  `2*pi`, `2*pi`, `pi` with real points outside the Taylor discs.
- **F4 finite-base boundary: bounded AUDIT PASS.** Actual finite evaluation at a
  nilpotent class is independent of every sufficiently large cutoff; a concrete
  unequal rational series has identical evaluations and constant coefficient.
  Actual topological Thom/Gysin obligations remain partial.
- **P4 Euler/zeta and cumulants: bounded AUDIT PASS.** The actual log-Gamma
  product, absolutely justified double-sum exchange, native zeta identification,
  actual deficit CGF series and all positive-order iterated-derivative cumulants
  are proved, including the displayed first through fourth values. Identification
  with native variance and target algebraic recurrence calibration remain open.
- **P5 local-AC hazard/logistic: bounded AUDIT PASS.** Almost-everywhere ODE
  data upgrades to a classical derivative, the endpoint anchor identifies the
  survival, and native CDF equality identifies the actual probability measure.
  Deriving the formal tail/ODE inputs from a native absolutely continuous law and
  its actual density-to-survival hazard remains open, as do the distributional
  Green kernel and Poisson-process arrival construction.

The coverage auditor was independent of the respective proving agents. The
finite-base witness was reviewed by a different agent from its author. No
partial probability/topology statements have been promoted by this milestone.

## Verification

- `lake build SigmaFormalization`: PASS.
- Project-owned Lean warnings in this build: 0.
- Dependency-only Mathlib doc-string warnings: unchanged.
- `python3 scripts/rebuild_coverage.py --check --lean`: PASS, 1127 mappings.
- `Verify.source_audit()`: PASS; no `sorry`, `admit`, `sorryAx`, or project axioms.
- Full `Verify.py` / `SigmaAxioms.lean`: pending final audit completion.
- Independent mathematical review: PASS for the scopes above.
- Diff whitespace checks: PASS.

Coverage: 80 named paper items, 2 definitions, **41 complete, 27 partial,
10 missing**. The additional labelled claims remain 13 complete and 2 missing.
The proved inventory records 176 component entries within complete statements
and 79 within partial statements, with all exact remaining obligations retained.

## Preserved unfinished work

`lean/SigmaProbCumulantCalibration.lean` remains an untracked local experiment.
Its targeted compilation fails; it is excluded from this milestone's imports,
commit, and coverage claims. No code or WIP was deleted. Both metadata-repair
stashes and `backup-before-author-fix` remain intact.
