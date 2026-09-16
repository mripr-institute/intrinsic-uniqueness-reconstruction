# Intrinsic Uniqueness and Reconstruction Across Mathematical Presentations

Formal mathematical sources, Lean 4 verification, reconstruction audits, and publication files accompanying:

**Alex Albert, _Intrinsic Uniqueness and Reconstruction Across Mathematical Presentations_**

DOI: 10.5281/zenodo.22775358

## Repository structure

- `paper/` — publication source and compiled PDF.
- `lean/` — Lean 4 formalization.
- `audits/` — reconstruction, dependency, formalization, and axiom-audit records.
- `scripts/` — publication and reproducibility utilities.

## Lean formalization

The formal development is organized by mathematical content.

Principal entry points:

- `lean/SigmaBase.lean` — intrinsic algebraic and convex primitives.
- `lean/SigmaReconstruction.lean` — reconstruction from differential data.
- `lean/SigmaPresentations.lean` — exact mathematical presentations and reversible transformations.
- `lean/SigmaFormalSeries.lean` — formal power-series reconstruction.
- `lean/SigmaCore.lean` — intrinsic analytic core.
- `lean/SigmaProbability.lean` — probability presentations.
- `lean/SigmaRealizations.lean` — realization results.
- `lean/Sigma.lean` — complete umbrella module.
- `lean/SigmaAxioms.lean` — exported-declaration axiom audit.
- `lean/Verify.py` — verification entry point.

Lean and mathlib versions are pinned in `lean/lean-toolchain` and `lean/lakefile.lean`.

## Verification

From the repository root:

    cd lean
    python3 Verify.py

The verifier builds the complete `Sigma` import graph and evaluates the axiom audit in `SigmaAxioms.lean`.

Generated `.olean`, `.ilean`, `.lake`, and temporary build files are not part of the repository.

## Paper

Publication files:

- `paper/intrinsic-uniqueness-reconstruction.tex`
- `paper/intrinsic-uniqueness-reconstruction.pdf`

Supporting section sources are retained under `paper/sections/`.

## Audits

`audits/` contains the mathematical reconstruction record and formalization audits used during verification. These records are organized by mathematical role rather than internal development phase.
