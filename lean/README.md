# Lean 4 Formalization

This directory contains the Lean 4 formalization accompanying
_Intrinsic Uniqueness and Reconstruction Across Mathematical Presentations_.

## Entry points

`Sigma.lean` is the complete umbrella module.

`SigmaAxioms.lean` imports the complete formal development and evaluates
`#print axioms` for the exported declarations included in the formal audit.

Foundational modules:

- `SigmaBase.lean`
- `SigmaReconstruction.lean`
- `SigmaPresentations.lean`
- `SigmaFormalSeries.lean`

The remaining `Sigma*.lean` modules contain the corresponding exact
presentations, reconstruction theorems, converse results, boundary results,
realizations, and mathematical consequences.

## Toolchain

Lean is pinned by `lean-toolchain`.

The exact mathlib revision is pinned by `lakefile.lean`.

## Verification

From this directory run:

    python3 Verify.py

The verifier checks the source tree for admitted proofs, builds the complete
`Sigma` import graph, and executes the axiom audit in `SigmaAxioms.lean`.

Generated Lean build files are not part of the source repository.
