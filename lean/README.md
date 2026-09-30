# Lean 4 formal reconstruction

The paper supplies the mathematical proofs; this directory contains their
formal encodings and supporting infrastructure. See the
[root README](../README.md#formal-reconstruction-in-lean-4) for current totals
and the [audit guide](../audits/README.md) for their exact scope.

## Entry points

| File | Purpose |
| --- | --- |
| [Sigma.lean](Sigma.lean) | Complete umbrella import |
| [SigmaAxioms.lean](SigmaAxioms.lean) | Committed declaration list for transitive axiom inspection |
| [SigmaBase.lean](SigmaBase.lean) | Intrinsic algebraic and convex primitives |
| [SigmaReconstruction.lean](SigmaReconstruction.lean) | Differential reconstruction |
| [SigmaPresentations.lean](SigmaPresentations.lean) | Exact presentations and reversible transformations |
| [SigmaCore.lean](SigmaCore.lean) | Intrinsic analytic core |
| [SigmaProbability.lean](SigmaProbability.lean) | Probability development |
| [SigmaFormalSeries.lean](SigmaFormalSeries.lean) | Formal-series development |
| [SigmaRealizations.lean](SigmaRealizations.lean) | Realization development |

The remaining `Sigma*.lean` modules supply the analytic, measure, operator,
matrix, stochastic, topological and arithmetic results and their countermodels.
Use the [proved inventory](../audits/proved-inventory.md) to navigate by paper
statement. Module names and the flat import layout are retained.

## Toolchain and build

[lean-toolchain](lean-toolchain) pins Lean; [lakefile.lean](lakefile.lean) and
[lake-manifest.json](lake-manifest.json) pin mathlib and its dependencies.
Python tooling requires Python 3.10 or newer.

From this directory:

```sh
lake build cache
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
python3 Build.py
python3 Verify.py
```

The cache commands are useful for initial setup. Running the cache program
through Lean avoids the macOS loader failure observed with its compiled
executable under this pinned toolchain. `Build.py` invokes
`lake --no-ansi build SigmaFormalization`. It filters cached mathlib docstring
diagnostics while retaining project warnings and errors. The full output is in
`.lake/build.log`; `--all-warnings` also prints it. Direct
`lake build SigmaFormalization` gives unfiltered output.

`Verify.py` runs the source admission/axiom-declaration scan, full library build
and all axiom commands. It checks that every requested declaration produced
exactly one report and rejects dependencies outside `propext`,
`Classical.choice` and `Quot.sound`. Raw axiom output is in `.lake/axioms.log`.

## Audit maintenance

From the repository root:

```sh
python3 scripts/rebuild_coverage.py --check --lean --require-complete
python3 lean/Verify.py --write-report
python3 lean/Verify.py --check-report
```

The first validates coverage and resolves mapped declarations; the second
refreshes build/dependency evidence after a full run. The last checks saved
evidence against current sources without executing Lean again. See the
[tooling guide](../scripts/README.md) for regeneration and link checks.

Build products, dependency checkouts and raw logs are ignored. The dependency
manifest and canonical generated audit reports are intentionally versioned.
