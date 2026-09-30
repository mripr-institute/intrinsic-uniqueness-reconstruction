# Intrinsic Uniqueness and Reconstruction Across Mathematical Presentations

The mathematical paper, its formal reconstruction in Lean 4, and the coverage
and verification evidence are maintained together in this repository.

## Paper

**Alex Albert** — Mathematical Research Institute of Physical Reality (MRIPR),
Pécs, Hungary.

- [Paper PDF](paper/intrinsic-uniqueness-reconstruction.pdf)
- [LaTeX source](paper/intrinsic-uniqueness-reconstruction.tex)
- [Archival record / DOI: 10.5281/zenodo.22775358](https://doi.org/10.5281/zenodo.22775358)

The complete identifying presentations established in the work are exact
presentations of the same intrinsic mathematical object Σ. The reconstruction
theorems retain their stated candidate classes, calibrations and contexts;
counterexamples establish the boundaries of reconstruction.

## Formal reconstruction in Lean 4

**The current coverage audit records complete formalization of every named
mathematical result in the paper.**

<!-- BEGIN GENERATED COVERAGE -->
| Coverage measure | Current inventory |
| --- | --- |
| Tracked named paper items | 80 (2 definitions and 78 named results) |
| Fully formalized named results | **78/78** |
| Tracked labelled equations | **15/15 complete** |
| Partial / missing named results | **0 / 0** |
| Distinct declarations mapped to named items | **2,039** (including definitions and helpers) |
| Distinct declarations checked across named items and equations | 2,057 |

Generated from the [coverage ledger](audits/lean-coverage.md) and
[proved inventory](audits/proved-inventory.md); `rebuild_coverage.py --check`
also checks this summary.
<!-- END GENERATED COVERAGE -->

These are distinct Lean declarations, **not a count of paper theorems or
independent proofs of one theorem**. A single paper result can require
definitions, supporting lemmas, analytic and measure-theoretic infrastructure,
domain proofs and countermodels, each separately encoded and typechecked.

The [build and axiom-dependency report](audits/axiom-dependencies.md) records a
successful full library build, no `sorry`, `admit`, `sorryAx` or project axiom
declarations in the source scan, and dependencies limited to `propext`,
`Classical.choice` and `Quot.sound` for the full committed axiom-check list.
The report identifies the verified sources by their fingerprints.

The paper provides the mathematical proofs. Lean kernel typechecking verifies
their formal reconstruction under the stated hypotheses. The coverage maps
identify the Lean declarations corresponding to each named paper result.

## Verification and audit structure

| Evidence | What it establishes |
| --- | --- |
| [Paper-to-Lean coverage](audits/lean-coverage.md) · [JSON](audits/lean-coverage.json) | Named-statement and tracked equation coverage, source locations, declaration mappings and explicit scope |
| [Proved inventory](audits/proved-inventory.md) | Formalized components and distinct declaration mappings for each paper item |
| [Reviewed source maps](audits/maps/) | Maintained generator inputs, hypotheses and cumulative review provenance |
| [Build and axiom dependencies](audits/axiom-dependencies.md) · [JSON](audits/axiom-dependencies.json) | Full build, source admission scan and transitive dependencies for the committed check list |
| [Audit guide](audits/README.md) | Authoritative files, generation commands and limits of each check |

## Repository map

| Path | Purpose |
| --- | --- |
| [paper/](paper/) | Finished manuscript, section sources and PDF |
| [lean/](lean/README.md) | Lean sources, pinned dependencies, build and verification entry points |
| [audits/](audits/README.md) | Current coverage, declaration and verification reports |
| [audits/maps/](audits/maps/) | Four maintained paper-to-Lean source maps |
| [audits/history/](audits/history/README.md) | Historical reconstruction audits, reviews and milestone evidence; not current status |
| [scripts/](scripts/README.md) | Coverage generation, documentation checks and publication tooling |
| [scripts/history/](scripts/history/) | Diagnostics for the archived reconstruction records |

The complete Lean entry point is [Sigma.lean](lean/Sigma.lean). The flat module
layout and import graph are retained. No GitHub Actions workflow is currently
configured; the commands below run the repository's checks locally.

## Reproducing the Lean build

Requirements: Python 3.10 or newer and an `elan` installation providing `lean`
and `lake`. The project pins **Lean 4.14.0** in
[lean-toolchain](lean/lean-toolchain) and mathlib in
[lakefile.lean](lean/lakefile.lean) and [lake-manifest.json](lean/lake-manifest.json).

From a fresh checkout, obtain the pinned dependency cache:

```sh
cd lean
lake build cache
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
cd ..
```

The interpreter invocation avoids a macOS loader failure observed with the
pinned toolchain's compiled cache executable. It runs the same mathlib cache
program and requires network access on initial setup.

From the repository root:

```sh
python3 lean/Verify.py
python3 scripts/rebuild_coverage.py --check --lean --require-complete
python3 scripts/check_docs.py
```

`Verify.py` scans for admissions and project axioms, builds the complete
`SigmaFormalization` library, then executes every `#print axioms` command in
[SigmaAxioms.lean](lean/SigmaAxioms.lean). It requires exactly one report per
requested declaration and rejects unexpected dependencies. The full axiom
scan can take substantially longer than a cached build.

For compilation alone, use `python3 lean/Build.py`. Its equivalent Lake command,
from `lean/`, is `lake build SigmaFormalization`. The wrapper retains project
warnings and errors while filtering cached mathlib docstring-linter messages;
`--all-warnings` prints the complete log. Build products and raw logs stay in
the ignored `lean/.lake/` directory.

## Regenerating audits

From the repository root:

```sh
python3 scripts/rebuild_coverage.py --write
python3 scripts/rebuild_coverage.py --check --lean --require-complete
python3 lean/Verify.py --write-report
python3 lean/Verify.py --check-report
python3 scripts/check_docs.py
```

Coverage generation updates the JSON ledger, both detailed Markdown reports
and the README coverage table from the same maintained maps. `--write-report`
runs the complete build and axiom scan before updating verification evidence.
`--check-report` checks saved fingerprints and report consistency; it is not a
new Lean run. See the [tooling guide](scripts/README.md) for historical
diagnostics and manuscript build commands.

## Citation and archive

Alex Albert. *Intrinsic Uniqueness and Reconstruction Across Mathematical
Presentations*. Mathematical Research Institute of Physical Reality (MRIPR).
[DOI: 10.5281/zenodo.22775358](https://doi.org/10.5281/zenodo.22775358).

## License

This repository does not currently include a license file. No additional
license grant is stated here; dependencies retain their own licenses.
