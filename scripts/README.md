# Repository tooling

Run commands from the repository root unless indicated otherwise.
Python tooling requires Python 3.10 or newer.

| Command | Purpose and output |
| --- | --- |
| `python3 lean/Build.py` | Full library build; local raw log in `lean/.lake/build.log` |
| `python3 lean/Verify.py` | Source admission scan, full build and complete committed axiom-check list |
| `python3 lean/Verify.py --write-report` | Same checks, then generate `audits/axiom-dependencies.json` and `.md` |
| `python3 lean/Verify.py --check-report` | Check saved fingerprints, declaration accounting and rendering; does not run Lean |
| `python3 scripts/rebuild_coverage.py --write` | Generate coverage JSON/Markdown, proved inventory and root README coverage table |
| `python3 scripts/rebuild_coverage.py --check --lean --require-complete` | Check artifacts, kernel-resolve mapped names and require complete named-result/equation coverage |
| `python3 scripts/check_docs.py` | Check local Markdown links, heading/line anchors and maintained audit-map paths |
| `python3 scripts/build_publication.py` | Three clean pdfLaTeX passes; replace publication PDF after cross-reference and diagnostic checks |

The publication command requires TeX Live or MacTeX with `pdflatex`. Its
auxiliary files stay under ignored `paper/publication-build/`. It is a
manuscript publishing tool, not part of Lean or documentation verification.

## Historical diagnostics

These checks supplement archived written proofs. They do not establish
universal mathematics or current Lean coverage. They compare fresh results
with preserved diagnostic records without overwriting those records.

```sh
python3 scripts/history/global-graph-checks.py
python3 scripts/history/core-series-checks.py
```

The graph checker uses the Python standard library and resolves the original
graph's path names to archived documents. The core-series checker requires
SymPy; install it in a separate environment:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install sympy==1.13.3
.venv/bin/python scripts/history/core-series-checks.py
```

The [archive guide](../audits/history/README.md) distinguishes these rerunnable
diagnostics from frozen manifests and records whose original external inputs
are not distributed in this repository.
