# Historical research and formalization records

These records preserve the reconstruction and formalization campaign. **Their
milestone counts, partial statuses, instructions and local paths are historical.**
The [current audit guide](../README.md), [coverage ledger](../lean-coverage.md)
and [verification report](../axiom-dependencies.md) describe the present project.

## Organization

- [formalization/](formalization/) contains bounded reviews, proof records,
  superseded component maps and milestone axiom reports. The four maintained
  generator inputs now live in [maps/](../maps/).
- [reconstruction/](reconstruction/) contains the earlier mathematical audit,
  proof/counterexample record, typed dependency graph and diagnostics.
- The dependency, ten-field and verification ledgers at this level describe
  the earlier reconstruction, not current Lean coverage.

Proof records retain their mathematical content. Historical Markdown has an
explicit banner and repaired navigation. Misleading `current-` filename
prefixes were removed from archived milestones. The duplicate reconstruction
`formal.md` was consolidated into [verification.md](reconstruction/verification.md),
which contains the same verification narrative and the additional final
source-search record. The larger proof record's mathematical appendices are
retained, even where they overlap standalone reviews.

## Provenance and reproduction

Historical JSON maps, frozen manifests, input hashes and diagnostic records
are preserved byte-for-byte. Paths inside those snapshots name the original
workspace; they are provenance, not current runnable paths. Some original
external manuscripts, temporary check files and compiler logs are not included
in this repository. Their names and hashes are retained as evidence; Markdown
references to absent artifacts are explicitly labelled rather than linked to
unrelated current files.

Manifest hashes describe their original snapshots, before the archival notices
and link repairs; they are not checksums of the current Markdown copies. The
[pre-cleanup repository snapshot](https://github.com/mripr-institute/intrinsic-uniqueness-reconstruction/tree/6a4896052e5ff7e9afeeb1696f0de9741fd04e24)
retains the documents at their former paths, including the consolidated duplicate.

The [graph checker](../../scripts/history/global-graph-checks.py) resolves the
old graph register's document names to this archive without rewriting the
frozen graph. The [core-series checker](../../scripts/history/core-series-checks.py)
repeats its finite symbolic diagnostics. See [tooling](../../scripts/README.md#historical-diagnostics)
for commands and the SymPy dependency. Neither check reruns the historical
external-input campaign or establishes current Lean coverage.

## Documentation classification

This inventory accounts for every Markdown file present before housekeeping.
**A** = canonical/current; **B** = historical evidence retained; **C** = generated
current audit; **D** = duplicated narrative consolidated. No mathematical proof
record was discarded as a temporary checklist. Generated current audits remain
outside this archive.

| Original document | Class | Disposition / current location |
| --- | --- | --- |
| `README.md` | A | [Reorganized](../../README.md) |
| `audits/README.md` | A | [Reorganized](../README.md) |
| `audits/audit-ledger.md` | B | [Archived with historical notice](audit-ledger.md) |
| `audits/dependency-ledger.md` | B | [Archived with historical notice](dependency-ledger.md) |
| `audits/formalization/b4-trace-reconstruction-formal-independent-audit.md` | B | [Archived with historical notice](formalization/b4-trace-reconstruction-formal-independent-audit.md) |
| `audits/formalization/b4-trace-reconstruction-proof-record.md` | B | [Archived with historical notice](formalization/b4-trace-reconstruction-proof-record.md) |
| `audits/formalization/canonical-calculus-formal-independent-audit.md` | B | [Archived with historical notice](formalization/canonical-calculus-formal-independent-audit.md) |
| `audits/formalization/canonical-calculus-proof-record.md` | B | [Archived with historical notice](formalization/canonical-calculus-proof-record.md) |
| `audits/formalization/closure-proof-record.md` | B | [Archived with historical notice](formalization/closure-proof-record.md) |
| `audits/formalization/core-formal-independent-audit.md` | B | [Archived with historical notice](formalization/core-formal-independent-audit.md) |
| `audits/formalization/current-analytic-recovery-cumulants-proof-record.md` | B | [Archived with historical notice](formalization/analytic-recovery-cumulants-proof-record.md) |
| `audits/formalization/current-arithmetic-closure-matrix-boundary-proof-record.md` | B | [Archived with historical notice](formalization/arithmetic-closure-matrix-boundary-proof-record.md) |
| `audits/formalization/current-arithmetic-geodesic-proof-record.md` | B | [Archived with historical notice](formalization/arithmetic-geodesic-proof-record.md) |
| `audits/formalization/current-b2-p8-proof-record.md` | B | [Archived with historical notice](formalization/b2-p8-proof-record.md) |
| `audits/formalization/current-baseline.md` | B | [Archived with historical notice](formalization/baseline.md) |
| `audits/formalization/current-c8-proof-record.md` | B | [Archived with historical notice](formalization/c8-proof-record.md) |
| `audits/formalization/current-divisors-rankone-todd-proof-record.md` | B | [Archived with historical notice](formalization/divisors-rankone-todd-proof-record.md) |
| `audits/formalization/current-formal-automorphisms-proof-record.md` | B | [Archived with historical notice](formalization/formal-automorphisms-proof-record.md) |
| `audits/formalization/current-m2-proof-record.md` | B | [Archived with historical notice](formalization/m2-proof-record.md) |
| `audits/formalization/current-matrix-density-proof-record.md` | B | [Archived with historical notice](formalization/matrix-density-proof-record.md) |
| `audits/formalization/current-milestone-proof-record.md` | B | [Archived with historical notice](formalization/milestone-proof-record.md) |
| `audits/formalization/current-pearson-rational-tree-proof-record.md` | B | [Archived with historical notice](formalization/pearson-rational-tree-proof-record.md) |
| `audits/formalization/current-radial-drift-matrix-proof-record.md` | B | [Archived with historical notice](formalization/radial-drift-matrix-proof-record.md) |
| `audits/formalization/current-samples-automorphisms-proof-record.md` | B | [Archived with historical notice](formalization/samples-automorphisms-proof-record.md) |
| `audits/formalization/f4-complete-2026-09-27-review.md` | B | [Archived with historical notice](formalization/f4-complete-2026-09-27-review.md) |
| `audits/formalization/f5-complexification-component-formal-independent-audit.md` | B | [Archived with historical notice](formalization/f5-complexification-component-formal-independent-audit.md) |
| `audits/formalization/f5-native-k0-rational-proof-record.md` | B | [Archived with historical notice](formalization/f5-native-k0-rational-proof-record.md) |
| `audits/formalization/f5-nontriviality-proof-record.md` | B | [Archived with historical notice](formalization/f5-nontriviality-proof-record.md) |
| `audits/formalization/f5-tensor-square-bridge-proof-record.md` | B | [Archived with historical notice](formalization/f5-tensor-square-bridge-proof-record.md) |
| `audits/formalization/fenchel-converse-statement-audit.md` | B | [Archived with historical notice](formalization/fenchel-converse-statement-audit.md) |
| `audits/formalization/gaussian-wishart-formal-independent-audit.md` | B | [Archived with historical notice](formalization/gaussian-wishart-formal-independent-audit.md) |
| `audits/formalization/gaussian-wishart-proof-record.md` | B | [Archived with historical notice](formalization/gaussian-wishart-proof-record.md) |
| `audits/formalization/global-a-b-proof-record.md` | B | [Archived with historical notice](formalization/global-a-b-proof-record.md) |
| `audits/formalization/global-c-d-boundary-proof-record.md` | B | [Archived with historical notice](formalization/global-c-d-boundary-proof-record.md) |
| `audits/formalization/global-e-complete-2026-09-27-review.md` | B | [Archived with historical notice](formalization/global-e-complete-2026-09-27-review.md) |
| `audits/formalization/laguerre-spectrum-formal-independent-audit.md` | B | [Archived with historical notice](formalization/laguerre-spectrum-formal-independent-audit.md) |
| `audits/formalization/laguerre-spectrum-proof-record.md` | B | [Archived with historical notice](formalization/laguerre-spectrum-proof-record.md) |
| `audits/formalization/m3-canonical-path-admissibility-formal-independent-audit.md` | B | [Archived with historical notice](formalization/m3-canonical-path-admissibility-formal-independent-audit.md) |
| `audits/formalization/m3-canonical-path-admissibility-proof-record.md` | B | [Archived with historical notice](formalization/m3-canonical-path-admissibility-proof-record.md) |
| `audits/formalization/m3-global-distance-formal-independent-audit.md` | B | [Archived with historical notice](formalization/m3-global-distance-formal-independent-audit.md) |
| `audits/formalization/matrix-calculus-formal-independent-audit.md` | B | [Archived with historical notice](formalization/matrix-calculus-formal-independent-audit.md) |
| `audits/formalization/o3-complete-2026-09-27-review.md` | B | [Archived with historical notice](formalization/o3-complete-2026-09-27-review.md) |
| `audits/formalization/o3-form-complete-2026-09-26-review.md` | B | [Archived with historical notice](formalization/o3-form-complete-2026-09-26-review.md) |
| `audits/formalization/o3-form-sesquilinear-2026-09-26-review.md` | B | [Archived with historical notice](formalization/o3-form-sesquilinear-2026-09-26-review.md) |
| `audits/formalization/o3-maximal-flux-2026-09-26-review.md` | B | [Archived with historical notice](formalization/o3-maximal-flux-2026-09-26-review.md) |
| `audits/formalization/o4-convergence-boundary-proof-record.md` | B | [Archived with historical notice](formalization/o4-convergence-boundary-proof-record.md) |
| `audits/formalization/o4-determinants-2026-09-26-review.md` | B | [Archived with historical notice](formalization/o4-determinants-2026-09-26-review.md) |
| `audits/formalization/o4-determinants-complete-2026-09-27-review.md` | B | [Archived with historical notice](formalization/o4-determinants-complete-2026-09-27-review.md) |
| `audits/formalization/o4-finite-countermodels-2026-09-27-review.md` | B | [Archived with historical notice](formalization/o4-finite-countermodels-2026-09-27-review.md) |
| `audits/formalization/o4-resolvents-2026-09-26-review.md` | B | [Archived with historical notice](formalization/o4-resolvents-2026-09-26-review.md) |
| `audits/formalization/o4-zeta-determinant-2026-09-26-review.md` | B | [Archived with historical notice](formalization/o4-zeta-determinant-2026-09-26-review.md) |
| `audits/formalization/o5-generic-strong-mixing-formal-independent-audit.md` | B | [Archived with historical notice](formalization/o5-generic-strong-mixing-formal-independent-audit.md) |
| `audits/formalization/o5-mixing-and-gamma3-components-formal-independent-audit.md` | B | [Archived with historical notice](formalization/o5-mixing-and-gamma3-components-formal-independent-audit.md) |
| `audits/formalization/o6-canonical-inverse-formal-independent-audit.md` | B | [Archived with historical notice](formalization/o6-canonical-inverse-formal-independent-audit.md) |
| `audits/formalization/o6-generic-functional-calculus-formal-independent-audit.md` | B | [Archived with historical notice](formalization/o6-generic-functional-calculus-formal-independent-audit.md) |
| `audits/formalization/p4-boundaries-formal-independent-audit.md` | B | [Archived with historical notice](formalization/p4-boundaries-formal-independent-audit.md) |
| `audits/formalization/p4-boundaries-proof-record.md` | B | [Archived with historical notice](formalization/p4-boundaries-proof-record.md) |
| `audits/formalization/p5-causal-convolution-formal-independent-audit.md` | B | [Archived with historical notice](formalization/p5-causal-convolution-formal-independent-audit.md) |
| `audits/formalization/p5-causal-convolution-proof-record.md` | B | [Archived with historical notice](formalization/p5-causal-convolution-proof-record.md) |
| `audits/formalization/p5-distributional-green-formal-independent-audit.md` | B | [Archived with historical notice](formalization/p5-distributional-green-formal-independent-audit.md) |
| `audits/formalization/p5-distributional-green-proof-record.md` | B | [Archived with historical notice](formalization/p5-distributional-green-proof-record.md) |
| `audits/formalization/p5-poisson-process-formal-independent-audit.md` | B | [Archived with historical notice](formalization/p5-poisson-process-formal-independent-audit.md) |
| `audits/formalization/p5-poisson-process-proof-record.md` | B | [Archived with historical notice](formalization/p5-poisson-process-proof-record.md) |
| `audits/formalization/p5-survival-boundaries-formal-independent-audit.md` | B | [Archived with historical notice](formalization/p5-survival-boundaries-formal-independent-audit.md) |
| `audits/formalization/p5-survival-boundaries-proof-record.md` | B | [Archived with historical notice](formalization/p5-survival-boundaries-proof-record.md) |
| `audits/formalization/p6-boundaries-formal-independent-audit.md` | B | [Archived with historical notice](formalization/p6-boundaries-formal-independent-audit.md) |
| `audits/formalization/p6-boundaries-proof-record.md` | B | [Archived with historical notice](formalization/p6-boundaries-proof-record.md) |
| `audits/formalization/p6-gw-complete-2026-09-27-review.md` | B | [Archived with historical notice](formalization/p6-gw-complete-2026-09-27-review.md) |
| `audits/formalization/p8-complete-2026-09-27-review.md` | B | [Archived with historical notice](formalization/p8-complete-2026-09-27-review.md) |
| `audits/formalization/p8-levy-complete-2026-09-27-review.md` | B | [Archived with historical notice](formalization/p8-levy-complete-2026-09-27-review.md) |
| `audits/formalization/probability-formal-independent-audit.md` | B | [Archived with historical notice](formalization/probability-formal-independent-audit.md) |
| `audits/formalization/probability-transforms-proof-record.md` | B | [Archived with historical notice](formalization/probability-transforms-proof-record.md) |
| `audits/formalization/r1-geometry-2026-09-27-review.md` | B | [Archived with historical notice](formalization/r1-geometry-2026-09-27-review.md) |
| `audits/formalization/r1-stochastic-proof-record.md` | B | [Archived with historical notice](formalization/r1-stochastic-proof-record.md) |
| `audits/formalization/realization-formal-series-audit.md` | B | [Archived with historical notice](formalization/realization-formal-series-audit.md) |
| `audits/formalization/residual-low-distance-2026-09-23-proof-record.md` | B | [Archived with historical notice](formalization/residual-low-distance-2026-09-23-proof-record.md) |
| `audits/formalization/stein-statement-audit.md` | B | [Archived with historical notice](formalization/stein-statement-audit.md) |
| `audits/formalization/stieltjes-proof-record.md` | B | [Archived with historical notice](formalization/stieltjes-proof-record.md) |
| `audits/lean-coverage.md` | C | [Regenerated from maintained maps](../lean-coverage.md) |
| `audits/proved-inventory.md` | C | [Regenerated from maintained maps](../proved-inventory.md) |
| `audits/reconstruction/core-series-blind.md` | B | [Archived with historical notice](reconstruction/core-series-blind.md) |
| `audits/reconstruction/core-series.md` | B | [Archived with historical notice](reconstruction/core-series.md) |
| `audits/reconstruction/final-synthesis.md` | B | [Archived with historical notice](reconstruction/final-synthesis.md) |
| `audits/reconstruction/formal.md` | D | [Consolidated into verification record](reconstruction/verification.md) |
| `audits/reconstruction/global-minimality.md` | B | [Archived with historical notice](reconstruction/global-minimality.md) |
| `audits/reconstruction/independent-audit.md` | B | [Archived with historical notice](reconstruction/independent-audit.md) |
| `audits/reconstruction/minimal-primitives.md` | B | [Archived with historical notice](reconstruction/minimal-primitives.md) |
| `audits/reconstruction/operator-blind.md` | B | [Archived with historical notice](reconstruction/operator-blind.md) |
| `audits/reconstruction/operator.md` | B | [Archived with historical notice](reconstruction/operator.md) |
| `audits/reconstruction/probability-blind.md` | B | [Archived with historical notice](reconstruction/probability-blind.md) |
| `audits/reconstruction/probability.md` | B | [Archived with historical notice](reconstruction/probability.md) |
| `audits/reconstruction/proof-record.md` | B | [Archived with historical notice](reconstruction/proof-record.md) |
| `audits/reconstruction/realizations-blind.md` | B | [Archived with historical notice](reconstruction/realizations-blind.md) |
| `audits/reconstruction/realizations.md` | B | [Archived with historical notice](reconstruction/realizations.md) |
| `audits/reconstruction/reconstruction-theorem.md` | B | [Archived with historical notice](reconstruction/reconstruction-theorem.md) |
| `audits/reconstruction/synthesis-statement-brief.md` | B | [Archived with historical notice](reconstruction/synthesis-statement-brief.md) |
| `audits/reconstruction/verification.md` | B | [Archived with historical notice](reconstruction/verification.md) |
| `audits/reconstruction/zero-set-counterexample.md` | B | [Archived with historical notice](reconstruction/zero-set-counterexample.md) |
| `audits/verification-ledger.md` | B | [Archived with historical notice](verification-ledger.md) |
| `lean/README.md` | A | [Reorganized](../../lean/README.md) |
