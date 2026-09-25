# Mathematical proofs and Lean formalization audits

The paper contains mathematical proofs of its results. The Lean 4 project
formalizes those proofs and checks them in Lean's kernel. These are distinct
levels of documentation: an unfinished formalization is not an unproved
mathematical result.

In the coverage ledger, proved-result inventory, and formalization records:

- **Complete** means the paper statement has exact Lean coverage.
- **Partial** means some of its mathematical content still needs formalization.
- **Missing** means exact Lean coverage has not yet been supplied.
- **Remaining component** means a remaining Lean formalization task.

These statuses do not downgrade the paper's proved results to conjectures.
The machine-readable key `unproved_components` is retained for compatibility;
it means remaining Lean formalization components. The `labelled_equations`
records check displayed equations at equation level. Equations within named
statements are components of those statements, not additional paper results.

Use [the current coverage ledger](lean-coverage.md) and
[the formalized-result inventory](proved-inventory.md) for the current Lean
coverage. Earlier milestone and reconstruction reports retain their historical
scope and results; their dates and milestone totals are not current totals.
