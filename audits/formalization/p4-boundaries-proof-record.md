# Completed P4 deletion boundaries

Starting commit: `b681790d2062ce7d0deb41f27317a2756e51b031`.

Reused the existing upper-branch source-law counterexample. Added the two
remaining normalized-potential witnesses:

- `SigmaProbDeficitLawShift.lean`: a compact common-level coordinate shift is
  proved to be an order isomorphism fixing zero and one. The shifted potential
  satisfies the exact two-branch category and retains every sublevel width.
- `SigmaProbDeficitWidth.lean`: finite sublevel masses determine the actual
  unweighted level measure, even though its total mass is infinite. Weighting
  transfers this to equality of linked deficit laws and source normalization.
- `SigmaProbDeficitLawBoundary.lean`: assembles the same-deficit-law witness,
  including real density integrability, integral one and different pairing.
- `SigmaProbInvolutionBoundary.lean`: an explicitly balanced level perturbation
  gives a normalized noncanonical potential with the exact canonical involution
  and a different actual deficit probability law.

Whole-statement independent adversarial audit: PASS. The second construction
uses a direct zero-mean weight instead of the paper proof's implicit-function
argument, without strengthening the candidate class or moving its anchor.

Single integration gate: source proof-escape audit PASS; SigmaFormalization
build PASS; transitive axiom checks of both new final witnesses, both width-law
bridges and the reused source-law counterexample PASS. Only ordinary foundations
`propext`, `Classical.choice`, `Quot.sound` occur. Project warnings: zero.
SigmaAxioms is synchronized; no additional broad verifier was run.

Coverage: 80 named items; 2 definitions, 52 complete, 18 partial, 8 missing.
Unrelated and ongoing proof work is not included in this milestone.
