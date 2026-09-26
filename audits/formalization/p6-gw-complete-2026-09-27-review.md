# P6-gw: complete paper-to-Lean review

Date: 2026-09-27. Whole-statement reviewer: `/root/paper_coverage_review`.
Independent cross-reviewer: `/root/missing_countermodels`.

## Verdict

**COMPLETE PASS for `final:P6-gw`. No named-statement residuals remain.**

- The inverse cumulative sampler has the exact native PMF pushforward law. Countable iid word coordinates and whole-subtree independence are derived from Haar measures, with actual root independence.
- Finite words are retained exactly when their ancestor offspring counts permit each edge. Zero-based child indices merely relabel the paper's positive indices. The full tree map is measurable.
- Total size is literally counting measure of the retained-word set. It equals the increasing supremum of finite-depth counts, obeys the proved root decomposition, and is finite exactly when some finite depth is extinct.
- Actual root conditioning derives the extinction recurrence and, under explicit almost-sure actual-size finiteness, the total-size PGF equation. Neither equation is assumed in the final theorem.
- Poisson extinction follows by monotone convergence of the actual extinction probabilities, the derived exponential fixedpoint equation, and its unique probability-range solution one.
- The resulting Poisson total-size law is Borel by the derived PGF equation and fixedpoint/analytic coefficient uniqueness. Its exact probabilities are linked to the earlier Borel coefficient formula.
- Conversely, actual Borel-law equality on the extended nonnegative reals itself yields almost-sure finiteness. Natural-size conversion is then justified before root conditioning and Poisson identification.
- `iid_gw_borel_iff_poisson` applies to arbitrary supplied measurable iid arrays with their stated common offspring law; there is no finiteness or desired-PGF premise.
- `iid_gw_borel_determines_tree_law` identifies the entire literal rooted-tree pushforward law, using equality of full array measures derived from finite-dimensional projective uniqueness.

## Independent verification

All new sources elaborated cleanly. Targeted transitive axiom checks of principal infrastructure and all final equivalences returned only `propext`, `Classical.choice`, and `Quot.sound`.

The whole-statement reviewer independently audited the sampler, array laws, deterministic tree, canonical construction, size conditioning, scalar Borel identification and final equivalence. The source-independence, generic conditioning and extinction modules authored by that reviewer received a separate independent PASS from `missing_countermodels`. Thus every new implementation component has a review by a different agent.

The forward law proof uses uniqueness of the probability-range fixedpoint rather than repeating formal coefficient extraction. A general least-fixedpoint theory for all offspring laws is not claimed; this proof-only variation omits no clause of the named theorem.
