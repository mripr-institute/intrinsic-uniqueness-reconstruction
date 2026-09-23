# Independent P6-boundaries audit

Verdict: **AUDIT PASS** for the entire named statement `final:P6-boundaries`.

The independent coverage auditor compared the paper with actual Lean signatures
and witness definitions, including actual probability laws rather than scalar
sequences. Every named nonidentification assertion has a genuine witness:
rooted-tree laws, smooth normalized densities with identical inverse germs,
critical iid branching, and identical leading Borel tails.

The smooth witness derives positivity, normalization, branch shape, maximum and
endpoint limits; its nonidentity is an almost-everywhere distinction. The critical
witness derives the active tree and infinite total progeny from the offspring
array, rather than assuming a total-progeny conclusion.

Scope: deterministic infinite unary branching proves the named criticality-alone
assertion, which imposes no nondegeneracy or extinction premise. It does not prove
the stronger finite-extinct binary example used in the paper's explanatory proof.
