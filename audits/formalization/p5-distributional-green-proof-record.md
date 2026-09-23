# P5 distributional causal Green-kernel clause

Starting commit: `dacfccefaa91d1e1d154f0abb8e84f6c260efb88`.

This milestone formalizes clause (iv) of `final:P5` in
`lean/SigmaProbDistributionGreen.lean`. The test space consists of smooth,
compactly supported real functions on all of `R`. The derivative convention is
the standard distributional one, `DT(φ) = -T(φ')`; consequently the shifted
operator, when paired against a test function, acts by
`φ'' - 2φ' + φ`. Causality is vanishing on every test function supported
strictly to the left of zero, which is the test-function characterization of
support in `[0,∞)`.

The regular distribution defined by integration against
`causalGammaGreen(t) = 1_[0,∞)(t) t exp(-t)` satisfies the exact whole-line
equation `(D+1)^2 g = δ₀`; the right side is evaluation at zero, so its
normalization is exact. Its causal support and an `L¹` pairing bound are
proved. Uniqueness is established for the larger class of all algebraic linear
functionals on this test space satisfying causality and the equation, hence
applies to every distribution in the usual continuous-dual candidate class.
The representation as `k*k` reuses the existing full-real convolution theorem
`causal_unit_exponential_convolution_eq_gamma_green`.

This commit closes only the distributional Green-kernel clause. `final:P5`
remains `partial`: the genuine unit-rate Poisson-process construction and its
second-arrival law are still required. No O4, M3, or other coverage status is
part of this milestone.

The independent clause audit is recorded in
`p5-distributional-green-formal-independent-audit.md`.
