# Independent P5 distributional Green-kernel audit

Verdict: **AUDIT PASS** for clause (iv) of `final:P5`; this is not an audit
pass for the entire named theorem.

The auditor compared the full paper clause—an actual distribution on `R`,
supported in `[0,∞)`, satisfying `(D+1)^2 g = δ₀`, with conclusion
`g(t)=1_[0,∞)(t)t e^{-t}`—against the test-functional definitions and theorem
signatures in `SigmaProbDistributionGreen.lean`.

- The test functions are smooth and compactly supported on all of `R`, not
  functions restricted to positive time.
- Causality is vanishing on negative-half-line tests, the support condition
  corresponding to support contained in `[0,∞)`.
- The derivative convention is `DT(φ)=-T(φ')`; the formal transpose of the
  squared shift is exactly `φ''-2φ'+φ`.
- The equation is tested against every test function and its right side is
  evaluation at zero, giving the exact Dirac normalization.
- Existence is the regular functional obtained by integration against the
  exact zero-extended kernel. The kernel is causal, and its pairing satisfies
  the proved `L¹` bound.
- Uniqueness is proved for all algebraic linear functionals satisfying
  causality and the equation, a strictly larger class than continuous
  distributions. Thus it does not add a regularity hypothesis to the paper's
  candidate class.
- The formula `g=k*k` is delegated to the separately verified
  whole-line convolution theorem and includes every real time.

No omitted support, endpoint, domain, normalization, PDE, or uniqueness clause
was found. The remaining P5 clause—the actual unit-rate Poisson process and
second-arrival law—is outside this milestone and keeps `final:P5` partial.
