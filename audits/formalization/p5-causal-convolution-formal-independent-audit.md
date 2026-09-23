# Independent P5 causal-convolution audit

Verdict: **AUDIT PASS** for the explicit `g = k * k` clause in the proof of
`final:P5`; this is not an audit pass for the entire named theorem.

The auditor compared the paper's full-line causal kernels
`k(t) = 1_{[0,∞)}(t) exp(-t)` and
`g(t) = 1_{[0,∞)}(t) t exp(-t)` with the definitions and signature of
`Sigma.causal_unit_exponential_convolution_eq_gamma_green`. The Lean
convolution is the Lebesgue integral over all `s : ℝ` of `k(s) k(t-s)`, and
the result identifies it with `g(t)` for every real `t`. The proof explicitly
covers the negative half-line, zero endpoint, and positive half-line. Thus it
does not conflate a whole-line convolution with an oriented-interval integral,
and does not omit endpoint or support behavior.

No distribution-valued equation, uniqueness among all supported
distributions, or Poisson-process arrival-time statement is concluded from
this formula. Those remain residual clauses of `final:P5` and keep its status
`partial`.
