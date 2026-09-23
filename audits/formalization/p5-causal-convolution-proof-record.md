# P5 causal convolution clause

Starting commit: `f5ec672aefee5526c3e8ef62761e06dc601e3fb2`.

The exact whole-line convolution identity in the proof of `final:P5` is now
formalized. In `SigmaProbCausalConvolution.lean`, `causalUnitExponential` is
the zero extension of `exp(-t)` from the nonnegative ray, and
`causalGammaGreen` is the zero extension of `t * exp(-t)`. The theorem
`causal_unit_exponential_convolution_eq_gamma_green` proves their ordinary
Lebesgue convolution identity for every real `t`, covering negative times,
the endpoint `t = 0`, and positive times. This is the full-line convolution,
not only the integral over an oriented interval.

The proof reduces the nonnegative-time integral to the existing exact
exponential-pair interval integral; for negative times the integrand vanishes
identically. The theorem is imported by `Sigma.lean`, registered in
`lakefile.lean`, and included in `SigmaAxioms.lean`.

This closes only the explicit convolution formula clause of `final:P5`.
Coverage remains `partial`: the distributional Green-kernel existence and
uniqueness clause and the actual second-arrival-time law of a unit-rate Poisson
process are not established by this milestone. No parent coverage status is
promoted.

The independent clause audit is recorded in
`p5-causal-convolution-formal-independent-audit.md`.
