# P5 unit-rate Poisson-process construction

Target: the final sentence of `final:P5` in
`paper/sections/probability.tex`: the Gamma(2,1) probability is the law of the
second arrival of a unit-rate Poisson process.

The construction is on the actual probability space
`PoissonClockSpace = ℕ → AddCircle (1 : ℝ)` with its normalized product Haar
probability. Each coordinate is sent through the circle-to-`(0,1]` uniform
representative and then through `u ↦ -log u`. The resulting full sequence of
waiting times is proved independent, and each coordinate has the actual
`unitExpProbability` law. This is the standard exponential-interarrival
construction of a rate-one Poisson process.

`poissonRenewalArrival n` is the cumulative sum of the first `n+1` waiting
times; in particular the actual second arrival is index `1` and equals the sum
of the first two clocks. The associated counting process counts arrival epochs
with multiplicity. Its fixed-time count is measurable and almost surely
finite, its paths are monotone, and the arrival epochs tend to infinity almost
surely (proved using independence and Borel--Cantelli). The second-arrival
pushforward law is proved to equal `gammaProbability`, and the actual
at-most-one-arrival event has probability `(1+t) exp(-t)` for `t ≥ 0`.

The relevant declarations are in `SigmaProbPoissonClock.lean`,
`SigmaProbPoissonArrival.lean`, and `SigmaProbPoissonRenewal.lean`; the latter
is imported by `Sigma.lean` and included in `SigmaFormalization`. The proof
uses the actual first two coordinates of the constructed infinite clock
family, rather than assuming a separately supplied exponential pair or a
pre-existing Poisson process.

The independent exact-statement review is recorded in
`p5-poisson-process-formal-independent-audit.md`.
