# Exact Stein statement audit

`final:O1` and `final:O1-kernel` are completely proved in the ten `SigmaFinalStein*.lean` modules listed in `stein-lean-map.json`. All files compiled before promotion; the 63 theorem declarations have only `propext`, `Classical.choice`, and `Quot.sound` in their printed dependencies. No theorem admits a proof escape or custom axiom.

## Full-line measure characterization

`weak_stein_characterization` takes an arbitrary native Borel measure on `ℝ` with native `IsProbabilityMeasure`. Its `WeakGammaStein` premise quantifies over every native `ContDiff ℝ ∞` real function with `HasCompactSupport`, and uses the actual derivative and actual Bochner integral on the whole real line. `stein_test_integrable` proves those integrands integrable from finite mass alone. Neither support, absolute continuity, density regularity, moments nor exponential integrability is supplied.

The formal proof differs from the draft's distributional half-line proof while establishing exactly the same statement. With a native smooth bump `χ`, test `t^(2n+1) χ(t/R)^2`. A pointwise completed-square inequality bounds the next even cutoff moment by the previous even moment plus the zero Stein integral. Native integration over a compact-interval cover yields the next genuine even moment. Induction gives every even moment, and domination gives every monomial. Native dominated convergence then yields the polynomial recurrence `m_(n+1)=(n+2)m_n`. Probability normalization gives `(n+1)!`. The previously compiled actual full-real-line factorial-moment uniqueness theorem identifies the measure. The converse uses the actual derivative of `t^2 exp(-t)` and compact-support integration by parts.

Separate theorems identify the exact `volume.withDensity` measure with density `1_(0,infinity) t exp(-t)`, prove native absolute continuity, prove mass zero on `(-infinity,0]`, prove no atoms at any real point, and give both integrability and values of all moments. Here “positive support” means concentration on the positive ray; it does not incorrectly assert that the closed topological support omits zero.

## Locally integrable kernel characterization

`weak_stein_kernel_iff_family` assumes only native `LocallyIntegrableOn (tau*p) (Ioi 0) volume`. This is weaker than the draft's additional measurability of `tau`. `WeakDerivativePositive` is a transparent definition of the actual compact smooth test pairing equation, not a custom axiom or a differentiable-density premise. Tests are native smooth functions on `ℝ` whose topological supports are compact and contained in the positive ray, the standard zero-extension representation of `C_c^infinity(0,infinity)`.

The zero-derivative implication is proved. A compact positive-ray smooth function of integral zero has a compact positive-ray smooth primitive, constructed by an actual interval integral and differentiated using the fundamental theorem. Subtracting the integral times a normalized native bump reduces arbitrary tests to derivative tests. The native `AEEqOfIntegralContDiff` fundamental lemma gives almost-everywhere constancy. Applied to `tau*p-t^2 exp(-t)`, it yields precisely `tau=t+C exp(t)/t` almost everywhere. Every member satisfies the actual weak equation.

The representative is derived rather than assumed. It is smooth, has the actual specified derivative, and satisfies the actual integral fundamental theorem on every compact interval. The pinned library does not have a named function `AbsolutelyContinuousOn` predicate. Accordingly, `stein_flux_representative_absolute_continuity` proves the full finite-interval epsilon–delta property directly. Its estimate even permits overlapping intervals, so it implies the usual definition with disjoint intervals. An arbitrary continuous representative of the flux equals the derived representative pointwise on the open positive ray.

Both endpoint limits are `C`. Either zero endpoint selects the canonical kernel, including when stated using an arbitrary continuous representative of the same flux. Integrability of the weighted family is equivalent to `C=0`; for an actual weak kernel, native integrability against the Gamma probability is equivalent to being the canonical kernel almost everywhere. Measurability plus native `HasFiniteIntegral` represents genuine finite Lebesgue expectation. The proof does not mistake the always-real totalized integral for an assertion of finite expectation. The exact centered identity `integral(tau*p)=2` also selects the canonical kernel; if that integrand were not integrable, the native totalized integral would instead be zero, which proves the needed integrability. The canonical integral equals two, and the existing Gamma mean and centered-second-moment theorems supply the variance computation.

Finally, almost-everywhere nonnegativity of the entire kernel family is equivalent to `C>=0`. It therefore does not select only the canonical kernel. The exact component map lists every declaration supporting these assertions.

## Scope boundary

These results close the two specified Stein labels. They do not complete the rest of the operator chapter: the operator essential-self-adjointness, Hilbert-domain and other previously recorded gaps remain explicitly partial in `operator-lean-map.json`.
