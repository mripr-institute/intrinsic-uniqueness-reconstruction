# Sigma: ten-field dependency ledger

This inventory covers the sixteen-branch manuscript, the original requested structures retained during consolidation, and the additional converse results verified in this audit. Related identities are grouped once. Read with **sigma-16-branch-audit.md** and **sigma-audit-proof-record.md**.

**≡** exact representation; **⇔** proved reconstruction; **⇒** consequence; **+H** conditional on explicitly supplied structure; **?** unresolved verification; **×** false proposed implication, refuted by the stated counterexample. Multiple symbols state both the conditional framework and the valid internal arrow. “Not kernel-formalized” does not mean unproved: the written proof and its independent review are separate evidence from machine checking.

Every entry has exactly the requested ten fields. The JSON companion contains the same inventory for graph or table reuse.

## R1

1. **ID:** R1
2. **Exact statement:** \(t=\mu r+a,\ a=\mu/\gamma\): \(( -1/\gamma,\infty)\leftrightarrow(0,\infty)\), and \(\sigma(r)-\sigma(r_*)=H(t)=\log t-t+1\).
3. **Status:** ≡
4. **Assumptions:** \(\mu>0,\gamma>\mu\); full domains and placement retained.
5. **Proof:** Substitute t into the original logarithm and subtract the value at t=1.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root direct substitution; original and updated manuscripts agree.
8. **Reverse reconstruction:** Yes, with μ,a and the original amplitude normalization.
9. **Removed input:** Separate intrinsic-vs-original law distinction removed.
10. **Remaining dependency:** Placement μ,a is lost if discarded.

## R2

1. **ID:** R2
2. **Exact statement:** \(I=-H,\ p=e^{H-1}=te^{-t},\ H=\log[p/p(1)],\ p(1)=e^{-1}\).
3. **Status:** ≡
4. **Assumptions:** Positive coordinate t and the stated normalization.
5. **Proof:** Algebra and ∫te^-t=1.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root direct verification.
8. **Reverse reconstruction:** Yes; exact invertible representations.
9. **Removed input:** No separate probability object is introduced.
10. **Remaining dependency:** Reference measure dt must be retained.

## R3

1. **ID:** R3
2. **Exact statement:** \(\rho(r)dr=p(t)dt/S(a)\), \(S(a)=(1+a)e^{-a}\); on \(r\ge0\) this is conditional normalization on \(t\ge a\).
3. **Status:** ≡
4. **Assumptions:** R1; original r≥0 normalization.
5. **Proof:** Jacobian dt=μdr and direct survival integral.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root direct verification.
8. **Reverse reconstruction:** Yes within placed Sigma family; restriction alone cannot recover an arbitrary omitted lower tail.
9. **Removed input:** Apparent distinction between two laws removed.
10. **Remaining dependency:** Retain cutoff and coordinate; no arbitrary-tail converse.

## R4

1. **ID:** R4
2. **Exact statement:** \(\mu=\sqrt{-\sigma''}-\sigma'\), \(\gamma=\sqrt{-\sigma''}/(1-r\sqrt{-\sigma''})\); normalization fixes amplitude \(\mu^2/(\mu+\gamma)\).
3. **Status:** ⇔
4. **Assumptions:** A known point and membership in the original Sigma family; admissible recovered parameters.
5. **Proof:** Use q=1/(r+1/γ) and integrate (1+γr)e^-μr.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root algebra audit passed.
8. **Reverse reconstruction:** Yes within the family.
9. **Removed input:** No independent amplitude remains.
10. **Remaining dependency:** Finite jet is not a characterization of arbitrary smooth functions.

## E0

1. **ID:** E0
2. **Exact statement:** \(H(t)=\log t-t+1\) for all \(t>0\).
3. **Status:** ⇔
4. **Assumptions:** R2 identifies I and p.
5. **Proof:** Definition and all reverse proofs in the main audit §3.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent core/converse review passed with the qualifications stated here.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** All equivalent presentations identify this same function.
10. **Remaining dependency:** Original placement is separate retained data.

## E1

1. **ID:** E1
2. **Exact statement:** \(H''=-t^{-2},\ H(1)=H'(1)=0\).
3. **Status:** ⇔
4. **Assumptions:** H twice differentiable on (0,∞).
5. **Proof:** Integrate twice; anchors remove affine terms.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent core/converse review passed with the qualifications stated here.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** No separate convexity needed.
10. **Remaining dependency:** Both affine anchors or equivalent identifying data.

## E2

1. **ID:** E2
2. **Exact statement:** \(H''=-(H'+1)^2,\ H(1)=H'(1)=0\); equivalently \(q(t+s)=q(t)/(1+sq(t)),q(1)=1\).
3. **Status:** ⇔
4. **Assumptions:** C² H; q=H'+1; flow only where t,t+s>0.
5. **Proof:** ODE uniqueness gives q=1/t; integrate.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent core/converse review passed with the qualifications stated here.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** Exact flow and Riccati equation are one node.
10. **Remaining dependency:** Flow domain and additive anchor.

## E3

1. **ID:** E3
2. **Exact statement:** \(H(av)-H(a)-aH'(a)(v-1)=H(v)\) for all a,v>0 and \(H''(1)=-1\).
3. **Status:** ⇔
4. **Assumptions:** C² H on the full positive half-line.
5. **Proof:** v=1 forces H1=0; differentiate once for H'1=0 and twice for a²H''(a)=-1.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent converse reviewer confirmed that no missing affine anchors exist.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** Both affine anchors follow from the recentering identity.
10. **Remaining dependency:** Curvature calibration -1 remains.

## E4

1. **ID:** E4
2. **Exact statement:** \(h(x\star y)=h(x)+h(y)-xy,\ h'(0)=0,\ x\star y=x+y+xy\).
3. **Status:** ⇔
4. **Assumptions:** Differentiable h on D=(-1,∞), identity for all x,y in D.
5. **Proof:** Differentiate in y at0; cocycle also forces h0=0.
6. **Formal-proof status:** Forward cocycle kernel-checked in SigmaAudit.lean; full converse written, not kernel-checked.
7. **Adversarial result:** Independent core/converse review passed with the qualifications stated here.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** Value anchor follows from cocycle.
10. **Remaining dependency:** Slope calibration; without it h=c log(1+x)-x.

## E5

1. **ID:** E5
2. **Exact statement:** If \(\ell=\mathrm{id}+h,\ h'(D)\subset D,\ \ell(h')=-\ell\), then \(h=h_K=K\log(1+z)-z-(K/2)\log K,\ K>0\). Either \(h(0)=0\) or \(h'(0)=0\) selects K=1.
3. **Status:** ⇔
4. **Assumptions:** Only differentiability and the typed domain condition, plus one anchor for Sigma.
5. **Proof:** Strict increase of ℓ yields inverse continuity, then differentiability, involution, and (1+z)(1+h')=K.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Two independent core reviews pass; p5 standalone normalization omission corrected.
8. **Reverse reconstruction:** Yes with either anchor; no without it.
9. **Removed input:** Independent injectivity, C², concavity and involution removed.
10. **Remaining dependency:** One scalar normalization is necessary.

## E6

1. **ID:** E6
2. **Exact statement:** Scale-invariant actual Bregman divergence \(B_\Phi(ct,cs)=B_\Phi(t,s)\), with \(\Phi(1)=\Phi'(1)=0,\Phi''(1)=1\), forces \(\Phi=I\).
3. **Status:** ⇔
4. **Assumptions:** C² candidate; all positive c,t,s.
5. **Proof:** Differentiate twice to force Φ''(t)=t^-2; integrate.
6. **Formal-proof status:** Exact forward Bregman expression is kernel-checked; converse written.
7. **Adversarial result:** Independent core/converse review passed with the qualifications stated here.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** Separate convexity unnecessary.
10. **Remaining dependency:** Affine and curvature calibration.

## E7

1. **ID:** E7
2. **Exact statement:** \((\partial_t+1)^2p=0,\ p(0)=0,\int p=1\); equivalently causal Green function of \((\partial+1)^2\).
3. **Status:** ⇔
4. **Assumptions:** Classical or distributional ODE; endpoint trace; causal support for full-line version.
5. **Proof:** General solution (A+Bt)e^-t; endpoint/mass fix A=0,B=1. Causal homogeneous difference is zero.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** ODE, Green and two-unit-exponential convolution merged.
10. **Remaining dependency:** Endpoint or causal condition cannot be dropped.

## E8

1. **ID:** E8
2. **Exact statement:** \((tp)'=(2-t)p\), or \(\int[tf'+(2-t)f]\,dP=0\) for every compactly supported smooth f.
3. **Status:** ⇔
4. **Assumptions:** Probability on (0,∞); weak solutions interpreted distributionally.
5. **Proof:** First-order equation forces density Cte^-t; normalization fixes C.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** Density smoothness can be derived from the weak equation on the open interval.
10. **Remaining dependency:** Probability normalization; p=0 otherwise also solves the equation.

## E9

1. **ID:** E9
2. **Exact statement:** \(\mathcal LP(s)=(1+s)^{-2}\) for every s≥0.
3. **Status:** ⇔
4. **Assumptions:** Probability on [0,∞).
5. **Proof:** Laplace-transform uniqueness.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Yes, smooth representative p.
9. **Removed input:** No independent Gamma label needed.
10. **Remaining dependency:** Entire determining transform, not finitely many values.

## E10

1. **ID:** E10
2. **Exact statement:** \(\mathbb ET^n=(n+1)!\) for every integer n≥0.
3. **Status:** ⇔
4. **Assumptions:** Nonnegative probability law with these moments.
5. **Proof:** Tonelli gives MGF (1-s)^-2 for 0≤s<1 and distributional uniqueness.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** No independent moment-determinacy assumption needed.
10. **Remaining dependency:** Complete sequence; finite moments do not identify general laws.

## E11

1. **ID:** E11
2. **Exact statement:** \(\mathbb ET^{i\xi}=\Gamma(2+i\xi)\) for all real ξ; full Mellin transform \(\Gamma(s+1)\), Re s>-1.
3. **Status:** ⇔
4. **Assumptions:** Probability on (0,∞).
5. **Proof:** Characteristic-function uniqueness for log T.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** Only one complete determining vertical line needed.
10. **Remaining dependency:** All real frequencies.

## E12

1. **ID:** E12
2. **Exact statement:** \(I^*(\theta)=-\log(1-\theta)\) for θ<1, +∞ otherwise.
3. **Status:** ⇔
4. **Assumptions:** Candidate I proper, lower-semicontinuous, convex, extended by +∞ on t≤0.
5. **Proof:** Legendre maximization and Fenchel–Moreau biconjugation.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent core/converse review passed with the qualifications stated here.
8. **Reverse reconstruction:** Yes in that class.
9. **Removed input:** No separate primal formula needed.
10. **Remaining dependency:** Closed convex function class; arbitrary functions with same envelope are not identified.

## E13

1. **ID:** E13
2. **Exact statement:** \(\lambda(x)=x/(1+x),\ S(0)=1,\ S'=-\lambda S\).
3. **Status:** ⇔
4. **Assumptions:** Positive survival, x≥0, normalized probability density.
5. **Proof:** Integrate λ to S=(1+x)e^-x, then p=-S'.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** Survival and hazard are not independent primitives.
10. **Remaining dependency:** Normalization and coordinate x.

## E14

1. **ID:** E14
2. **Exact statement:** Calibrated cross-ratio map \(H'\) with values \(0,-1/2,-2/3\) at \(1,2,3\), and H1=0.
3. **Status:** ⇔
4. **Assumptions:** Injective projective map on (0,∞); distinct cross-ratio inputs; no domain pole.
5. **Proof:** Three projective values force H'=1/t-1; integrate.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent core/converse review passed with the qualifications stated here.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** Cross-ratio and calibrated Möbius characterization merged.
10. **Remaining dependency:** Three-value and additive calibration; generic projectivity insufficient.

## E15

1. **ID:** E15
2. **Exact statement:** Normalized differentiable group logarithm \(\ell(x\star y)=\ell(x)+\ell(y),\ell'(0)=1\), with \(h=\ell-\mathrm{id}\).
3. **Status:** ⇔
4. **Assumptions:** Fixed coordinate law x★y=x+y+xy on D.
5. **Proof:** Differentiate at the identity to obtain ℓ'=1/(1+x).
6. **Formal-proof status:** Group laws and forward logarithm identity kernel-checked; converse written.
7. **Adversarial result:** Independent core/converse review passed with the qualifications stated here.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** Logarithm does not need separate functional specification.
10. **Remaining dependency:** Relation to the potential and derivative normalization.

## E16

1. **ID:** E16
2. **Exact statement:** Full Todd unit series \(Q_T=u/(1-e^{-u})\) with \(E=u/(Q_T-u)\), \(\ell=E^{-1},h=\ell-\mathrm{id}\).
3. **Status:** +H; ⇔
4. **Assumptions:** Rational formal series and specified Euler-coordinate conversion; analytic extension for global functions.
5. **Proof:** Invert the unit Q_T-u, then compositional inverse.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Yes as a normalized formal germ; global real identity with analytic formula.
9. **Removed input:** No independent exponential/logarithm once conversion retained.
10. **Remaining dependency:** A formal germ does not determine arbitrary nonanalytic global functions.

## E17

1. **ID:** E17
2. **Exact statement:** Actual symmetrized Bregman data \(B_\Phi(t,1)+B_\Phi(1,t)=t+t^{-1}-2\), \(\Phi(1)=\Phi'(1)=0\), force Φ=I.
3. **Status:** ⇔
4. **Assumptions:** Differentiable Φ on (0,∞); full identity.
5. **Proof:** Symmetrization gives (t-1)Φ'(t)=(t-1)²/t; then derivative uniqueness.
6. **Formal-proof status:** Symmetrization algebra and derivative reconstruction kernel-checked separately; full composed theorem not formalized.
7. **Adversarial result:** Two independent reviews pass; reciprocal-value-only counterexample found.
8. **Reverse reconstruction:** Yes; A-hat reconstructs through this declared Bregman map.
9. **Removed input:** C¹ regularity, independent convexity and unit curvature unnecessary.
10. **Remaining dependency:** Actual Bregman meaning and affine anchors.

## E18

1. **ID:** E18
2. **Exact statement:** Global \(Q_L=u/\tanh u\), marked projective map \(C(a)=(1+a)/(1-a)\), increasing affine \(A(a)=(1+a)/2\), and normalized survival reconstruct H.
3. **Status:** +H; ⇔
4. **Assumptions:** Global analytic series realization, labelled projective values, orientation and hazard construction.
5. **Proof:** t=C(tanh u)=e²ᵘ; A=t/(1+t); solve survival ODE.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Yes with these data.
9. **Removed input:** No extra probability-shape parameter after calibration.
10. **Remaining dependency:** Bare genus/germ or arbitrary continuous group isomorphism insufficient.

## E19

1. **ID:** E19
2. **Exact statement:** Labelled projective Calkin–Wilf pair \(L(x)=x/(1+x),R(x)=1+x\) reconstructs \(I(t)=\int_0^{t-1}L(s)ds\); conversely L=I'(1+x).
3. **Status:** +H; ⇔
4. **Assumptions:** Real affine coordinate, specified R, root/rational labels, primitive anchor; domain t>0.
5. **Proof:** Integrate x/(1+x); differentiate the result.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent arithmetic/discrete-projective review passed with typing and domain corrections.
8. **Reverse reconstruction:** Yes for that complete coordinate presentation.
9. **Removed input:** The analytic primitive is forced by labelled L,R.
10. **Remaining dependency:** An abstract binary tree or unlabelled rational enumeration is insufficient.

## E20

1. **ID:** E20
2. **Exact statement:** \(\int L_n^{(1)}\,dP=0\) for all n≥1, plus probability and finite moments, determines p.
3. **Status:** ⇔
4. **Assumptions:** Probability on [0,∞), finite all moments; fixed normalized Laguerre polynomials.
5. **Proof:** Triangular leading coefficients determine all moments; E10 identifies law.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator-converse addendum passes.
8. **Reverse reconstruction:** Yes.
9. **Removed input:** Full pairwise orthogonality and its norms are more data than necessary.
10. **Remaining dependency:** Complete sequence of means.

## C1

1. **ID:** C1
2. **Exact statement:** \(\sigma^{(n)}=(-1)^{n-1}(n-1)!q^n\), q=γ/(1+γr); normalized hierarchy is multiplicative/rank one.
3. **Status:** ⇒
4. **Assumptions:** R1; n≥2 and legitimate hierarchy indices.
5. **Proof:** Differentiate q'=-q² inductively.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root direct derivative audit.
8. **Reverse reconstruction:** Full calibrated curvature reverses; generic rank-one Hankel property does not.
9. **Removed input:** Duplicate derivative constraints grouped.
10. **Remaining dependency:** Calibration and differential compatibility for converse.

## C2

1. **ID:** C2
2. **Exact statement:** Zeros of \(\rho^{(n)}\) are \(r_n=n/\mu-1/\gamma\), n≥1; two indexed zeros recover μ,γ.
3. **Status:** ⇒
4. **Assumptions:** Placed Sigma family; known derivative orders.
5. **Proof:** Derivative of affine-times-exponential has one affine zero.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root direct algebra.
8. **Reverse reconstruction:** Yes within family and with indexed zeros.
9. **Removed input:** No independent zero-lattice parameter.
10. **Remaining dependency:** Family membership and indexing.

## C3

1. **ID:** C3
2. **Exact statement:** For V=I(T), \(M_V(s)=e^{-s}\Gamma(2-s)/(1-s)^{2-s}\), s<1; \(\kappa_1=\gamma_E,\ \kappa_n=(n-1)![\zeta(n)-1/(n-1)]\), n≥2.
3. **Status:** ⇒
4. **Assumptions:** T has density p.
5. **Proof:** Integrate t^{1-s}e^{-(1-s)t} and differentiate log MGF.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root exact derivation; previous symbolic/high-precision diagnostics support it.
8. **Reverse reconstruction:** Not unrestrictedly; deficit loses allocation between level branches.
9. **Removed input:** All moments from cumulants/Bell recurrence, not independent constants.
10. **Remaining dependency:** Law of a composed statistic does not identify the underlying function without structure.

## C4

1. **ID:** C4
2. **Exact statement:** For v>0, \(t_\pm=-W_{0,-1}(-e^{-1-v})\); \(f_V(v)=e^{-1-v}[t_-/(1-t_-)+t_+/(t_+-1)]\).
3. **Status:** ⇒
4. **Assumptions:** Canonical p and I; both real branches.
5. **Proof:** Change variables on each monotone branch using |dt/dv|=t/|t-1|.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root exact change-of-variable verification.
8. **Reverse reconstruction:** Full specified inverses reconstruct I; marginal deficit density alone does not.
9. **Removed input:** Branch contributions explicitly combined.
10. **Remaining dependency:** Branch labels and normalization.

## C5

1. **ID:** C5
2. **Exact statement:** The opposite Lambert branch of \(-W(-te^{-t})\) defines a decreasing analytic level-preserving involution j with j(1)=1.
3. **Status:** ⇒
4. **Assumptions:** Full positive domain; switch W branches at1.
5. **Proof:** Strict monotonicity on both sides; local signed square-root coordinate for I proves smooth crossing.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root branch audit; previous checks support it.
8. **Reverse reconstruction:** No: I+cI² for c>0 has the same level involution.
9. **Removed input:** No separate branch-switch rule after levels fixed.
10. **Remaining dependency:** Involution alone omits level scale.

## C6

1. **ID:** C6
2. **Exact statement:** \(S(x)=p(1+x)/p(1)\); among Erlang shapes m≥2, normalized positive-shift identity forces m=2 and shift1.
3. **Status:** ⇒
4. **Assumptions:** Unit rate; shift c>0; x≥0; named Erlang class.
5. **Proof:** Compare survival polynomial Σx^k/k! with (1+x/c)^{m-1}; linear/quadratic coefficients force m=2.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root exact polynomial proof.
8. **Reverse reconstruction:** Yes within the calibrated Erlang class; no arbitrary-density converse asserted.
9. **Removed input:** Erlang shape fixed within class.
10. **Remaining dependency:** Shape1 exception: every shift works; rateβ gives shift1/β.

## C7

1. **ID:** C7
2. **Exact statement:** \(v(u)=\lambda(e^u)=1/(1+e^{-u})\), \(v'=v(1-v),v(0)=1/2\).
3. **Status:** ⇔
4. **Assumptions:** v is composed probability hazard; whole real u-domain.
5. **Proof:** Logistic ODE and E13.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator and topology reviews pass.
8. **Reverse reconstruction:** Yes with the composed-hazard map.
9. **Removed input:** No independent logistic translation parameter after v0 fixed.
10. **Remaining dependency:** Hazard of log T is e^uλ(e^u), a different transformation.

## C8

1. **ID:** C8
2. **Exact statement:** \(B_I(t,s)=I(t/s)\), \(B_J(x,y)=J((x-y)/(1+y))\).
3. **Status:** ≡
4. **Assumptions:** Positive t,s; x,y>-1; actual gradients.
5. **Proof:** Direct subtraction using log quotient.
6. **Formal-proof status:** Kernel-checked in SigmaAudit.lean; independently rebuilt with standard foundational axioms only.
7. **Adversarial result:** Root and Lean independent review pass.
8. **Reverse reconstruction:** Yes from basepoint section with affine normalization.
9. **Removed input:** Group quotient and Bregman expression identify same two-point function.
10. **Remaining dependency:** Affine anchors if reconstructing a general potential.

## C9

1. **ID:** C9
2. **Exact statement:** Metric \(dt^2/t^2\), geodesic \(t_\tau=t_0^{1-\tau}t_1^\tau\), distance |log(t/s)|, symmetrized D=4sinh²(d/2).
3. **Status:** ⇒
4. **Assumptions:** Specified affine coordinate and Hessian construction.
5. **Proof:** Use u=log t and t/s+ s/t−2 identity.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root direct proof.
8. **Reverse reconstruction:** Metric plus affine anchors reconstructs I; abstract distance alone does not.
9. **Removed input:** Metric and geodesic coordinate are derived.
10. **Remaining dependency:** Affine coordinate and direction for a directed divergence.

## C10

1. **ID:** C10
2. **Exact statement:** \(\Lambda'=e^u-1=\exp_\star\), \((\Lambda^*)'=\log(1+z)=\log_\star\); \(J^*(s)=J(-s)\).
3. **Status:** ≡
4. **Assumptions:** Legendre domains: z>-1, s<1; include Λ*(-1)=1 and +∞ below -1.
5. **Proof:** Solve stationary dual equations.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root direct convex audit; boundary omission identified.
8. **Reverse reconstruction:** Full gradients plus constants reconstruct; reflected symmetry alone does not.
9. **Removed input:** Group exp/log and Legendre gradients are identical maps.
10. **Remaining dependency:** Domain boundary values and additive constants.

## C11

1. **ID:** C11
2. **Exact statement:** On r≥0, \((-\sigma''/\gamma)dr=-dU,\ U=(1+\gamma r)^{-1}\), so U is Uniform(0,1).
3. **Status:** ≡
4. **Assumptions:** Restricted original sector r≥0 and specified map.
5. **Proof:** Integrate derivative of U; total mass1.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root visual/domain audit found missing restriction on p12.
8. **Reverse reconstruction:** Yes with U,γ and affine derivative data; generic uniformizability does not.
9. **Removed input:** Curvature weight and uniformizing map mutually specified.
10. **Remaining dependency:** On full Sigma domain the measure is infinite, not probability.

## C12

1. **ID:** C12
2. **Exact statement:** Rate KL: \(\mathrm{KL}(\mathrm{Exp}(s)\Vert\mathrm{Exp}(t))=I(t/s)\); \(\mathrm{KL}(\mathrm{Pois}(s)\Vert\mathrm{Pois}(t))=sI(t/s)\); variance Gaussian KL=I(t/s)/2.
3. **Status:** ≡
4. **Assumptions:** s,t>0; parameter conventions explicitly rate/mean/variance respectively.
5. **Proof:** Integrate log density ratios.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator review found and repaired exponential basepoint error.
8. **Reverse reconstruction:** Full calibrated functions reconstruct I.
9. **Removed input:** No additional scalar information in these exact KL formulas.
10. **Remaining dependency:** Distributional realization and parameter order must be retained.

## C13

1. **ID:** C13
2. **Exact statement:** Original \(\mathcal L\rho(s)=\mu^2(s+\mu+\gamma)/[(\mu+\gamma)(s+\mu)^2]\); Mellin \(=\mu^{1-s}\Gamma(s)(a+s)/(a+1)\); \(M_n=n!(a+n+1)/[\mu^n(a+1)]\).
3. **Status:** ⇒
4. **Assumptions:** Original r≥0 normalization; Re s>−μ for Laplace and Re s>0 for Mellin.
5. **Proof:** Integrate constant and linear exponential terms.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root direct transform audit.
8. **Reverse reconstruction:** Full transforms reverse; finite data only within family.
9. **Removed input:** Transforms and moments grouped.
10. **Remaining dependency:** Original domain and placement.

## C14

1. **ID:** C14
2. **Exact statement:** \(\rho(r;\lambda\mu,\lambda\gamma)=\lambda\rho(\lambda r;\mu,\gamma)\), \(r_*\mapsto r_*/\lambda\).
3. **Status:** ⇒
4. **Assumptions:** λ>0 and admissible original parameters.
5. **Proof:** Substitute scaled parameters.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root algebra audit.
8. **Reverse reconstruction:** Not alone; many scale families satisfy covariance.
9. **Removed input:** No independent amplitude scale parameter.
10. **Remaining dependency:** Does not imply a spatial square-root scaling rule.

## O1

1. **ID:** O1
2. **Exact statement:** Centered Stein solutions are \(\tau=t+C/p\) a.e.; either zero flux or L¹(pdt) gives τ=t; positivity alone allows C≥0.
3. **Status:** ⇒
4. **Assumptions:** Locally integrable τp; distributional equation; AC representative for fluxes.
5. **Proof:** Difference has zero distributional derivative; integrability excludes nonzero constant.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** The specified centered equation identifies the kernel for p; generic invariant density does not select all diffusions.
9. **Removed input:** One flux suffices; L¹ makes both flux conditions redundant.
10. **Remaining dependency:** Normalized centered Stein construction.

## O2

1. **ID:** O2
2. **Exact statement:** For \(A_0=-p^{-1}(tpf')'\) on Cc∞, both endpoints are limit point and \(A=\overline A_0=A_0^*=A_{\max}\).
3. **Status:** ⇒
4. **Assumptions:** L²(pdt), specified differential expression and initial core.
5. **Proof:** Second zero-mode solution ~−1/t and ~e^t/t² is not L²; Weyl theorem.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Full coefficient structure can recover p; spectrum alone cannot.
9. **Removed input:** All self-adjoint boundary parameters removed.
10. **Remaining dependency:** Sturm–Liouville/Weyl theorem and selected expression.

## O3

1. **ID:** O3
2. **Exact statement:** D(A)={f∈L²:p-weighted expression in L², f and qf'∈ACloc}; form domain={f∈L²∩ACloc:∫q|f'|²<∞}, q=t²e^-t.
3. **Status:** ⇒
4. **Assumptions:** O2; derivatives and representatives interpreted locally.
5. **Proof:** Limit-point maximal domain; truncation/cutoff and interior smoothing prove form core.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Domain is a consequence of chosen realization.
9. **Removed input:** No extra boundary trace restriction; endpoint fluxes automatic.
10. **Remaining dependency:** Hilbert-space and differential realization.

## O4

1. **ID:** O4
2. **Exact statement:** e_n=L_n^(1)/sqrt(n+1) is a complete ONB, Ae_n=ne_n; spectral domains use Σn²|c_n|² and Σn|c_n|².
3. **Status:** ⇒
4. **Assumptions:** O2–O3; Rodrigues normalization.
5. **Proof:** Integration by parts for orthogonality; exponential-transform analyticity for completeness.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Complete calibrated Laguerre means already recover p via E20; spectrum alone does not.
9. **Removed input:** Completeness is proved, not an extra postulate.
10. **Remaining dependency:** Orthogonal-polynomial/analytic uniqueness foundations.

## O5

1. **ID:** O5
2. **Exact statement:** \((1+A)^{-2}=\int_0^\infty se^{-s}e^{-sA}ds\); trace=ζ(2), norm1, compact and injective.
3. **Status:** ⇒
4. **Assumptions:** O2–O4; strong operator integral.
5. **Proof:** Scalar Laplace integral and spectral theorem; sum (n+1)^-2.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Mixing measure reverses through O6; identity alone does not choose A.
9. **Removed input:** No external operator needed for intrinsic application.
10. **Remaining dependency:** Spectral calculus; arbitrary B requires supplying B.

## O6

1. **ID:** O6
2. **Exact statement:** For one fixed nonnegative self-adjoint A having every n≥0 as eigenvalue, \(\int e^{-sA}\nu(ds)=(1+A)^{-2}\) forces \(\nu(ds)=se^{-s}ds\).
3. **Status:** ⇔
4. **Assumptions:** Finite positive Borel ν on [0,∞); all integer modes observed.
5. **Proof:** Push ν by y=e^-s; eigenvalues specify all Hausdorff moments (n+1)^-2; polynomial density gives uniqueness.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator-converse addendum proved both directions and finite-spectrum counterexamples.
8. **Reverse reconstruction:** Yes, for the mixing measure with A fixed.
9. **Removed input:** No family of arbitrary test operators is needed; one determining infinite spectrum suffices.
10. **Remaining dependency:** A must be supplied; a finite spectrum does not identify ν.

## X1

1. **ID:** X1
2. **Exact statement:** Every probability convolution semigroup on [0,∞) with μ1=pdt is uniquely μr=Gamma(2r,1), μ0=δ0.
3. **Status:** +H; ⇔
4. **Assumptions:** Convolution semigroup indexed by every real r≥0; support and time calibration.
5. **Proof:** Nonnegative additive negative-log Laplace transform is linear; uniqueness and explicit existence.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Time1 restriction returns p; full completion unique in category.
9. **Removed input:** Weak continuity is derived.
10. **Remaining dependency:** The semigroup/process framework is not forced by a single marginal.

## X2

1. **ID:** X2
2. **Exact statement:** Lévy exponent 2log(1+λ), density \(2e^{-x}/x\), zero drift and killing.
3. **Status:** ⇒
4. **Assumptions:** X1; nonnegative subordinator convention.
5. **Proof:** Tonelli integral; λ→0 and growth at∞ fix killing/drift; differentiated Laplace uniqueness.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Exact Lévy data reconstruct p through its transform.
9. **Removed input:** Wrong shape1 coefficient corrected to2.
10. **Remaining dependency:** Generic infinite divisibility alone is not identifying.

## X3

1. **ID:** X3
2. **Exact statement:** Gamma subordination gives \(T_r=(1+A)^{-2r}\), positive generator \(2\log(1+A)\).
3. **Status:** ⇒
4. **Assumptions:** X1 and intrinsic A, or another explicitly supplied nonnegative SA operator.
5. **Proof:** Spectral calculus.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent operator blind review passed; measurable functions are identified a.e.
8. **Reverse reconstruction:** Full subordinate semigroup recovers A in its fixed realization by logarithmic calculus.
9. **Removed input:** No additional scalar subordination parameter.
10. **Remaining dependency:** Operator realization; usual infinitesimal generator has negative sign.

## X4

1. **ID:** X4
2. **Exact statement:** Haar dt/t is fixed by the scalar group up to scale; ∫pdt/t=1 fixes scale; −logt sends it to density exp(−x−e^-x).
3. **Status:** ≡; ⇒
4. **Assumptions:** Same kernel; multiplicative Haar construction and explicit coordinate.
5. **Proof:** Haar scaling law and change of variables.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent group/converse review passes.
8. **Reverse reconstruction:** Yes retaining measure weighting and inverse coordinate.
9. **Removed input:** No arbitrary Haar normalization remains.
10. **Remaining dependency:** Not the pushforward of pdt; changing reference measure is explicit.

## X5

1. **ID:** X5
2. **Exact statement:** For standard Z∈R⁴ Gaussian, T=||Z||²/2 has p; OU generator ½Δ−½z·∇ acts radially as tf''+(2−t)f'.
3. **Status:** +H; ≡
4. **Assumptions:** Supplied 4D Gaussian/angular structure and OU normalization.
5. **Proof:** Polar integration and chain rule ∇t=z, Δt=4.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root direct calculation; prior manuscript verification context.
8. **Reverse reconstruction:** Radial law plus independent uniform angle recovers Gaussian; radial law alone does not.
9. **Removed input:** Radial Laguerre coefficient and time factor are exact.
10. **Remaining dependency:** Dimension/angular law and process realization.

## X6

1. **ID:** X6
2. **Exact statement:** T(x)=−W0(−x)=Σn^(n−1)x^n/n!, T=xe^T; B(s)=T(s/e) is Borel PGF.
3. **Status:** ⇒; ⇔
4. **Assumptions:** Formal inverse at0 or local analytic inverse; probability radius handled at1/e.
5. **Proof:** Lagrange inversion, nonnegative coefficients and T(1/e)=1.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent group/converse review passes.
8. **Reverse reconstruction:** Full local inverse reconstructs p's analytic germ; B full germ reverses under scaling.
9. **Removed input:** Tree coefficients are fixed analytic consequences.
10. **Remaining dependency:** Naming rooted labelled trees uses their combinatorial realization.

## X7

1. **ID:** X7
2. **Exact statement:** If B is total progeny PGF of one-ancestor iid Galton–Watson, offspring PGF is uniquely exp(w−1).
3. **Status:** +H; ⇔
4. **Assumptions:** Actual Galton–Watson independence/identical-offspring framework.
5. **Proof:** B=sf(B); invert B locally to get f(w)=e^(w−1).
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent group/converse review passes.
8. **Reverse reconstruction:** Yes for offspring law within GW; not for arbitrary genealogies.
9. **Removed input:** No free offspring law remains inside GW.
10. **Remaining dependency:** Branching framework/joint law is added.

## X8

1. **ID:** X8
2. **Exact statement:** The scalar CGF Λ(u)=e^u−1−u uniquely identifies centered Poisson1; iid Gamma summation has Gamma(2n,1) and normalized sums converge to Gaussian.
3. **Status:** ⇒
4. **Assumptions:** CGF uniqueness; iid copies for sum/CLT.
5. **Proof:** MGF calculation and independence; finite variance CLT.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Root mathematical audit.
8. **Reverse reconstruction:** Full CGF reverses; Gaussian limit alone does not.
9. **Removed input:** Poisson parameter fixed.
10. **Remaining dependency:** Independence/process constructions; generic limit is nonidentifying.

## T1

1. **ID:** T1
2. **Exact statement:** In K⁰, xL=[L]−1 gives tensor F+, dual inverse, and integer n-series.
3. **Status:** +H; ≡
4. **Assumptions:** Actual complex line bundles and their Grothendieck ring.
5. **Proof:** Expand tensor product and invert unit [L].
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Exact line coordinate data recover scalar group with calibration; not whole K functor.
9. **Removed input:** No new scalar group law.
10. **Remaining dependency:** Spaces/bundles/K construction.

## T2

1. **ID:** T2
2. **Exact statement:** ψⁿ([L])=[L]^n and ψⁿ(xL)=[n]F(xL) on lines; not on arbitrary virtual classes.
3. **Status:** +H; ⇒
4. **Assumptions:** Exterior-power λ-ring construction; degreezero Adams convention.
5. **Proof:** Newton identities/splitting; CP² counterexample ψ²(2x)≠[2]F(2x).
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Line operations determine n-series; generic Adams machinery not recovered.
9. **Removed input:** Line tensor rule distinct from extra whole-functor operations.
10. **Remaining dependency:** λ-ring and Bott-degree conventions.

## T3

1. **ID:** T3
2. **Exact statement:** ch(V)=Σe^{u_i}; ch(xL)=e^u−1 and ch(log(1+xL))=u.
3. **Status:** +H; ≡
4. **Assumptions:** Ordinary Chern classes, rational coefficients, splitting and finite-degree/completed setting.
5. **Proof:** Symmetric polynomials descend; splitting verifies ring laws.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Line series reverses scalar logarithm; not integral torsion.
9. **Removed input:** Character line formula is derived after foundations.
10. **Remaining dependency:** Cohomology/Chern classes; rational ch-isomorphism needs Bott/cellular machinery.

## T4

1. **ID:** T4
2. **Exact statement:** zK=eK(L)=1−[L]^-1=xL/(1+xL); ch(zK)=1−e^-u; its coordinate law is z+w−zw.
3. **Status:** +H; ≡
4. **Assumptions:** K and cohomology expressions kept in their own rings.
5. **Proof:** Koszul zero-section restriction and algebra.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Exact Euler coordinate reconstructs J' and calibrated J.
9. **Removed input:** Euler and derivative are exact corresponding coordinates.
10. **Remaining dependency:** Do not omit ch or confuse plus/minus coordinate laws.

## T5

1. **ID:** T5
2. **Exact statement:** Koszul complex (π*Λ*V*,ιv) defines multiplicative relative K-Thom class; Bott and gluing give Thom isomorphism.
3. **Status:** +H; ⇒
4. **Assumptions:** Relative K-theory by complexes, complex bundles, Bott normalization and exactness.
5. **Proof:** Complex is contractible away from zero; fibre Bott class; finite-base gluing.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** No unrestricted scalar-to-Thom converse.
9. **Removed input:** Thom class is actually constructed, not postulated from Euler values.
10. **Remaining dependency:** Relative theory, Bott and local-to-global foundations.

## T6

1. **ID:** T6
2. **Exact statement:** ch(UK(V))=π*Td(V)^-1 UH(V) as a relative cohomology class.
3. **Status:** +H; ⇒
4. **Assumptions:** T5, ordinary Thom freeness, universal-line classification and injective splitting.
5. **Proof:** Universal compatible finite stages allow u-cancellation in Q[[u]], then pull back and split.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Its line coefficient returns QT; not whole topology.
9. **Removed input:** Thom correction factor is derived from universal line conversion.
10. **Remaining dependency:** Ordinary Thom/splitting foundations; finite-base Euler cancellation invalid.

## T7

1. **ID:** T7
2. **Exact statement:** Universal computation uses lim_N Q[u]/u^(N+1)=Q[[u]], not Z[[x]]⊗Q=Q[[x]].
3. **Status:** ⇒
4. **Assumptions:** Infinite-base degree completion distinguished from finite-base rationalization.
5. **Proof:** Common-denominator obstruction; use compatible finite stages.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Not a scalar characterization.
9. **Removed input:** No illicit tensor/inverse-limit interchange.
10. **Remaining dependency:** Specify completion when using universal series.

## T8

1. **ID:** T8
2. **Exact statement:** Embedding Gysin maps from tubular collapse obey ch(i!E)=i*(chE Td(N)^-1); projection formula follows from module property.
3. **Status:** +H; ⇒
4. **Assumptions:** Actual embedding, complex normal orientation, Thom construction and ordinary pushforward.
5. **Proof:** Apply natural ch to collapse; multiply Thom class.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Returns correction series for universal tests; not geometry from scalar.
9. **Removed input:** Gysin comparison and projection formula are derived after construction.
10. **Remaining dependency:** Embedding/tubular and orientation inputs.

## T9

1. **ID:** T9
2. **Exact statement:** For compact stably complex X, topological p!K(E)=∫Xch(E)Td(TX); general proper oriented RR follows by graph embedding.
3. **Status:** +H; ⇒
4. **Assumptions:** Stable complex tangent, embedding/collapse, Bott identification and fundamental class.
5. **Proof:** Normal/tangent virtual relation and T6–T8.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Not an unrestricted scalar reconstruction theorem.
9. **Removed input:** Topological RR is derived without analytic index theorem.
10. **Remaining dependency:** Differential-topological and cohomological foundations.

## T10

1. **ID:** T10
2. **Exact statement:** Topological index=analytic Dirac index and, in complex setting, holomorphic Euler characteristic requires the relevant analytic/HRR bridge; h0=χ needs vanishing.
3. **Status:** +H
4. **Assumptions:** Elliptic operators, compatible orientations/complex structures, analytic index/cohomology theorem.
5. **Proof:** These are separate theorem statements; topological integer alone is not their definition.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** No; scalar series do not supply operators/cohomology.
9. **Removed input:** No automatic conflation of topological index, χ and h0.
10. **Remaining dependency:** Index theorem or holomorphic theorem and, when used, vanishing.

## T11

1. **ID:** T11
2. **Exact statement:** For all n≥0 and all integer k, [uⁿ]e^{ku}QT(u)^{n+1}=binom(k+n,n).
3. **Status:** ⇒
4. **Assumptions:** Formal rational series, generalized polynomial binomial.
5. **Proof:** Residue substitution z=1−e^-u gives [zⁿ](1−z)^(-k−1).
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Full universal series data can reconstruct; one coefficient does not.
9. **Removed input:** No HRR assumption needed for coefficient identity.
10. **Remaining dependency:** Topological interpretation needs CP tangent/orientation; h0 ranges separate.

## T12

1. **ID:** T12
2. **Exact statement:** QA=(u/2)/sinh(u/2), QT=e^{u/2}QA; QA(0)=1 selects even unit branch.
3. **Status:** ≡; ⇒
4. **Assumptions:** Analytic/formal series; signed denominator at0.
5. **Proof:** Algebra from symmetric divergence.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology and core reviews pass.
8. **Reverse reconstruction:** Yes via E17 Bregman framework; not via reciprocal values alone.
9. **Removed input:** No principal-square-root sign ambiguity after branch fixed.
10. **Remaining dependency:** Spin/Dirac orientation not reconstructed.

## T13

1. **ID:** T13
2. **Exact statement:** QL=u/tanh u gives L[CP^{2m}]=1; with rational oriented-bordism generators and genus/signature homomorphisms, L=signature.
3. **Status:** +H; ⇒
4. **Assumptions:** Pontryagin/fundamental classes, bordism invariance, multiplicativity and ΩSO⊗Q=Q[CP²,CP⁴,…].
5. **Proof:** Residue z=tanh u yields coefficient1; compare on generators.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Scalar QL reconstructs via E18; signature theorem alone needs entire framework.
9. **Removed input:** No analytic Atiyah–Singer step needed for this conditional proof.
10. **Remaining dependency:** Bordism and intersection-form foundations.

## T14

1. **ID:** T14
2. **Exact statement:** E=KU⊕Σ(KU/p) has same degreezero universal line data/rationalization but E⁰(S¹)=Z⊕Z/p.
3. **Status:** ×
4. **Assumptions:** Trivial square-zero extension as ring spectrum by KU-module; E is two-periodic, not even-periodic.
5. **Proof:** Compute coefficients, finite projective test spaces and S¹.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent topology blind review passed within the stated foundations.
8. **Reverse reconstruction:** Refutes unrestricted scalar-line-data ⇒ unique full cohomology theory.
9. **Removed input:** No claim of an unexplained universal topological primitive reduction.
10. **Remaining dependency:** Does not refute uniqueness under stronger specified even-periodic/full-coefficient hypotheses.

## M1

1. **ID:** M1
2. **Exact statement:** Rank-one I + orthogonal invariance + block additivity uniquely force Φn(X)=trX−logdetX−n.
3. **Status:** +H; ⇔
4. **Assumptions:** Family on all finite SPD ranks; positive spectrum.
5. **Proof:** Diagonalize and split into scalar blocks.
6. **Formal-proof status:** Only finite/list scalar assembly kernel-checked; full SPD theorem written.
7. **Adversarial result:** Independent matrix review passes; root gives counterexamples dropping either property.
8. **Reverse reconstruction:** Yes by rank1 restriction; conditional unique lift.
9. **Removed input:** Continuity, differentiability and convexity not needed for uniqueness; scalar block recursion suffices.
10. **Remaining dependency:** SPD category, spectral invariance and additive assembly.

## M2

1. **ID:** M2
2. **Exact statement:** ∇Φ=Id−X^-1; gX(U,V)=tr(X^-1UX^-1V); BΦ(X,Y)=tr(Y^-1X)−logdet(Y^-1X)−n.
3. **Status:** ⇒
4. **Assumptions:** SPD tangent space symmetric matrices; Frobenius pairing.
5. **Proof:** Differentiate inverse/logdet and simplify.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent matrix review passes.
8. **Reverse reconstruction:** Full anchored Bregman potential reverses; metric alone has affine ambiguity.
9. **Removed input:** Matrix differential quantities follow from unique lift.
10. **Remaining dependency:** No full commutative product group on noncommuting SPD matrices.

## M3

1. **ID:** M3
2. **Exact statement:** Covariance Gaussian KL=D(X,Y)/2; precision Gaussian KL=D(Y,X)/2.
3. **Status:** ≡
4. **Assumptions:** Centered nonsingular Gaussians; covariance versus precision convention.
5. **Proof:** Expectation of log density ratio with E[xxᵀ]=covariance.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent matrix review passes.
8. **Reverse reconstruction:** Full family identifies divergence; Gaussian realization is supplied.
9. **Removed input:** Order/factor ambiguity eliminated.
10. **Remaining dependency:** Gaussian measure construction not forced by scalar p.

## A1

1. **ID:** A1
2. **Exact statement:** Δgσ(n)=log(1+γg/(1+γn))−μg; discrete curvature log(1−γ²/(1+γn)²); multiplicative correction σ(ab)−σ(a)−σ(b) as displayed.
3. **Status:** ⇒
4. **Assumptions:** Nonnegative integer nodes, n≥1 for curvature, valid source parameters.
5. **Proof:** Substitute and cancel logs/linear terms.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent arithmetic/discrete-projective review passed with typing and domain corrections.
8. **Reverse reconstruction:** Within family enough labelled data may recover parameters; these properties alone not general characterization.
9. **Removed input:** Discrete identities are exact restrictions.
10. **Remaining dependency:** Integer sampling/product are specified.

## A2

1. **ID:** A2
2. **Exact statement:** For nonzero algebraic μ and algebraic γ in admissible locus, σ is injective on nonnegative integers.
3. **Status:** +H; ⇒
4. **Assumptions:** Integer inputs; positive algebraic parameters.
5. **Proof:** Equality gives e^{μ(m−n)} algebraic; Hermite–Lindemann excludes m≠n.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent arithmetic/discrete-projective review passed with typing and domain corrections.
8. **Reverse reconstruction:** Not from injectivity alone.
9. **Removed input:** Algebraicity is sufficient, not necessary; monotone-sector injection is alternative.
10. **Remaining dependency:** Transcendence theorem if using algebraic route; no source kernel rerun.

## A3

1. **ID:** A3
2. **Exact statement:** For injective e(n)=σ(n) on n≥2, e(a)⊙e(b)=e(ab) gives Irr(Sσ,⊙)=e(P).
3. **Status:** +H; ≡
4. **Assumptions:** a,b,k are integers≥2; Sσ=image; injective coding.
5. **Proof:** Transport equality through injection; prime iff no two factors≥2.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent arithmetic/discrete-projective review passed with typing and domain corrections.
8. **Reverse reconstruction:** No H reconstruction from unlabelled prime predicate.
9. **Removed input:** No separate prime predicate after integer multiplication and injection fixed.
10. **Remaining dependency:** Integer multiplicative structure and injection; Mσ on Z was not internally typed.

## A4

1. **ID:** A4
2. **Exact statement:** Without injection, γ=1, μ=log(5/4) gives σ(3)=σ(4), so prime label3 is decomposable through2·2.
3. **Status:** ×
4. **Assumptions:** Admissible real parameters, absent algebraic/injection restriction.
5. **Proof:** Direct equality 4e^-3μ=5e^-4μ.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent arithmetic/discrete-projective review passed with typing and domain corrections.
8. **Reverse reconstruction:** Counterexample to unconditional prime-label conclusion.
9. **Removed input:** Establishes exact necessity of retained identifying scope.
10. **Remaining dependency:** Repair by sufficient injection condition.

## A5

1. **ID:** A5
2. **Exact statement:** Calkin–Wilf reduced positive rationals have unique parent/word; Farey right inverse 1/t−1 equals H'(t).
3. **Status:** +H; ⇒
4. **Assumptions:** Integer reduced pairs, root1, labelled L/R; consistent branch endpoints.
5. **Proof:** Euclidean subtraction decreases a+b; explicit projective inverse.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent arithmetic/discrete-projective review passed with typing and domain corrections.
8. **Reverse reconstruction:** Analytic generator pair reverses via E19; bare tree does not.
9. **Removed input:** No independent analytic primitive once generator data fixed.
10. **Remaining dependency:** Correct closed/half-open domain conventions.

## G1

1. **ID:** G1
2. **Exact statement:** Nonnegative orthogonally additive r on supplied Euclidean space dim≥2 is exactly c||x||², c≥0.
3. **Status:** +H; ⇔
4. **Assumptions:** Supplied real inner product; all orthogonal pairs; global nonnegativity.
5. **Proof:** Even part radial/additive/monotone; odd dyadic scaling plus quadratic bound kills it.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent spatial and geometry reviews passed within the stated hypotheses.
8. **Reverse reconstruction:** Characterizes squared-norm observable under these premises; not H.
9. **Removed input:** Continuity, rotation, evenness and r0=0 assumptions removed.
10. **Remaining dependency:** Inner product, additivity, and calibration/nontriviality remain.

## G2

1. **ID:** G2
2. **Exact statement:** Global lower-bounded orthogonally additive r=c||x||²+ell(x), c≥0, ell real-linear; c=0 forces ell=0.
3. **Status:** +H; ⇔
4. **Assumptions:** Dimension≥2; full vector domain; finite lower bound.
5. **Proof:** Even part regularizes to radial quadratic; odd additive part bounded on balls becomes real-linear.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent spatial and geometry reviews passed within the stated hypotheses.
8. **Reverse reconstruction:** No scalar reconstruction; identifies possible spatial observables.
9. **Removed input:** Continuity follows, but evenness does not.
10. **Remaining dependency:** Nonnegative/minimum-at0 condition needed to kill ell.

## G3

1. **ID:** G3
2. **Exact statement:** Scalar H/F/Bregman/Hessian does not force spatial orthogonal additivity or dimension; r=||x||⁴ is a countermodel pullback.
3. **Status:** ×
4. **Assumptions:** Unqualified scalar-to-spatial implication.
5. **Proof:** For orthonormal x,y: r(x+y)=4≠2; all pointwise scalar formulas still hold.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Two independent geometry routes agree.
8. **Reverse reconstruction:** Negative result: claimed implication fails.
9. **Removed input:** This unqualified question is resolved by counterexample.
10. **Remaining dependency:** A separately justified bridge to spatial composition.

## G4

1. **ID:** G4
2. **Exact statement:** Orthogonal ★-homomorphism z≥0 implies z=exp(c||x||²)−1; scalar metric pullback has rank≤1.
3. **Status:** +H; ⇒
4. **Assumptions:** Supplied Euclidean structure; log(1+z) composition; differentiable observable for metric pullback.
5. **Proof:** Take group logarithm then G1; metric is rank-one outer product.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent group and spatial reviews pass.
8. **Reverse reconstruction:** Does not identify z with squared radius.
9. **Removed input:** Distinguishes additive coordinate from group displacement.
10. **Remaining dependency:** Choosing which coordinate is spatially additive is substantive.

## G5

1. **ID:** G5
2. **Exact statement:** Positivity + parallelogram alone does not force real homogeneity; q(x)=A(x)² for a non-real-linear additive Hamel bijection is a counterexample.
3. **Status:** ×
4. **Assumptions:** No norm homogeneity/continuity supplied.
5. **Proof:** Choose A fixing1 and sending sqrt2 to2sqrt2; q satisfies parallelogram but q(sqrt2)=8≠2q1.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent minimal-hypothesis adversary found and corrected an earlier review error.
8. **Reverse reconstruction:** No norm reconstruction without further data.
9. **Removed input:** Prevents false removal of homogeneity.
10. **Remaining dependency:** Genuine norm or suitable additional regularity/homogeneity.

## G6

1. **ID:** G6
2. **Exact statement:** Radial conjugation residual =(D−1)(D−3)/(4x²); vanishes iff D=1 or3, hence3 if D≥2.
3. **Status:** +H; ⇔
4. **Assumptions:** Supplied radial operator, x>0, chosen residual-cancellation condition; nonzero f for quotient form.
5. **Proof:** Product differentiation; independent of profile.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent spatial and geometry reviews passed within the stated hypotheses.
8. **Reverse reconstruction:** Characterizes residual cancellation, not H or space from scalar data.
9. **Removed input:** No Sigma-specific differential equation needed for this identity.
10. **Remaining dependency:** Cancellation and D≥2 are additional; origin operator domains remain separate.

## G7

1. **ID:** G7
2. **Exact statement:** For Σ(x)=σ(||x||²), Hessian=2σ'Id+4σ''xxᵀ; closure preimage sphere has zero tangential and −4μ²r* radial Hessian eigenvalue.
3. **Status:** +H; ⇒
4. **Assumptions:** Calibrated squared radius, supplied Euclidean dimension, r*>0.
5. **Proof:** Chain rule and σ'(r*)=0.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Independent spatial review passes.
8. **Reverse reconstruction:** No unique dimension; every supplied D has its closure sphere.
9. **Removed input:** Geometry of the chosen pullback is fully determined.
10. **Remaining dependency:** Squared-radius/Euclidean choice; origin is also stationary and has positive Hessian.

## V1

1. **ID:** V1
2. **Exact statement:** New Lean scalar group/log/cocycle/Bregman identities plus actual potential derivative and uniqueness from normalized derivative were compiled and independently rebuilt.
3. **Status:** ⇒
4. **Assumptions:** Lean4.14/mathlib4.14 and standard logical foundations.
5. **Proof:** Executable source and #print axioms audit.
6. **Formal-proof status:** Kernel-checked; exact theorem inventory in outputs/lean/README.md.
7. **Adversarial result:** Independent reviewer rebuilt twice including calculus addendum.
8. **Reverse reconstruction:** Formal reconstruction covers derivative premise only, not full P or full symmetric-Bregman theorem.
9. **Removed input:** No unproved custom axioms or admitted facts in this subset.
10. **Remaining dependency:** Operator/topology/transcendence/SPD formalization not included.

## V2

1. **ID:** V2
2. **Exact statement:** Supplied blind/unblinded audits and previous 59 symbolic/numerical diagnostics are supporting evidence, not proofs of every new converse.
3. **Status:** ⇒
4. **Assumptions:** Saved reports and prior check ledger; no implied fresh execution.
5. **Proof:** Custody records and explicit separation of diagnostics from proof.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** Matching audit counts not added as independent runs; phase2 zero convention flagged.
8. **Reverse reconstruction:** No.
9. **Removed input:** False precision about independent runs removed.
10. **Remaining dependency:** Original harness/kernel sources needed for executable rerun.

## V3

1. **ID:** V3
2. **Exact statement:** New PDF reports prior prime Lean/Coq custody; those formal source files were not supplied with this PDF and were not kernel-rechecked here.
3. **Status:** ?
4. **Assumptions:** Provenance statement on p33.
5. **Proof:** Inspect supplied artifacts and distinguish claim from executable evidence.
6. **Formal-proof status:** Written exact proof; not kernel-formalized in this delivery.
7. **Adversarial result:** No adverse verdict on unavailable proof sources.
8. **Reverse reconstruction:** Not applicable.
9. **Removed input:** No inferred formal certification from a PDF statement.
10. **Remaining dependency:** Provide actual source/build environment if a custody rerun is desired.


