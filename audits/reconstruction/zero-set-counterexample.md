# Exact derivative-zero sets: the probability converse is refuted

**Z4 — status ×; analytic/probabilistic.** On the marked domain \(t>0\), the complete exact zero sets \(Z_n=\{n\}\), \(n\ge1\), do not characterize \(p(t)=te^{-t}\) among smooth positive probability densities. The conclusion still fails when the candidates are required to be real analytic, to vanish at both endpoints, and to have a unique mode at one.

For any real \(k>1\), define
\[
 f_k(t)=(k-1)k^k\frac{t}{(t+k)^{k+1}}.
\]
This function is positive and real analytic on \((0,\infty)\), vanishes at zero and infinity, and has integral one. Indeed, substitution \(t=ks\) gives
\[
 \int_0^\infty\frac{t\,dt}{(t+k)^{k+1}}
 =k^{1-k}\int_0^\infty\frac{s\,ds}{(1+s)^{k+1}}
 =\frac{k^{-k}}{k-1}.
\]
The last integral follows by writing \(s=(1+s)-1\) and integrating the two powers; no distributional identification is needed.

Put \(C_k=(k-1)k^k\) and \((k)_n=k(k+1)\cdots(k+n-1)\). For every integer \(n\ge1\),
\[
 f_k^{(n)}(t)=C_k(-1)^n(k)_n\frac{t-n}{(t+k)^{k+n+1}}. \tag{Z4.1}
\]
For \(n=1\), direct differentiation gives \(C_k k(1-t)/(t+k)^{k+2}\). Differentiating the right side of (Z4.1) uses the identity
\[
 \frac{d}{dt}\frac{t-n}{(t+k)^{k+n+1}}
 =-(k+n)\frac{t-(n+1)}{(t+k)^{k+n+2}},
\]
which proves the formula by induction. Its prefactor never vanishes and its denominator is strictly positive. Thus every derivative has exactly one zero, at \(t=n\), and that zero is simple. These are exactly the zero sets of \(p^{(n)}\).

The elementary representative
\[
 \boxed{f_2(t)=\frac{4t}{(t+2)^3}}
\]
already suffices. It differs from \(p\), for example by its algebraic tail. Consequently this is a counterexample to **exact sets**, not just zero incidences. It also preserves their strict interlacing and the derivative signs between the zeros.

For the placed coordinate \(t=\mu r+a\), \(\mu>0,0<a<1\), the full-half-line probability density \(\mu f_k(\mu r+a)\) on \(r>-a/\mu\) has zeros \(r_n=(n-a)/\mu\). If probability normalization is instead on \(r\ge0\), divide by the positive survival mass \(\int_a^\infty f_k(t)dt\). This scalar factor leaves all derivative zeros unchanged and gives the same placed zero lattice as Sigma on that domain. The distinction matters: placed \(e^{\sigma_P}\) has mass one on \([0,\infty)\), whereas its integral on its entire analytic domain is \(e^a/(1+a)\).

The counterexample does not satisfy global log-concavity: \((\log f_k)''=-t^{-2}+(k+1)/(t+k)^2\) becomes positive when \(t>1+\sqrt{k+1}\). It is not entire, owing to its singularity at \(-k\). Thus (Z4.1) refutes the stated smooth and real-analytic probability converses; it makes no claim about additional entire or globally log-concave candidate restrictions. Those restrictions are unnecessary to settle the question that Phase III left open and are not new nodes in the frozen graph.

The root derived the example directly. Two statement-only independent checks verified its normalization and all-order induction, recorded in the core/series and probability audits. Finite symbolic differentiation is retained only as a diagnostic, not the proof of (Z4.1). This theorem is not claimed to be Lean-formalized.
