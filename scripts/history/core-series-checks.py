"""Finite exact diagnostics; universal proofs are in core-series.md."""

import json
from pathlib import Path

AUDIT_DIR = Path(__file__).resolve().parents[2] / "audits/history/reconstruction"

import sympy as s

u, t, k = s.symbols("u t k")
Q = s.series(u / (1 - s.exp(-u)), u, 0, 8).removeO()
A = s.series((u / 2) / s.sinh(u / 2), u, 0, 8).removeO()
L = s.series(u / s.tanh(u), u, 0, 8).removeO()
checks = []
for n in range(7):
    actual = s.series(s.exp(k * u) * Q ** (n + 1), u, 0, n + 1).removeO().coeff(u, n)
    expected = s.prod(k + j for j in range(1, n + 1)) / s.factorial(n)
    checks.append({"id": f"CS07.twist.n{n}", "passed": s.simplify(actual - expected) == 0})
checks.append({"id": "CS08.TA.through7", "passed": s.series(Q - s.exp(u / 2) * A, u, 0, 8).removeO() == 0})
checks.append({"id": "CS08.TL.through7", "passed": s.expand(L - Q.subs(u, 2 * u) + u) == 0})
f = 4 * t / (t + 2) ** 3
checks.append({"id": "CS14.f2.exact_mass", "passed": s.integrate(f, (t, 0, s.oo)) == 1})
for n in range(1, 13):
    expected = (-1) ** (n - 1) * 8 * s.rf(3, n - 1) * (n - t) / (t + 2) ** (n + 3)
    checks.append({"id": f"CS14.f2.derivative.n{n}", "passed": s.cancel(s.diff(f, t, n) - expected) == 0})
result = {
    "scope": "Finite exact symbolic diagnostics, not universal uniqueness proofs",
    "todd_coefficients_0_through_7": [str(Q.coeff(u, n)) for n in range(8)],
    "count": len(checks),
    "all_passed": all(check["passed"] for check in checks),
    "checks": checks,
}
expected = json.loads((AUDIT_DIR / "core-series-checks.json").read_text())
if result != expected:
    raise SystemExit("Symbolic results differ from the preserved diagnostic record.")
print(json.dumps({"count": result["count"], "all_passed": result["all_passed"]}))
if not result["all_passed"]:
    raise SystemExit(1)
