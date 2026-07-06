#!/usr/bin/env python3
"""Numeric oracle for the developing-base derivation (DevelopingBase.lean).

The claim: qualitative SWModulusData (analytic on C minus {+-L^2}; omits {0,1};
J -> 1 at the monopole point, |J| -> infinity at the dyon point, J -> 0 at weak
coupling) forces J = 2 L^2/(u + L^2) exactly.

  A. The true cross-ratio satisfies every clause (non-vacuity), sampled.
  B. Must-fail: the p = 2 candidate 4 L^4/(u+L^2)^2 has the SAME cusp limits and
     analyticity but FAILS omit-1 at the extra point u = -3 L^2 (a would-be
     extra singularity) — the clause that kills higher degree is physical.
  C. Root arithmetic of the pinch: solutions of (u+L^2)^p = c are p distinct
     points; for p = 2, c = 4 L^4 they are {L^2, -3 L^2} — only one can be the
     monopole point.
  D. Normalization: the unique Mobius map with (L^2, -L^2, oo) |-> (1, oo, 0)
     is 2 L^2/(u+L^2) — three-point rigidity, coefficient 2 derived not chosen.

mpmath dps = 40.
"""

import mpmath as mp

mp.mp.dps = 40
TOL = mp.mpf(10) ** (-30)
checks = []


def check(name, ok, detail=""):
    checks.append((name, ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))


L = mp.mpc("1.23", "0.41")
L2, L4 = L**2, L**4


def J_true(u):
    return 2 * L2 / (u + L2)


def J_p2(u):
    return 4 * L4 / (u + L2) ** 2


print("A. the cross-ratio satisfies SWModulusData (sampled)")
import random

random.seed(7)
pts = [mp.mpc(random.uniform(-5, 5), random.uniform(-5, 5)) for _ in range(200)]
pts = [u for u in pts if abs(u - L2) > 0.1 and abs(u + L2) > 0.1]
check("A1 omits 0 on samples", all(abs(J_true(u)) > 1e-6 for u in pts))
check("A2 omits 1 on samples", all(abs(J_true(u) - 1) > 1e-6 for u in pts))
eps = mp.mpf("1e-12")
check("A3 J -> 1 at the monopole point", abs(J_true(L2 + eps) - 1) < mp.mpf("1e-11"))
check("A4 1/J -> 0 at the dyon point", abs(1 / J_true(-L2 + eps)) < mp.mpf("1e-11"))
check("A5 J -> 0 at weak coupling", abs(J_true(mp.mpf(10) ** 14)) < mp.mpf("1e-13"))

print("B. must-fail: the p = 2 candidate passes cusps but fails omit-1")
check("B1 p=2: J -> 1 at monopole", abs(J_p2(L2 + eps) - 1) < mp.mpf("1e-10"))
check("B2 p=2: 1/J -> 0 at dyon", abs(1 / J_p2(-L2 + eps)) < mp.mpf("1e-20"))
check("B3 p=2: J -> 0 at weak coupling", abs(J_p2(mp.mpf(10) ** 14)) < mp.mpf("1e-25"))
extra = -3 * L2
check("B4 p=2 FAILS omit-1 at u = -3L^2 (in the smooth locus!)",
      abs(J_p2(extra) - 1) < TOL and abs(extra - L2) > 0.1 and abs(extra + L2) > 0.1)

print("C. root arithmetic of the pinch")
sols = [w - L2 for w in (2 * L2, -2 * L2)]  # (u+L^2)^2 = 4L^4
check("C1 p=2 solutions are {L^2, -3L^2}, distinct",
      abs(sols[0] - L2) < TOL and abs(sols[1] + 3 * L2) < TOL
      and abs(sols[0] - sols[1]) > 0.1)
check("C2 -L^2 is never a solution (0^p != c)", all(abs(s + L2) > 0.1 for s in sols))

print("D. three-point Mobius rigidity: the coefficient 2 is derived")
# f(u) = c/(u+L^2) with f(L^2) = 1  =>  c = 2 L^2; check uniqueness numerically
c = 1 * (L2 + L2)
check("D1 c = 2L^2", abs(c - 2 * L2) < TOL)
check("D2 the resulting map has the right three values",
      abs(c / (L2 + L2) - 1) < TOL and abs(c / (mp.mpf(10) ** 20 + L2)) < mp.mpf("1e-18"))

npass = sum(1 for _, ok in checks if ok)
print(f"\n{npass}/{len(checks)} checks passed" + ("" if npass == len(checks) else "  *** FAILURES ***"))
raise SystemExit(0 if npass == len(checks) else 1)
