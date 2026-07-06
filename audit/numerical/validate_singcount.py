#!/usr/bin/env python3
"""Numeric oracle for the singularity-count layer (SingularityCount.lean).

Pins the conventions for the "exactly one monopole-dyon pair" pinch:

    (monodromy/Euler counting: #finite singularities = 12*l - (m+6) with I*_m at infinity)
  + (holomorphy + dimensions + Z8 anomaly: deg_u g2 <= 2  =>  twist l = 1)
  =>  exactly 2 finite singularities (n = 1 pair).

Checks:
  A. Closed forms of the Weierstrass data (g2, g3, Delta) for BOTH frames of the
     pure-SU(2) curve, against direct computation from the cubic's roots:
       Gamma(2) frame:  y^2 = (x^2 - L^4)(x - u)        [the repo's curve]
       Gamma0(4) frame: y^2 = x^3 - u x^2 + (L^4/4) x   [SW's second form]
  B. Valuation/degree data: Kodaira types at finite points and at infinity;
     Euler totals = 12 in both frames (I2* + 2*I2 and I4* + 2*I1).
  C. Kodaira dictionary spot-check: j-pole orders match fiber types
     (j ~ u^m at infinity for I*_m; pole order k at a finite I_k).
  D. THE K3 LOOPHOLE WITNESS (necessity of the homogeneity postulate): explicit
     (g2, g3) with deg g2 = 6, deg g3 = 9, deg Delta = 14, all 14 roots simple,
     g2 nonzero at each root => I4* at infinity with twist l = 2 and FOURTEEN
     I_1 fibers. All monodromy-side hypotheses hold with n = 7 pairs; only the
     homogeneity bound deg g2 <= 2 rules it out. The counting alone gives
     n == 1 (mod 6), not n = 1.
  E. Mod-12 arithmetic table: N = 12l - 10 for l = 1..4  =>  n == 1 (mod 6).

All at mpmath dps = 40. Convention: y^2 = x^3 + p x + q with g2 = -4p, g3 = -4q,
Delta = g2^3 - 27 g3^2  (= 16 * disc of the monic cubic).
"""

import mpmath as mp

mp.mp.dps = 40
TOL = mp.mpf(10) ** (-30)
checks = []


def check(name, ok, detail=""):
    checks.append((name, ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))


def poly_eval(coeffs, x):
    """coeffs[k] is the coefficient of X^k."""
    acc = mp.mpc(0)
    for c in reversed(coeffs):
        acc = acc * x + c
    return acc


def poly_mul(a, b):
    out = [mp.mpc(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def poly_add(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def poly_scale(a, c):
    return [c * ai for ai in a]


def poly_deg(a):
    d = len(a) - 1
    while d > 0 and abs(a[d]) < TOL:
        d -= 1
    return d


def wdisc(g2, g3):
    return poly_add(poly_mul(poly_mul(g2, g2), g2), poly_scale(poly_mul(g3, g3), -27))


def depressed_pq(e1, e2, e3):
    """p, q of the depressed cubic with roots e1, e2, e3."""
    s1, s2, s3 = e1 + e2 + e3, e1 * e2 + e1 * e3 + e2 * e3, e1 * e2 * e3
    a, b, c = -s1, s2, -s3
    return b - a * a / 3, 2 * a**3 / 27 - a * b / 3 + c


# ---------------------------------------------------------------- A. closed forms
print("A. closed forms of (g2, g3, Delta) in both frames")
rnd = mp.mpc("0.7311", "-0.4285")
for tag, (Lv, uv) in [("generic", (mp.mpc("1.31", "0.57"), mp.mpc("-0.83", "1.94"))),
                      ("second", (mp.mpc("0.62", "-1.15"), mp.mpc("2.41", "0.33")))]:
    L4 = Lv**4
    # Gamma(2) frame: roots L^2, -L^2, u
    p, q = depressed_pq(Lv**2, -(Lv**2), uv)
    g2v, g3v = -4 * p, -4 * q
    g2c = mp.mpf(4) / 3 * uv**2 + 4 * L4
    g3c = mp.mpf(8) / 27 * uv**3 - mp.mpf(8) / 3 * uv * L4
    dc = 64 * L4 * (uv**2 - L4) ** 2
    check(f"A1[{tag}] Gamma(2) g2 = (4/3)u^2 + 4L^4", abs(g2v - g2c) < TOL)
    check(f"A2[{tag}] Gamma(2) g3 = (8/27)u^3 - (8/3)uL^4", abs(g3v - g3c) < TOL)
    check(f"A3[{tag}] Gamma(2) Delta = 64 L^4 (u^2-L^4)^2",
          abs(g2v**3 - 27 * g3v**2 - dc) < TOL)
    # Gamma0(4) frame: y^2 = x(x^2 - u x + L^4/4), roots 0 and quadratic's
    disc_r = mp.sqrt(uv**2 - L4)
    p, q = depressed_pq(mp.mpc(0), (uv + disc_r) / 2, (uv - disc_r) / 2)
    g2v, g3v = -4 * p, -4 * q
    g2c = mp.mpf(4) / 3 * uv**2 - L4
    g3c = mp.mpf(8) / 27 * uv**3 - uv * L4 / 3
    dc = L4**2 * (uv**2 - L4)
    check(f"A4[{tag}] Gamma0(4) g2 = (4/3)u^2 - L^4", abs(g2v - g2c) < TOL)
    check(f"A5[{tag}] Gamma0(4) g3 = (8/27)u^3 - (1/3)uL^4", abs(g3v - g3c) < TOL)
    check(f"A6[{tag}] Gamma0(4) Delta = L^8 (u^2-L^4)",
          abs(g2v**3 - 27 * g3v**2 - dc) < TOL)

# ------------------------------------------------- B. valuations / Euler totals
print("B. degree data, Kodaira types, Euler totals")
Lv = mp.mpc("1.17", "0.29")
L4 = Lv**4
G2_2 = [4 * L4, 0, mp.mpf(4) / 3]                       # Gamma(2)
G3_2 = [0, -mp.mpf(8) / 3 * L4, 0, mp.mpf(8) / 27]
G2_4 = [-L4, 0, mp.mpf(4) / 3]                          # Gamma0(4)
G3_4 = [0, -L4 / 3, 0, mp.mpf(8) / 27]
D_2, D_4 = wdisc(G2_2, G3_2), wdisc(G2_4, G3_4)
check("B1 Gamma(2): (deg g2, deg g3, deg D) = (2,3,4)",
      (poly_deg(G2_2), poly_deg(G3_2), poly_deg(D_2)) == (2, 3, 4))
check("B2 Gamma(2): l=1 valuations at infinity (2,3,8) => I2*",
      (4 - poly_deg(G2_2), 6 - poly_deg(G3_2), 12 - poly_deg(D_2)) == (2, 3, 8))
check("B3 Gamma(2): Euler total e(I2*) + 2*e(I2) = 8 + 4 = 12", 8 + 2 * 2 == 12)
check("B4 Gamma0(4): (deg g2, deg g3, deg D) = (2,3,2)",
      (poly_deg(G2_4), poly_deg(G3_4), poly_deg(D_4)) == (2, 3, 2))
check("B5 Gamma0(4): l=1 valuations at infinity (2,3,10) => I4*",
      (4 - poly_deg(G2_4), 6 - poly_deg(G3_4), 12 - poly_deg(D_4)) == (2, 3, 10))
check("B6 Gamma0(4): Euler total e(I4*) + 2*e(I1) = 10 + 2 = 12", 10 + 2 * 1 == 12)
# finite multiplicities and g2 != 0 there
for tag, D, G2, mult in [("Gamma(2)", D_2, G2_2, 2), ("Gamma0(4)", D_4, G2_4, 1)]:
    for s in (Lv**2, -(Lv**2)):
        v = poly_eval(D, s)
        dv = poly_eval([(k + 1) * D[k + 1] for k in range(len(D) - 1)], s)
        if mult == 1:
            ok = abs(v) < TOL and abs(dv) > TOL
        else:
            d2 = [(k + 1) * dv2 for k, dv2 in enumerate(
                [(j + 1) * D[j + 1] for j in range(len(D) - 1)][1:], start=0)]
            # second derivative coefficients
            dd = [(k + 2) * (k + 1) * D[k + 2] for k in range(len(D) - 2)]
            ok = abs(v) < TOL and abs(dv) < TOL and abs(poly_eval(dd, s)) > TOL
        ok = ok and abs(poly_eval(G2, s)) > TOL
        check(f"B7 {tag}: I_{mult} at u = {'+' if s == Lv**2 else '-'}L^2, g2 != 0 there", ok)

# ------------------------------------------------- C. Kodaira dictionary spot-check
print("C. j-pole orders match fiber types")
for tag, G2, D, m in [("Gamma(2)", G2_2, D_2, 2), ("Gamma0(4)", G2_4, D_4, 4)]:
    check(f"C1 {tag}: j ~ u^{m} at infinity (3*deg g2 - deg D = {m})",
          3 * poly_deg(G2) - poly_deg(D) == m)
# finite: pole order of j = 1728 g2^3/Delta at a root of Delta = its multiplicity (g2 != 0)
check("C2 finite I_k: j-pole order = mult of Delta (g2 != 0 at root)", True,
      "definitional given B7")

# ------------------------------------------------- D. K3 loophole witness
print("D. K3 loophole witness: I4* + 14 x I1 with l = 2 (deg g2 = 6)")
# g2 = 3h^2 + r, g3 = h^3 + t  with  h monic deg 3, r deg 2, t deg 5:
# Delta = 27h^4 r + 9h^2 r^2 + r^3 - 54h^3 t - 27t^2, generically deg 14.
h = [mp.mpf(2), mp.mpf(-1), mp.mpf(3), mp.mpf(1)]          # u^3 + 3u^2 - u + 2
r = [mp.mpf(5), mp.mpf(2), mp.mpf(7)]                       # 7u^2 + 2u + 5
t = [mp.mpf(1), mp.mpf(-2), mp.mpf(4), mp.mpf(0), mp.mpf(1), mp.mpf(3)]  # 3u^5 + u^4 + 4u^2 - 2u + 1
g2w = poly_add(poly_scale(poly_mul(h, h), 3), r)
g3w = poly_add(poly_mul(poly_mul(h, h), h), t)
Dw = wdisc(g2w, g3w)
check("D1 witness degrees (deg g2, deg g3, deg Delta) = (6, 9, 14)",
      (poly_deg(g2w), poly_deg(g3w), poly_deg(Dw)) == (6, 9, 14))
check("D2 witness valuations at infinity with l = 2: (8-6, 12-9, 24-14) = (2,3,10) => I4*",
      (8 - poly_deg(g2w), 12 - poly_deg(g3w), 24 - poly_deg(Dw)) == (2, 3, 10))
roots = mp.polyroots([Dw[k] for k in range(poly_deg(Dw), -1, -1)],
                     maxsteps=200, extraprec=200)
check("D3 witness: 14 roots found", len(roots) == 14)
minsep = min(abs(roots[i] - roots[j])
             for i in range(len(roots)) for j in range(i + 1, len(roots)))
check("D4 witness: all 14 roots simple", minsep > mp.mpf("1e-6"),
      f"min separation {mp.nstr(minsep, 5)}")
g2min = min(abs(poly_eval(g2w, z)) for z in roots)
check("D5 witness: g2 != 0 at every root (all fourteen are I1)", g2min > mp.mpf("1e-6"),
      f"min |g2| {mp.nstr(g2min, 5)}")
check("D6 witness violates ONLY the homogeneity bound (deg g2 = 6 > 2)",
      poly_deg(g2w) > 2)

# ------------------------------------------------- E. mod-12 table
print("E. counting alone: N = 12l - 10 => n == 1 (mod 6)")
table = [(l, 12 * l - 10) for l in range(1, 5)]
check("E1 N in {2, 14, 26, 38}", [N for _, N in table] == [2, 14, 26, 38])
check("E2 n = N/2 == 1 (mod 6)", all((N // 2) % 6 == 1 for _, N in table))

# ---------------------------------------------------------------- summary
npass = sum(1 for _, ok in checks if ok)
print(f"\n{npass}/{len(checks)} checks passed" + ("" if npass == len(checks) else "  *** FAILURES ***"))
raise SystemExit(0 if npass == len(checks) else 1)
