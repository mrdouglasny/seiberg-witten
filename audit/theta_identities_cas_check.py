#!/usr/bin/env python3
"""
CAS evidence for the two theta-function axioms in SeibergWitten/Physics/ThetaLambda.lean:

  AX_jacobi_quartic : theta3 t ^ 4 = theta2 t ^ 4 + theta4 t ^ 4   (Jacobi's identity)
  AX_theta3_ne_zero : theta3 t ≠ 0   on the upper half plane

These are NOT yet Lean-proved (Mathlib lacks the Sturm bound / dimension of M_2(Gamma(2))
needed for the quartic, and the Jacobi triple product / divisor needed for non-vanishing).
This script is reproducible *external evidence* supporting their audit rating, per the
project's "results require saved scripts with saved outputs" discipline.

Conventions (matching ThetaLambda.lean, nome q = exp(i*pi*t)):
  theta3(t) = sum_{n in Z} q^{n^2}
  theta4(t) = sum_{n in Z} (-1)^n q^{n^2}
  theta2(t) = sum_{n in Z} q^{(n+1/2)^2}

PART A — exact integer q-series identity (rigorous to the truncation order).
  We work in Q = q^{1/4} so all exponents are integers:
    theta3 = sum Q^{4 n^2},  theta4 = sum (-1)^n Q^{4 n^2},  theta2 = sum Q^{(2n+1)^2}.
  Verify theta3^4 - theta4^4 - theta2^4 == 0 coefficientwise up to order M.

PART B — high-precision numerical check of the quartic + theta3 non-vanishing on a grid.
  Uses mpmath if available; otherwise a high-order direct series sum.
"""

# ---------- PART A: exact integer q-series (in Q = q^{1/4}) ----------

def qseries_to(M):
    """Coefficient lists (length M+1) of theta3, theta4, theta2 in Q = q^{1/4}."""
    import math
    t3 = [0] * (M + 1)
    t4 = [0] * (M + 1)
    t2 = [0] * (M + 1)
    nmax = int(math.isqrt(M)) + 2
    for n in range(-nmax, nmax + 1):
        e = 4 * n * n                      # theta3/theta4 exponent in Q
        if e <= M:
            t3[e] += 1
            t4[e] += (-1) ** n
        eo = (2 * n + 1) ** 2              # theta2 exponent in Q
        if 0 <= eo <= M:
            t2[eo] += 1
    return t3, t4, t2

def mul(a, b, M):
    c = [0] * (M + 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if i + j > M:
                break
            if bj:
                c[i + j] += ai * bj
    return c

def pow4(a, M):
    return mul(mul(a, a, M), mul(a, a, M), M)

def part_A(M=200):
    t3, t4, t2 = qseries_to(M)
    lhs = pow4(t3, M)
    rhs = [x + y for x, y in zip(pow4(t4, M), pow4(t2, M))]
    diff = [l - r for l, r in zip(lhs, rhs)]
    ok = all(d == 0 for d in diff)
    # report the first few nonzero coeffs of theta3^4 (= sum_{k} r_4-counts) as a sanity peek
    head = [lhs[i] for i in range(0, min(M, 40) + 1, 4)]   # coeffs of q^0,q^1,... (Q^{4k})
    print(f"[A] exact integer q-series, Q=q^(1/4), order M={M}")
    print(f"[A] theta3^4 - theta4^4 - theta2^4 == 0  up to order {M}:  {ok}")
    print(f"[A] theta3^4 q-coefficients (q^0..q^10): {head[:11]}   "
          f"(should be 1,8,24,32,24,48,96,64,24,104,144 = r_4(n))")
    return ok

# ---------- PART B: numerical (mpmath) ----------

def _thetas_stdlib(t, terms=400):
    """Direct series sums (pure stdlib cmath), q = exp(i*pi*t), converges for Im t > 0."""
    import cmath
    q = cmath.exp(1j * cmath.pi * t)
    th3 = 1 + 0j
    th4 = 1 + 0j
    for n in range(1, terms + 1):
        qn = q ** (n * n)
        th3 += 2 * qn
        th4 += 2 * ((-1) ** n) * qn
    th2 = 0j
    for n in range(0, terms + 1):
        e = (n + 0.5) ** 2
        th2 += 2 * (q ** e)
    return th3, th2, th4

def part_B():
    try:
        import mpmath as mp
        mp.mp.dps = 40
        def thetas(t):
            q = mp.e ** (mp.pi * 1j * t)
            return mp.jtheta(3, 0, q), mp.jtheta(2, 0, q), mp.jtheta(4, 0, q)
        absf, conv, name = (lambda z: abs(z)), mp.mpc, "mpmath dps=40"
    except Exception:
        thetas, absf, conv, name = _thetas_stdlib, abs, complex, "stdlib cmath, 400 terms"
    print(f"[B] numerics backend: {name}")
    # quartic at several interior points
    pts = [0.5j, 1j, 2j, 0.3 + 0.7j, -0.4 + 1.3j, 0.9 + 0.2j]
    maxerr = 0.0
    for t in pts:
        th3, th2, th4 = thetas(conv(t))
        maxerr = max(maxerr, float(absf(th3**4 - th2**4 - th4**4)))
    print(f"[B] |theta3^4 - theta2^4 - theta4^4| over {len(pts)} points, max = {maxerr:.3e}")
    # non-vanishing of theta3 on a grid of the upper half plane
    mn = None
    nx, ny = 41, 40
    for ix in range(nx):
        x = -1.0 + 2.0 * ix / (nx - 1)
        for iy in range(ny):
            y = 0.05 + (2.5 - 0.05) * iy / (ny - 1)
            th3, _, _ = thetas(conv(complex(x, y)))
            v = float(absf(th3))
            mn = v if mn is None else min(mn, v)
    print(f"[B] min |theta3| over {nx}x{ny} grid, x in [-1,1], Im t in [0.05,2.5] = {mn:.6f}")
    print(f"[B] theta3 non-vanishing on grid: {mn > 0}")
    return maxerr, mn


if __name__ == "__main__":
    a = part_A(200)
    part_B()
    print(f"\nSUMMARY: quartic exact-series identity verified to order 200: {a}")
