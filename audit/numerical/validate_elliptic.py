#!/usr/bin/env python3
"""Numerical vetting of the proposed C-route elliptic-integral axioms (C1-C3).

Per audit/GENUS1_PERIODS_PLAN.md (revision 2026-07-04): before formalizing, vet the
three proposed classical axioms with an independent engine (mpmath). Companion to
validate_lambda.py (same conventions: theta-nulls with nome q = exp(pi*i*tau), the
modular lambda = theta2^4/theta3^4; dps = 40).

Checks:
  * D0 (definition faithfulness): the proposed Lean definition of K(m) — the honest
    interval integral of (1 - m sin^2 t)^(-1/2), principal branch — agrees with
    mpmath.ellipk(m) on the cut plane (same for E via ellipe). This pins the Lean
    def to the classical object BEFORE the axioms about it are trusted.
  * C1 (Jacobi inversion / theta-bridge): for sampled m in the cut plane, the
    explicit witness tau* = i K(1-m)/K(m) satisfies
      Im tau* > 0,   lambda(tau*) = m,   K(m) = (pi/2) theta3(tau*)^2.
  * C2 (Legendre relation): E K' + E' K - K K' = pi/2.
  * C3 (log asymptotic): K(1-m) + (1/2) log m -> 2 log 2 as m -> 0, with the
    expected O(m log m) rate.

A pass is necessary, not sufficient (it cannot see quantifier/branch-domain issues
at points not sampled); the branch checks here deliberately sample all four
quadrants of the cut plane, since branch conventions are the flagged risk.
"""
import mpmath as mp

mp.mp.dps = 40
TOL = mp.mpf(10) ** (-25)
N = 90  # theta series cutoff

def theta3(tau):
    return mp.fsum(mp.e ** (mp.pi * 1j * tau * (n * n)) for n in range(-N, N + 1))

def theta2(tau):
    return mp.fsum(mp.e ** (mp.pi * 1j * tau * (n + mp.mpf(1) / 2) ** 2)
                   for n in range(-N, N + 1))

def lam(tau):
    return theta2(tau) ** 4 / theta3(tau) ** 4

# The PROPOSED LEAN DEFINITIONS, transcribed: honest integrals, principal branch.
def K_def(m):
    return mp.quad(lambda t: (1 - m * mp.sin(t) ** 2) ** mp.mpf('-0.5'),
                   [0, mp.pi / 2])

def E_def(m):
    return mp.quad(lambda t: (1 - m * mp.sin(t) ** 2) ** mp.mpf('0.5'),
                   [0, mp.pi / 2])

results = []
def check(name, cond, detail=""):
    results.append((name, bool(cond), detail))
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")

# Sample m across the cut plane C \ ((-inf,0] u [1,inf)): all four quadrants,
# real (0,1), near-cut, and large-|m| off-axis points.
M_SAMPLES = [mp.mpc('0.3', '0.4'), mp.mpc('0.7', '-0.2'), mp.mpc('0.5', '0'),
             mp.mpc('-0.3', '0.5'), mp.mpc('-1.2', '-0.7'), mp.mpc('1.5', '0.8'),
             mp.mpc('2.0', '-3.0'), mp.mpc('0.99', '0.001'), mp.mpc('0.01', '0')]

print("=== D0: proposed Lean defs = classical K, E (vs mpmath.ellipk/ellipe) ===")
for m in M_SAMPLES:
    rK = abs(K_def(m) - mp.ellipk(m))
    rE = abs(E_def(m) - mp.ellipe(m))
    check(f"K_def(m)=ellipk  m={mp.nstr(m, 5)}", rK < TOL, f"res={mp.nstr(rK, 3)}")
    check(f"E_def(m)=ellipe  m={mp.nstr(m, 5)}", rE < TOL, f"res={mp.nstr(rE, 3)}")

print("=== C1: Jacobi inversion — tau* = i K(1-m)/K(m) inverts lambda; theta bridge ===")
for m in M_SAMPLES:
    K, Kp = mp.ellipk(m), mp.ellipk(1 - m)
    tau = 1j * Kp / K
    im_ok = mp.im(tau) > 0
    rlam = abs(lam(tau) - m)
    rbridge = abs(K - (mp.pi / 2) * theta3(tau) ** 2)
    check(f"Im tau* > 0      m={mp.nstr(m, 5)}", im_ok, f"Im={mp.nstr(mp.im(tau), 5)}")
    check(f"lambda(tau*)=m   m={mp.nstr(m, 5)}", rlam < TOL, f"res={mp.nstr(rlam, 3)}")
    check(f"K=(pi/2)theta3^2 m={mp.nstr(m, 5)}", rbridge < TOL, f"res={mp.nstr(rbridge, 3)}")

print("=== C2: Legendre relation  E K' + E' K - K K' = pi/2 ===")
for m in M_SAMPLES:
    K, Kp = mp.ellipk(m), mp.ellipk(1 - m)
    E, Ep = mp.ellipe(m), mp.ellipe(1 - m)
    r = abs(E * Kp + Ep * K - K * Kp - mp.pi / 2)
    check(f"Legendre         m={mp.nstr(m, 5)}", r < TOL, f"res={mp.nstr(r, 3)}")

print("=== C3: K(1-m) + (1/2) log m -> 2 log 2  as m -> 0 (rate ~ m log m) ===")
prev = None
for expo in (4, 8, 12, 16):
    for m in (mp.mpf(10) ** (-expo), mp.mpc(1, 1) / mp.sqrt(2) * mp.mpf(10) ** (-expo)):
        r = abs(mp.ellipk(1 - m) + mp.mpf('0.5') * mp.log(m) - 2 * mp.log(2))
        # residual should be O(|m| log|m|): comfortably below 10^(-expo+2)
        check(f"C3 residual      m~1e-{expo} ({'real' if mp.im(m)==0 else 'cplx'})",
              r < mp.mpf(10) ** (-expo + 2), f"res={mp.nstr(r, 3)}")

# --- v2 additions after the adversarial review (GR 2026-07-04): the strengthened
# --- clauses of C1/C3 and the new C4 cusp-labeling axiom.

print("=== C1v2: K(m) != 0 (explicit nonvanishing clause) — grid sample ===")
grid = [mp.mpc(r, 0) for r in ('0.01', '0.5', '0.99')] + \
       [mp.mpc(rad, 0) * mp.e ** (1j * mp.pi * ang)
        for rad in ('0.3', '1.7', '8.0', '50.0')
        for ang in (mp.mpf(k) / 12 for k in (1, 3, 5, 7, 9, 11, -2, -6, -10))]
minK = min(abs(mp.ellipk(m)) for m in grid)
check(f"min |K| on {len(grid)}-pt grid", minK > mp.mpf('0.01'),
      f"min|K|={mp.nstr(minK, 5)}")

print("=== C3v2: E(m) -> pi/2 and E(1-m) -> 1 as m -> 0 (H2's missing limits) ===")
for expo in (4, 8, 12):
    for m in (mp.mpf(10) ** (-expo), mp.mpc(1, 1) / mp.sqrt(2) * mp.mpf(10) ** (-expo)):
        r1 = abs(mp.ellipe(m) - mp.pi / 2)
        r2 = abs(mp.ellipe(1 - m) - 1)
        tag = 'real' if mp.im(m) == 0 else 'cplx'
        check(f"E(m)->pi/2       m~1e-{expo} ({tag})", r1 < mp.mpf(10) ** (-expo + 1),
              f"res={mp.nstr(r1, 3)}")
        check(f"E(1-m)->1        m~1e-{expo} ({tag})", r2 < mp.mpf(10) ** (-expo + 2),
              f"res={mp.nstr(r2, 3)}")

print("=== C3v3: K(m) -> pi/2 as m -> 0 (added for the monopole-vanishing theorem) ===")
for expo in (4, 8, 12):
    for m in (mp.mpf(10) ** (-expo), mp.mpc(1, 1) / mp.sqrt(2) * mp.mpf(10) ** (-expo)):
        r = abs(mp.ellipk(m) - mp.pi / 2)
        tag = 'real' if mp.im(m) == 0 else 'cplx'
        check(f"K(m)->pi/2       m~1e-{expo} ({tag})", r < mp.mpf(10) ** (-expo + 1),
              f"res={mp.nstr(r, 3)}")

print("=== C4: cusp labeling — tau + (i/pi) log(m/16) single-valued at m=0 (T^2) ===")
def tau_of(m):
    return 1j * mp.ellipk(1 - m) / mp.ellipk(m)
eps = mp.mpf(10) ** (-6)
for delta in ('0.3', '0.1', '0.01'):
    d = mp.mpf(delta)
    mp_up = eps * mp.e ** (1j * (mp.pi - d))   # just above the negative-real cut
    mp_dn = eps * mp.e ** (-1j * (mp.pi - d))  # just below
    # tau itself jumps across the cut by exactly the T^2 generator: tau_up - tau_dn -> +2
    jump = tau_of(mp_up) - tau_of(mp_dn)
    check(f"tau jump at m=0 -> +2   delta={delta}", abs(jump - 2) < mp.mpf(2) * d,
          f"jump={mp.nstr(jump, 8)}")
    # equivalently the log-remainder h = tau + (i/pi) log(m/16) is single-valued
    h_up = tau_of(mp_up) + (1j / mp.pi) * mp.log(mp_up / 16)
    h_dn = tau_of(mp_dn) + (1j / mp.pi) * mp.log(mp_dn / 16)
    check(f"h single-valued at m=0  delta={delta}", abs(h_up - h_dn) < mp.mpf(2) * d,
          f"|dh|={mp.nstr(abs(h_up - h_dn), 3)}")

print("=== C4: cusp at m=1 — the jump is the conjugate parabolic ST^2S^-1 ===")
for delta in ('0.3', '0.1', '0.01'):
    d = mp.mpf(delta)
    A = tau_of(1 - eps * mp.e ** (1j * (mp.pi - d)))
    B = tau_of(1 - eps * mp.e ** (-1j * (mp.pi - d)))
    # expect A and B related by tau -> tau/(1 - 2 tau) (one orientation) — try both
    r1 = abs(A - B / (1 - 2 * B))
    r2 = abs(B - A / (1 - 2 * A))
    check(f"m=1 jump is ST2S^-1     delta={delta}", min(r1, r2) < mp.mpf(2) * d,
          f"res={mp.nstr(min(r1, r2), 3)} (orient {'A=g(B)' if r1 < r2 else 'B=g(A)'})")

print("=== C4 analyticity of the remainder h (rebuts review-round-2 objection) ===")
# h(m) = tau(m) + (i/pi) log(m/16). Arithmetic-stencil second difference kills
# constant+linear AND the log part of any m*log(m) term: analytic h => d2/m^2 bounded
# (-> 2 h2); a c*m*log m term => d2/m^2 ~ 0.523 c/m (grows 10x per decade). Also
# |h1| must equal 1/(2pi) per the nome series q = m/16 + m^2/32 + ...
def h_rem(m):
    return tau_of(m) + (1j / mp.pi) * mp.log(m / 16)
ratios = []
for expo in (4, 6, 8):
    m = mp.mpf(10) ** (-expo)
    d2 = h_rem(3 * m) - 2 * h_rem(2 * m) + h_rem(m)
    ratios.append(abs(d2) / m ** 2)
check("d2/m^2 bounded (analytic), stable to 1e-4",
      abs(ratios[-1] - ratios[-2]) < mp.mpf('1e-4') * ratios[-1],
      f"ratios={[mp.nstr(r, 8) for r in ratios]}")
m = mp.mpf(10) ** (-8)
h1 = (h_rem(2 * m) - h_rem(m)) / m
check("|h1| = 1/(2pi) (nome-series prediction)",
      abs(abs(h1) - 1 / (2 * mp.pi)) < mp.mpf('1e-6'),
      f"|h1|={mp.nstr(abs(h1), 10)} vs {mp.nstr(1/(2*mp.pi), 10)}")

ok = all(r[1] for r in results)
npass = sum(1 for r in results if r[1])
print(f"\n=== {'ALL PASS' if ok else 'FAILURES PRESENT'} : "
      f"{npass}/{len(results)} checks, dps={mp.mp.dps} ===")
raise SystemExit(0 if ok else 1)
