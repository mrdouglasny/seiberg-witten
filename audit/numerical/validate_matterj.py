#!/usr/bin/env python3
"""MC0 — numeric pinning for the matter (j-invariant) route
(`audit/MATTER_CLASSICAL_PLAN.md`).

The SU(2) N_f curve is y² = Q(x) := (x²−u)² − Λ^{4−N_f}·∏(x−mᵢ). The route anchors
the coupling through the j-invariant, computed two independent ways:

  * COEFFICIENT side (the future Lean definitions): the classical Weierstrass
    invariants of a quartic a x⁴+b x³+c x²+d x+e,
        g₂ = ae − bd/4 + c²/12
        g₃ = ace/6 + bcd/48 − ad²/16 − b²e/16 − c³/216
        j  = 1728 g₂³/(g₂³ − 27 g₃²),
    rational in (u, m, Λ).
  * ROOT side (the classical meaning): λ = cross-ratio of the four branch points,
    jλ(λ) = 256(1−λ+λ²)³/(λ²(1−λ)²); and the τ side, τ = iK(1−λ)/K(λ),
    j from the θ-based λ(τ) of the companion scripts' conventions.

Checks:
  A. anharmonic invariance: all 6 cross-ratio orderings give one jλ value;
  B. jλ(cross-ratio) = j(g₂,g₃) for complex samples, N_f = 0 and N_f = 1;
  C. pure-case reduction WITH THE LANDEN FACTOR 2 (a convention finding this gate
     caught): j(g₂,g₃) = jλ(Landen(2Λ²/(u+Λ²))) for N_f = 0, where
     Landen(m) = ((1−√(1−m))/(1+√(1−m)))² = λ(2τ)|_{λ(τ)=m} — the quartic's
     intrinsic modulus is 2·τ_SW; the naive jλ(m(u)) DIFFERS (witness kept);
  D. τ-side: jλ(λ(τ_curve)) = j(g₂,g₃) with τ_curve = iK(1−κ)/K(κ) at a root
     cross-ratio κ (any ordering — by A);
  E. the N_f = 1 Argyres–Douglas point (u,m) = (¾Λ², −¾Λ): g₂ = g₃ = 0 exactly
     (triple root ⟺ both invariants vanish), with linear vanishing along a ray.

A pass is necessary, not sufficient (branch/ordering issues at unsampled points).
dps = 40 as in the companion scripts.
"""
import mpmath as mp

mp.mp.dps = 40
TOL = mp.mpf(10) ** (-25)

results = []
def check(name, cond, detail=""):
    results.append((name, bool(cond), detail))
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")

def quartic_coeffs(Nf, L, masses, u):
    """Coefficients (a,b,c,d,e) of (x²−u)² − Λ^{4−Nf}·∏(x−mᵢ)."""
    # (x²−u)² = x⁴ − 2u x² + u²
    a, b, c, d, e = mp.mpf(1), mp.mpf(0), -2*u, mp.mpf(0), u**2
    # subtract Λ^{4−Nf} ∏ (x − mᵢ)
    pref = L ** (4 - Nf)
    prod = [mp.mpf(1)]
    for mi in masses:
        new = [mp.mpf(0)] * (len(prod) + 1)
        for k, ck in enumerate(prod):
            new[k] += ck * (-mi)
            new[k + 1] += ck
        prod = new
    # prod has degree Nf ≤ 3 here; align into (a..e), x⁴..x⁰ order
    coeffs = [a, b, c, d, e]
    for k, ck in enumerate(prod):            # ck is coeff of x^k
        coeffs[4 - k] -= pref * ck
    return coeffs

def g2g3(coeffs):
    a, b, c, d, e = coeffs
    g2 = a*e - b*d/4 + c*c/12
    g3 = a*c*e/6 + b*c*d/48 - a*d*d/16 - b*b*e/16 - c**3/216
    return g2, g3

def j_from_g(g2, g3):
    return 1728 * g2**3 / (g2**3 - 27 * g3**2)

def j_from_lambda(lam):
    return 256 * (1 - lam + lam**2)**3 / (lam**2 * (1 - lam)**2)

def roots_of(coeffs):
    return mp.polyroots([mp.mpc(x) for x in coeffs], maxsteps=200, extraprec=80)

def cross_ratio(e1, e2, e3, e4):
    return ((e1 - e2) * (e3 - e4)) / ((e1 - e3) * (e2 - e4))

import itertools

print("=== A: anharmonic invariance of jλ over root orderings ===")
SAMPLES = [
    (0, mp.mpc(1), [],                 mp.mpc(3, 1)),
    (1, mp.mpc(1), [mp.mpc('0.3','0.2')], mp.mpc(2, 1)),
    (1, mp.mpc('1.1','-0.3'), [mp.mpc('-0.7')], mp.mpc('1.5','2.0')),
]
for Nf, L, masses, u in SAMPLES:
    co = quartic_coeffs(Nf, L, masses, u)
    rts = roots_of(co)
    js = []
    for perm in itertools.permutations(range(4)):
        k = cross_ratio(*[rts[i] for i in perm])
        js.append(j_from_lambda(k))
    spread = max(abs(js[0] - jv) for jv in js)
    check(f"jλ ordering-free  Nf={Nf} u={mp.nstr(u,4)}", spread < TOL,
          f"spread={mp.nstr(spread, 3)}")

print("=== B: jλ(cross-ratio) = j(g₂,g₃) — coefficient vs root side ===")
for Nf, L, masses, u in SAMPLES:
    co = quartic_coeffs(Nf, L, masses, u)
    rts = roots_of(co)
    k = cross_ratio(*rts)
    r = abs(j_from_lambda(k) - j_from_g(*g2g3(co)))
    check(f"j coeff=root      Nf={Nf} u={mp.nstr(u,4)}", r < TOL, f"res={mp.nstr(r,3)}")

print("=== C: pure-case reduction (with the Landen factor 2) ===")
# CONVENTION FINDING (caught by this gate, 2026-07-05): the quartic's intrinsic
# modulus is 2·τ_SW — the same Γ(2) factor the pure pinning caught. The correct
# reduction is j_curve = jλ(Landen(m(u))), Landen(m) = ((1−√(1−m))/(1+√(1−m)))²
# = λ(2τ) at λ(τ) = m; the naive jλ(m(u)) is the τ_SW-level j and DIFFERS.
def landen(m):
    s = mp.sqrt(1 - m)
    return ((1 - s) / (1 + s)) ** 2
for u in (mp.mpc(3, 1), mp.mpc('-0.5', '2.2'), mp.mpc(5, 0)):
    L = mp.mpc(1)
    co = quartic_coeffs(0, L, [], u)
    mm = 2 * L**2 / (u + L**2)
    r = abs(j_from_g(*g2g3(co)) - j_from_lambda(landen(mm)))
    check(f"pure j = jλ(Landen m) u={mp.nstr(u,4)}", r < TOL, f"res={mp.nstr(r,3)}")
    rw = abs(j_from_g(*g2g3(co)) - j_from_lambda(mm))
    check(f"factor-2 witness      u={mp.nstr(u,4)}", rw > 1,
          f"naive-res={mp.nstr(rw,3)} (must NOT vanish)")

print("=== D: τ-side  jλ(λ(τ_curve)) = j(g₂,g₃), τ_curve = iK'/K at a root κ ===")
N = 90
def theta3s(tau):
    return mp.fsum(mp.e ** (mp.pi * 1j * tau * (n * n)) for n in range(-N, N + 1))
def theta2s(tau):
    return mp.fsum(mp.e ** (mp.pi * 1j * tau * (n + mp.mpf(1)/2) ** 2)
                   for n in range(-N, N + 1))
def lam_of_tau(tau):
    return theta2s(tau) ** 4 / theta3s(tau) ** 4
for Nf, L, masses, u in SAMPLES:
    co = quartic_coeffs(Nf, L, masses, u)
    rts = roots_of(co)
    k = cross_ratio(*rts)
    tau = 1j * mp.ellipk(1 - k) / mp.ellipk(k)
    if mp.im(tau) < 0:
        tau = -tau  # orientation of the ordering; jλ is insensitive
    r = abs(j_from_lambda(lam_of_tau(tau)) - j_from_g(*g2g3(co)))
    check(f"j(τ_curve)=j      Nf={Nf} u={mp.nstr(u,4)}", r < mp.mpf(10)**(-20),
          f"res={mp.nstr(r,3)}")

print("=== E: N_f=1 AD point  (u,m) = (¾Λ², −¾Λ):  g₂ = g₃ = 0 ===")
L = mp.mpc(1)
co = quartic_coeffs(1, L, [mp.mpf(-0.75) * L], mp.mpf(0.75) * L**2)
g2, g3 = g2g3(co)
check("g2 = 0 at AD", abs(g2) < TOL, f"|g2|={mp.nstr(abs(g2),3)}")
check("g3 = 0 at AD", abs(g3) < TOL, f"|g3|={mp.nstr(abs(g3),3)}")
prev2 = prev3 = None
for eps in ('1e-2', '1e-4'):
    du = mp.mpf(eps)
    co = quartic_coeffs(1, L, [mp.mpf(-0.75) * L], mp.mpf(0.75) * L**2 + du)
    g2e, g3e = g2g3(co)
    if prev2 is not None:
        check(f"g2 linear rate    du={eps}", abs(g2e) < prev2 / 50,
              f"|g2|={mp.nstr(abs(g2e),3)}")
        check(f"g3 linear rate    du={eps}", abs(g3e) < prev3 / 50,
              f"|g3|={mp.nstr(abs(g3e),3)}")
    prev2, prev3 = abs(g2e), abs(g3e)

print("=== F: MC3 chart hypotheses are satisfiable (non-vacuity probe) ===")
# For Nf = 1 samples: the intrinsic tau (= 2 tau_SW, what the developing condition
# anchors) has lambda-value x with AnharmonicRegular(x): off the cusps {0,1} and
# the coincidence set {1/2, -1, 2, e^{+-i pi/3}} - i.e. the MC3 regularity
# hypotheses hold on honest charts, not vacuously.
EXC = [mp.mpf(0), mp.mpf(1), mp.mpf(1)/2, mp.mpf(-1), mp.mpf(2),
       mp.e ** (1j * mp.pi / 3), mp.e ** (-1j * mp.pi / 3)]
def lam_theta(tau):
    return lam_of_tau(tau)
for Nf, L, masses, u in SAMPLES:
    if Nf != 1:
        continue
    co = quartic_coeffs(Nf, L, masses, u)
    rts = roots_of(co)
    k = cross_ratio(*rts)
    tau = 1j * mp.ellipk(1 - k) / mp.ellipk(k)
    if mp.im(tau) < 0:
        tau = -tau
    x = lam_theta(tau)
    dmin = min(abs(x - e) for e in EXC)
    check(f"AnharmonicRegular  u={mp.nstr(u,4)}", dmin > mp.mpf('1e-6'),
          f"min dist to exceptional set = {mp.nstr(dmin, 4)}")
# and along a small u-path (chart-sized nonvacuity, not just points)
L = mp.mpc(1)
for s in range(5):
    u = mp.mpc('2.0', '1.0') + mp.mpf(s) / 10
    co = quartic_coeffs(1, L, [mp.mpc('0.3','0.2')], u)
    rts = roots_of(co)
    k = cross_ratio(*rts)
    tau = 1j * mp.ellipk(1 - k) / mp.ellipk(k)
    if mp.im(tau) < 0:
        tau = -tau
    x = lam_theta(tau)
    dmin = min(abs(x - e) for e in EXC)
    check(f"regular on path    s={s}", dmin > mp.mpf('1e-6'),
          f"min dist = {mp.nstr(dmin, 4)}")

ok = all(r[1] for r in results)
npass = sum(1 for r in results if r[1])
print(f"\n=== {'ALL PASS' if ok else 'FAILURES PRESENT'} : "
      f"{npass}/{len(results)} checks, dps={mp.mp.dps} ===")
raise SystemExit(0 if ok else 1)
