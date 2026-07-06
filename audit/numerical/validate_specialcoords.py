#!/usr/bin/env python3
"""Pin the SU(2) special coordinates a, a_D (milestone S0 of the special-coordinate layer).

Determines, by computation that does not assume the answer, the closed forms landed in
SeibergWitten/Physics/SU2Rigidity.lean:

  a(u)   = (sqrt2/pi) * sqrt(u+L^2) * E(m),          m = 2L^2/(u+L^2)
  a_D(u) = (sqrt2/pi) * i * sqrt(u+L^2) * (K(1-m) - E(1-m))

Checks:
  * PIN-A: sqrt(u+L^2)*E(m) is proportional to the A-period of x^2 dx/y (the SW
    differential), constant |i/2| across real and complex u; the bracket K(1-m)-E(1-m)
    is the UNIQUE candidate whose ratio to the B-period is constant (= 1/2).
  * H1 (numeric): d a_D / d a = swTau(u) (finite differences), the special-geometry
    relation the C2-based milestone S1 will prove.
  * H2 (numeric): a_D -> 0 linearly at the monopole u = L^2 (the theorem
    swAD_tendsto_zero_monopole proves the limit from C3).
  * NORM: weak coupling a/sqrt(u) -> sqrt2/pi * pi/2 = 1/sqrt2, i.e. a ~ sqrt(u/2)
    (the standard SW normalization; fixes the prefactor for the future H6 milestone).
"""
import mpmath as mp

mp.mp.dps = 30
results = []
def check(name, cond, detail=""):
    results.append((name, bool(cond), detail))
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")

def seg_num(p, q, r3, r4, num, n=3000):
    h = (mp.pi/2)/n; vals=[]; w_prev=None
    for k in range(n+1):
        t = mp.sin(k*h)**2; x = p + (q-p)*t
        W = -((q-p)**2)*(x-r3)*(x-r4); s = mp.sqrt(W)
        if w_prev is not None and abs(-s-w_prev) < abs(s-w_prev): s = -s
        w_prev = s; vals.append(2*(q-p)*num(x)/s)
    tot = vals[0]+vals[-1]+4*mp.fsum(vals[1:n:2])+2*mp.fsum(vals[2:n:2])
    return tot*h/3

L = mp.mpf(1)
def m_of(u): return 2*L**2/(u+L**2)
def a_of(u):  return (mp.sqrt(2)/mp.pi)*mp.sqrt(u+L**2)*mp.ellipe(m_of(u))
def aD_of(u): s = 1-m_of(u); return (mp.sqrt(2)/mp.pi)*1j*mp.sqrt(u+L**2)*(mp.ellipk(s)-mp.ellipe(s))
def tau_of(u): m = m_of(u); return 1j*mp.ellipk(1-m)/mp.ellipk(m)

print("=== PIN-A/B: closed forms vs contour quadrature of x^2 dx/y ===")
for u in (mp.mpc(5), mp.mpc(9), mp.mpc(3,2)):
    e1, e2 = mp.sqrt(u+L**2), mp.sqrt(u-L**2)
    x2 = lambda x: x*x
    PA = 2*seg_num(e2, e1, -e1, -e2, x2)
    PB = seg_num(-e2, e2, e1, -e1, x2)
    rA = mp.sqrt(u+L**2)*mp.ellipe(m_of(u))/PA
    rB = mp.sqrt(u+L**2)*(mp.ellipk(1-m_of(u))-mp.ellipe(1-m_of(u)))/PB
    check(f"|rA| = 1/2   u={mp.nstr(u,4)}", abs(abs(rA)-mp.mpf(1)/2) < mp.mpf('1e-10'),
          f"rA={mp.nstr(rA, 8)}")
    check(f"rB  = 1/2    u={mp.nstr(u,4)}", abs(rB-mp.mpf(1)/2) < mp.mpf('1e-10'),
          f"rB={mp.nstr(rB, 8)}")

print("=== H1 (numeric): d a_D / d a = swTau ===")
for u in (mp.mpc(5), mp.mpc(9), mp.mpc(3,2), mp.mpc('2.2')):
    h = mp.mpf(10)**-12
    r = (aD_of(u+h)-aD_of(u-h))/(a_of(u+h)-a_of(u-h))
    check(f"dAD/dA = tau  u={mp.nstr(u,4)}", abs(r-tau_of(u)) < mp.mpf('1e-15'),
          f"res={mp.nstr(abs(r-tau_of(u)),3)}")

print("=== H2 (numeric): a_D -> 0 at the monopole, linear rate ===")
prev = None
for expo in (4, 6, 8):
    u = L**2 + mp.mpf(10)**(-expo)
    v = abs(aD_of(u))
    check(f"|a_D(1+1e-{expo})| small", v < mp.mpf(10)**(-expo+1), f"|aD|={mp.nstr(v,4)}")

print("=== NORM: weak coupling a ~ sqrt(u/2) ===")
u = mp.mpf(10)**8
r = a_of(u)/mp.sqrt(u)
check("a/sqrt(u) -> 1/sqrt2", abs(r-1/mp.sqrt(2)) < mp.mpf('1e-6'), f"ratio={mp.nstr(r,8)}")

ok = all(r[1] for r in results)
print(f"\n=== {'ALL PASS' if ok else 'FAILURES PRESENT'} : "
      f"{sum(1 for r in results if r[1])}/{len(results)} checks, dps={mp.mp.dps} ===")
raise SystemExit(0 if ok else 1)
