#!/usr/bin/env python3
"""Numerical vetting of the tau-derivative layer proved by the discharge loop
(iterations 22-23): the Wronskian formula, the coupling's closed-form derivative,
and the faithful weak-coupling log-running constant.

Same conventions as the companion scripts (mpmath, dps = 40; m the elliptic
parameter; K(m) = mp.ellipk(m)):

  * W  (Wronskian, `tau_ratio_hasDerivAt`):
        d/dm [ i K(1-m)/K(m) ] = -i pi / (4 m (1-m) K(m)^2)   on the cut plane.
  * D  (coupling derivative, `swTau_hasDerivAt`): with m(u) = 2 L^2/(u+L^2),
        d/du tau(u) = i pi / (4 (u+L^2) (1-m) K(m)^2).
  * R  (faithful log-running, `swTau_logDeriv_weakCoupling`):
        u * tau'(u) -> i/pi as |u| -> oo on the chart, with O(1/u) rate.

These pin the hand-derived constants (the i/pi limit and the 4 in the denominators)
against an independent engine; the kernel guarantees the derivations, this guards
the statements. A pass is necessary, not sufficient.
"""
import mpmath as mp

mp.mp.dps = 40
TOL = mp.mpf(10) ** (-25)

results = []
def check(name, cond, detail=""):
    results.append((name, bool(cond), detail))
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")

def tau_of_m(m):
    return 1j * mp.ellipk(1 - m) / mp.ellipk(m)

print("=== W: Wronskian  d/dm [iK'/K] = -i pi/(4 m (1-m) K^2) ===")
M_SAMPLES = [mp.mpc('0.3', '0.4'), mp.mpc('0.7', '-0.2'), mp.mpc('0.5', '0'),
             mp.mpc('-0.3', '0.5'), mp.mpc('2.0', '-3.0'), mp.mpc('0.01', '0')]
for m in M_SAMPLES:
    num = mp.diff(tau_of_m, m)
    K = mp.ellipk(m)
    closed = -1j * mp.pi / (4 * m * (1 - m) * K ** 2)
    r = abs(num - closed)
    check(f"Wronskian        m={mp.nstr(m, 5)}", r < mp.mpf(10) ** (-20),
          f"res={mp.nstr(r, 3)}")

print("=== D: d tau/du = i pi/(4 (u+L^2)(1-m) K(m)^2), m = 2L^2/(u+L^2) ===")
UL_SAMPLES = [(mp.mpc(3, 0), mp.mpc(1, 0)), (mp.mpc(2, 5), mp.mpc(1, 0)),
              (mp.mpc(-4, 1), mp.mpc(1, 0)), (mp.mpc(7, -2), mp.mpc('1.3', '0.4'))]
for u, L in UL_SAMPLES:
    def tau_of_u(uu, L=L):
        return tau_of_m(2 * L ** 2 / (uu + L ** 2))
    num = mp.diff(tau_of_u, u)
    m = 2 * L ** 2 / (u + L ** 2)
    K = mp.ellipk(m)
    closed = 1j * mp.pi / (4 * (u + L ** 2) * (1 - m) * K ** 2)
    r = abs(num - closed)
    check(f"d tau/du         u={mp.nstr(u, 4)} L={mp.nstr(L, 4)}",
          r < mp.mpf(10) ** (-20), f"res={mp.nstr(r, 3)}")

print("=== R: u tau'(u) -> i/pi (lambda-normalization), O(1/u) rate ===")
L = mp.mpc(1, 0)
target = 1j / mp.pi
prev = None
for expo in (3, 5, 7, 9):
    u = mp.mpf(10) ** expo
    m = 2 * L ** 2 / (u + L ** 2)
    K = mp.ellipk(m)
    val = u * (1j * mp.pi / (4 * (u + L ** 2) * (1 - m) * K ** 2))
    r = abs(val - target)
    # O(1/u): residual comfortably below 10^(-expo+2)
    check(f"u tau' vs i/pi   u=1e{expo}", r < mp.mpf(10) ** (-expo + 2),
          f"res={mp.nstr(r, 3)}")
    if prev is not None:
        # rate check: residual falls ~ 100x per two decades
        check(f"O(1/u) rate      u=1e{expo}", r < prev / 50,
              f"prev={mp.nstr(prev, 3)}")
    prev = r
# off-axis approach within the chart (u along a complex ray)
for expo in (4, 8):
    u = mp.mpf(10) ** expo * mp.e ** (1j * mp.pi / 5)
    m = 2 * L ** 2 / (u + L ** 2)
    K = mp.ellipk(m)
    val = u * (1j * mp.pi / (4 * (u + L ** 2) * (1 - m) * K ** 2))
    r = abs(val - target)
    check(f"u tau' cplx ray  |u|=1e{expo}", r < mp.mpf(10) ** (-expo + 2),
          f"res={mp.nstr(r, 3)}")

print("=== R': cross-check the closed form against direct numerical u tau'(u) ===")
for expo in (3, 6):
    u = mp.mpf(10) ** expo
    def tau_of_u(uu, L=L):
        return tau_of_m(2 * L ** 2 / (uu + L ** 2))
    num = u * mp.diff(tau_of_u, u)
    r = abs(num - target)
    check(f"direct u tau'    u=1e{expo}", r < mp.mpf(10) ** (-expo + 2),
          f"res={mp.nstr(r, 3)}")

ok = all(r[1] for r in results)
npass = sum(1 for r in results if r[1])
print(f"\n=== {'ALL PASS' if ok else 'FAILURES PRESENT'} : "
      f"{npass}/{len(results)} checks, dps={mp.mp.dps} ===")
raise SystemExit(0 if ok else 1)
