#!/usr/bin/env python3
"""Numeric oracle for the cusp-data campaign, step A (CuspData.lean).

Pins the lambda-frame monodromy conventions:
  M_weak = -T^{-2} = [[-1,2],[0,-1]]   (tau -> tau-2, with the Weyl -1)
  M_mono = S T^{2} S^{-1} = [[1,0],[-2,1]]      (tau -> tau/(1 - 2 tau), fixes cusp 0)
  M_dyon = M_mono^{-1} M_weak = [[-1,2],[-2,3]] (tau -> (-tau+2)/(-2 tau+3), fixes cusp 1)

  A. dets = 1; all three == I mod 2 (so in Gamma(2) itself: -I is in Gamma(2));
     M_mono * M_dyon = M_weak.
  B. lambda(M tau) = lambda(tau) for all three, at random H points, 40 digits
     (lambda = theta2^4/theta3^4, nome q = e^{i pi tau}).
  C. width-2 convention: lambda(tau)/(16 e^{i pi tau}) -> 1 as Im tau grows.
  D. im positivity of the three Moebius images on H.
"""
import mpmath as mp
import random

mp.mp.dps = 40
TOL = mp.mpf(10) ** (-30)
checks = []

def check(name, ok, detail=""):
    checks.append((name, ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))

def lam(tau):
    q = mp.exp(1j * mp.pi * tau)
    return (mp.jtheta(2, 0, q) / mp.jtheta(3, 0, q)) ** 4

MW = [[-1, 2], [0, -1]]
MM = [[1, 0], [-2, 1]]
MD = [[-1, 2], [-2, 3]]

def mmul(A, B):
    return [[A[0][0]*B[0][0]+A[0][1]*B[1][0], A[0][0]*B[0][1]+A[0][1]*B[1][1]],
            [A[1][0]*B[0][0]+A[1][1]*B[1][0], A[1][0]*B[0][1]+A[1][1]*B[1][1]]]

def act(M, t):
    return (M[0][0]*t + M[0][1]) / (M[1][0]*t + M[1][1])

print("A. matrix arithmetic (incl. PARABOLICITY - the check that caught the v1 bug)")
for nm, M in [("M_weak", MW), ("M_mono", MM), ("M_dyon", MD)]:
    check(f"A1 det {nm} = 1", M[0][0]*M[1][1] - M[0][1]*M[1][0] == 1)
    check(f"A2 {nm} == I mod 2", all((M[i][j] - (1 if i == j else 0)) % 2 == 0
                                     for i in range(2) for j in range(2)))
check("A3 M_mono * M_dyon = M_weak", mmul(MM, MD) == MW)
for nm, M in [("M_weak", MW), ("M_mono", MM), ("M_dyon", MD)]:
    check(f"A4 {nm} parabolic (|trace| = 2)", abs(M[0][0] + M[1][1]) == 2)
# fixed cusps: monopole fixes 0 (lambda-value 1), dyon fixes 1 (lambda-value infinity)
check("A5 M_mono fixes tau = 0", MM[0][1] == 0)
check("A6 M_dyon fixes tau = 1",
      MD[0][0]*1 + MD[0][1] == (MD[1][0]*1 + MD[1][1]) * 1)

print("B. lambda-invariance at random H points")
random.seed(11)
pts = [mp.mpc(random.uniform(-2, 2), random.uniform(0.4, 2.0)) for _ in range(4)]
for nm, M in [("M_weak", MW), ("M_mono", MM), ("M_dyon", MD)]:
    err = max(abs(lam(act(M, t)) - lam(t)) for t in pts)
    check(f"B1 lambda({nm} tau) = lambda(tau)", err < TOL, f"max err {mp.nstr(err, 3)}")

print("C. width-2 convention")
t = mp.mpc("0.3", "12")
check("C1 lambda(tau) ~ 16 e^{i pi tau}", abs(lam(t) / (16 * mp.exp(1j*mp.pi*t)) - 1) < 1e-15)

print("D. im positivity of images")
for nm, M in [("M_weak", MW), ("M_mono", MM), ("M_dyon", MD)]:
    check(f"D1 Im({nm} tau) > 0", all(act(M, t).imag > 0 for t in pts))

npass = sum(1 for _, ok in checks if ok)
print(f"\n{npass}/{len(checks)} checks passed" + ("" if npass == len(checks) else "  *** FAILURES ***"))
raise SystemExit(0 if npass == len(checks) else 1)
