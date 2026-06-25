#!/usr/bin/env python3
"""Independent numerical oracle for the SU(2) Seiberg–Witten formalization.

Per formalization-assurance/NUMERICAL_VALIDATION.md: instantiate the formalized
statements at sampled points and evaluate both sides with an independent engine
(mpmath / numpy here — shares no provenance with the Lean). A pass is *necessary,
not sufficient* (blind to logical-structure/vacuity bugs); it catches the
sign/constant/normalization/convention bugs the kernel cannot see.

Covers:
  * the AXIOMS being numerically vetted —
      AX_jacobi_quartic   θ₃⁴ = θ₂⁴ + θ₄⁴
      AX_theta3_ne_zero   θ₃ ≠ 0 on ℍ            (partial: sampled points)
  * the PROVED theorems being fidelity-checked (did we state them right?) —
      theta{2,3}_neg_inv  via the λ S-law below
      oneMinusLambda      1 − λ = θ₄⁴/θ₃⁴
      modularLambda_add_two   λ(τ+2)   = λ(τ)
      modularLambda_S         λ(-1/τ)  = 1 − λ(τ)
      modularLambda_ST2S      λ(-1/(-1/τ+2)) = λ(τ)
  * the convention anchor λ(i) = 1/2 (pins θ-null normalization)
  * su2_singular_locus: (x²−u)²−Λ⁴ has a repeated root iff u ∈ {±Λ²}

The θ-nulls are defined to match the Lean (Mathlib jacobiTheta₂ convention,
nome q = exp(πiτ)):
  θ₃ = Σ qⁿ²,  θ₄ = Σ (−1)ⁿ qⁿ²,  θ₂ = Σ q^((n+½)²),  λ = θ₂⁴/θ₃⁴.
"""
import mpmath as mp
import numpy as np

mp.mp.dps = 40
TOL = mp.mpf(10) ** (-25)
N = 90  # series cutoff; q^{n²} decays super-geometrically for Im τ ≳ 0.2

# Each term is a single-valued exp of the FULL argument πiτ·k — NOT q^k with a reduced
# nome q=exp(πiτ), which would route the half-integer power of θ₂ through a principal
# fractional power and pick the wrong branch at transformed arguments.
def theta3(tau):
    return mp.fsum(mp.e ** (mp.pi * 1j * tau * (n * n)) for n in range(-N, N + 1))

def theta4(tau):
    return mp.fsum((-1) ** n * mp.e ** (mp.pi * 1j * tau * (n * n)) for n in range(-N, N + 1))

def theta2(tau):
    return mp.fsum(mp.e ** (mp.pi * 1j * tau * (n + mp.mpf(1) / 2) ** 2)
                   for n in range(-N, N + 1))

def lam(tau):
    return theta2(tau) ** 4 / theta3(tau) ** 4

# High-precision sample points in ℍ. (Double-precision inputs would limit the
# transformation-law residuals to ~1e-16 — the transformed args -1/τ, τ+2 inherit the
# input error — even though the identities are exact; mpc inputs expose full precision.)
SAMPLES = [mp.mpc(0, 1), mp.mpc(0, 2), mp.mpc('0.5', '1'), mp.mpc('-0.3', '0.8'),
           mp.mpc('0.25', '0.6'), mp.mpc('1.3', '1.7')]

results = []
def check(name, cond, detail=""):
    results.append((name, bool(cond), detail))
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")

print("=== θ-null identities and λ transformation laws (mpmath, dps=40) ===")
for tau in SAMPLES:
    t2, t3, t4 = theta2(tau), theta3(tau), theta4(tau)
    L = lam(tau)
    print(f"\nτ = {complex(tau)}")
    check("AX_jacobi_quartic  θ₃⁴=θ₂⁴+θ₄⁴", abs(t3**4 - (t2**4 + t4**4)) < TOL,
          f"|resid|={mp.nstr(abs(t3**4-(t2**4+t4**4)),3)}")
    check("AX_theta3_ne_zero  θ₃≠0", abs(t3) > mp.mpf(10)**(-6),
          f"|θ₃|={mp.nstr(abs(t3),5)}")
    check("oneMinusLambda  1−λ=θ₄⁴/θ₃⁴", abs((1 - L) - t4**4 / t3**4) < TOL)
    check("modularLambda_add_two  λ(τ+2)=λ(τ)", abs(lam(tau + 2) - L) < TOL)
    check("modularLambda_S  λ(-1/τ)=1−λ(τ)", abs(lam(-1 / tau) - (1 - L)) < TOL)
    check("modularLambda_ST2S  λ(-1/(-1/τ+2))=λ(τ)",
          abs(lam(-1 / (-1 / tau + 2)) - L) < TOL)

print("\n=== convention anchor: λ(i) = 1/2 ===")
check("λ(i)=1/2 (θ-null normalization)", abs(lam(mp.mpc(0, 1)) - mp.mpf(1) / 2) < TOL,
      f"λ(i)={mp.nstr(lam(mp.mpc(0, 1)), 8)}")

print("\n=== su2_singular_locus: (x²−u)²−Λ⁴ repeated root ⟺ u=±Λ² ===")
def min_root_gap(u, Lam=1.0):
    # quartic in x: x⁴ − 2u x² + (u²−Λ⁴)
    r = np.roots([1.0, 0.0, -2.0 * u, 0.0, u * u - Lam**4])
    return min(abs(a - b) for i, a in enumerate(r) for b in r[i + 1:])

for u in [1.0, -1.0, 1.0001, 0.5, 0.0, 2.0, -1.5]:
    gap = min_root_gap(u)
    singular = gap < 1e-6
    expected = (abs(u - 1.0) < 1e-9) or (abs(u + 1.0) < 1e-9)
    check(f"u={u:+.4f}: singular={singular} (expect {expected})",
          singular == expected, f"min root gap={gap:.2e}")

ok = all(r[1] for r in results)
print(f"\n=== {'ALL PASS' if ok else 'FAILURES PRESENT'} : "
      f"{sum(r[1] for r in results)}/{len(results)} checks ===")
exit(0 if ok else 1)
