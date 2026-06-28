/-
Reproducible check backing `audit/SU2_MATTER_PLAN.md` (the SU(2)-with-matter / Argyres–Douglas plan).

Both identities close by `ring` (run: `lake env lean audit/su2_matter_ad_check.lean`; clean = both ✓):

1. The N_f=1 SU(2) Argyres–Douglas point (the (A₁,A₂) theory). With the matter curve
   Q(x) = (x²−u)² − Λ³(x−m), at the tuned point (u,m) = (¾Λ², −¾Λ), Q acquires a TRIPLE root at
   x = −Λ/2 — the cusp y² ~ (x+Λ/2)³, i.e. two singularities of the u-plane colliding (an AD point).

2. Contrast: pure SU(2), Q = (x²−u)² − Λ⁴, splits into two DISTINCT quadratics, so for Λ ≠ 0 its
   only x-collisions are simple double roots (u = ±Λ²) — never a triple root, hence no AD point.
-/
import Mathlib

example (Λ x : ℂ) :
    (x^2 - (3/4)*Λ^2)^2 - Λ^3 * (x - (-(3/4)*Λ))
      = (x + (1/2)*Λ)^3 * (x - (3/2)*Λ) := by ring

example (Λ u x : ℂ) :
    (x^2 - u)^2 - Λ^4 = (x^2 - (u + Λ^2)) * (x^2 - (u - Λ^2)) := by ring
