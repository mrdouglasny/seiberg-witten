/-
# Genus-1 Seiberg–Witten periods, explicitly, on pure Mathlib

The reachable route to discharging the rank-1 `PeriodLayer` (`audit/GENUS1_PERIODS_PLAN.md`):
build the SU(2) periods as explicit elliptic integrals on **pure Mathlib** — no
`jacobian-challenge`/`jacobian-claude` dependency, no abstract de Rham / Gauss–Manin layer. This
file lays down **G0/G1** (the curve, the `dx/y` integrand), the concrete objects the period
construction integrates; holomorphy (G2), Picard–Fuchs (G3), and monodromy (G5) build on
`Physics/PeriodVariationProbe.lean` and the repo's modular-`λ` machinery — see the plan doc.
-/
import SeibergWitten.Physics.SWFamily
import Mathlib

namespace SeibergWitten.Physics

open Polynomial Complex

/-- **G0 — the SU(2) fibre equation.** `y²` as a function of the modulus `u` and the fibre
coordinate `x`: the Seiberg–Witten curve `y² = (x²−u)² − Λ⁴`. Same data as `swQuartic`, evaluated. -/
noncomputable def swCurveValue (Λ u x : ℂ) : ℂ := (x ^ 2 - u) ^ 2 - Λ ^ 4

/-- The fibre equation is the evaluation of the curve polynomial `swQuartic` (ties G0 to
`SWFamily`). -/
@[simp] theorem swCurveValue_eq_swQuartic (Λ u x : ℂ) :
    swCurveValue Λ u x = (swQuartic Λ u).eval x := by
  simp [swCurveValue, swQuartic]

/-- The fibre equation factors at the four branch points `x² = u ± Λ²`. -/
theorem swCurveValue_eq_factored (Λ u x : ℂ) :
    swCurveValue Λ u x = (x ^ 2 - (u + Λ ^ 2)) * (x ^ 2 - (u - Λ ^ 2)) := by
  simp only [swCurveValue]; ring

/-- **G1 — the `dx/y` integrand.** The holomorphic-differential integrand `1/y = (y²)^(−1/2)`,
whose period `∮ swOmegaIntegrand` is (up to normalization) `a'(u)`. -/
noncomputable def swOmegaIntegrand (Λ u x : ℂ) : ℂ := (swCurveValue Λ u x) ^ (-(2 : ℂ)⁻¹)

/-- The fibre equation is entire in the modulus `u` (a polynomial in `u`) — a G1/G2 building
block for differentiating the period under the integral sign. -/
theorem swCurveValue_differentiable_modulus (Λ x : ℂ) :
    Differentiable ℂ (fun u => swCurveValue Λ u x) := by
  unfold swCurveValue; fun_prop

/-- The fibre equation is entire in the fibre coordinate `x`. -/
theorem swCurveValue_differentiable_fibre (Λ u : ℂ) :
    Differentiable ℂ (fun x => swCurveValue Λ u x) := by
  unfold swCurveValue; fun_prop

end SeibergWitten.Physics
