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

/-- The explicit modulus-derivative of the fibre equation: `∂/∂u (x²−u)² = −2(x²−u)`. -/
theorem swCurveValue_hasDerivAt_modulus (Λ x u₀ : ℂ) :
    HasDerivAt (fun u => swCurveValue Λ u x) (-(2 * (x ^ 2 - u₀))) u₀ := by
  have h : HasDerivAt (fun u : ℂ => x ^ 2 - u) (-1) u₀ := by
    simpa using (hasDerivAt_id u₀).const_sub (x ^ 2)
  have h2 := (h.pow 2).sub_const (Λ ^ 4)
  simp only [swCurveValue]
  convert h2 using 1
  push_cast; ring

/-- **G2, per-`x` ingredient.** The `dx/y` integrand is holomorphic in the modulus `u` at any `u₀`
where the fibre value `y²` lies off the branch cut of `(·)^(−1/2)` (the slit plane `ℂ ∖ (−∞,0]`) —
the per-fibre-coordinate input to differentiating the period `∮` under the integral sign (the
remaining G2 work being the integrable `√`-singularity at the branch points). -/
theorem swOmegaIntegrand_differentiableAt_modulus (Λ x u₀ : ℂ)
    (h : swCurveValue Λ u₀ x ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun u => swOmegaIntegrand Λ u x) u₀ :=
  ((swCurveValue_differentiable_modulus Λ x).differentiableAt).cpow_const h

/-- **G2/G3 ingredient — the explicit modulus-derivative of the `dx/y` integrand.** Off the branch
cut, `∂/∂u (y²)^(−1/2) = (−1/2)(y²)^(−3/2)·(−2(x²−u))`. This is the integrand whose contour integral
is `∂a/∂u` (the holomorphic-differential period) and whose bound discharges G2's domination; the
chain-rule shape feeds the G3 Picard–Fuchs derivation. -/
theorem swOmegaIntegrand_hasDerivAt_modulus (Λ x u₀ : ℂ)
    (h : swCurveValue Λ u₀ x ∈ Complex.slitPlane) :
    HasDerivAt (fun u => swOmegaIntegrand Λ u x)
      ((-(2 : ℂ)⁻¹) * (swCurveValue Λ u₀ x) ^ ((-(2 : ℂ)⁻¹) - 1) * (-(2 * (x ^ 2 - u₀)))) u₀ := by
  simpa only [swOmegaIntegrand] using (swCurveValue_hasDerivAt_modulus Λ x u₀).cpow_const h

end SeibergWitten.Physics
