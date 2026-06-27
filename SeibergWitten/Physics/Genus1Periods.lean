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

/-- **G2 domination ingredient — the integrand norm.** `‖(y²)^(−1/2)‖ = ‖y²‖^(−1/2)` (real
`rpow`), unconditionally. Lower-bounding `‖y²‖` away from `0` on a compact contour-neighbourhood
then bounds the integrand, the integrable bound the dominated-derivative lemma needs for G2. -/
theorem swOmegaIntegrand_norm (Λ u x : ℂ) :
    ‖swOmegaIntegrand Λ u x‖ = ‖swCurveValue Λ u x‖ ^ (-(2⁻¹) : ℝ) := by
  rw [swOmegaIntegrand, show (-(2 : ℂ)⁻¹) = (((-(2⁻¹) : ℝ)) : ℂ) by push_cast; ring]
  exact Complex.norm_cpow_real _ _

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

/-- **G2 integrability ingredient.** The `dx/y` integrand is continuous in the fibre coordinate at
any point off the branch cut (`y² ∈ slitPlane`). Over a contour that stays off the cut this gives
continuity ⇒ interval-integrability of the integrand and its `u`-derivative — the measurability /
`IntervalIntegrable` hypotheses the dominated-derivative lemma needs. -/
theorem swOmegaIntegrand_continuousAt_fibre (Λ u x₀ : ℂ)
    (h : swCurveValue Λ u x₀ ∈ Complex.slitPlane) :
    ContinuousAt (fun x => swOmegaIntegrand Λ u x) x₀ :=
  (continuousAt_cpow_const h).comp
    (swCurveValue_differentiable_fibre Λ u).continuous.continuousAt

/-- **G2 domination integrand — the norm of `∂(dx/y)/∂u`.** `‖∂/∂u (y²)^(−1/2)‖ =
‖x²−u‖·‖y²‖^(−3/2)`. With `‖y²‖` bounded below off the branch cut and `‖x²−u‖` bounded above on a
compact contour-neighbourhood, this is the integrable bound `hasDerivAt_integral_of_dominated_…`
consumes — the last ingredient before the period-integral holomorphy assembly. -/
theorem swOmegaIntegrand_deriv_norm (Λ x u₀ : ℂ) :
    ‖(-(2 : ℂ)⁻¹) * (swCurveValue Λ u₀ x) ^ ((-(2 : ℂ)⁻¹) - 1) * (-(2 * (x ^ 2 - u₀)))‖
      = ‖x ^ 2 - u₀‖ * ‖swCurveValue Λ u₀ x‖ ^ (-(3 / 2) : ℝ) := by
  rw [show ((-(2 : ℂ)⁻¹) - 1) = (((-(3 / 2) : ℝ)) : ℂ) by push_cast; ring]
  simp only [norm_mul, norm_neg, norm_inv, Complex.norm_cpow_real, Complex.norm_ofNat]
  ring

/-- **G2 assembly block — segment continuity.** Along a real contour `[a,b]` that stays off the
branch cut (`y² ∈ slitPlane` throughout), the `dx/y` integrand is continuous in the contour
parameter `t` (composing the fibre continuity with `ℝ ↪ ℂ`). -/
theorem swOmegaIntegrand_continuousOn_segment (Λ u : ℂ) (a b : ℝ)
    (hmem : ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane) :
    ContinuousOn (fun t : ℝ => swOmegaIntegrand Λ u (t : ℂ)) (Set.uIcc a b) :=
  fun t ht => ((swOmegaIntegrand_continuousAt_fibre Λ u (t : ℂ) (hmem t ht)).comp
    Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-- **G2 assembly block — interval-integrability.** Hence the integrand is interval-integrable on a
contour off the cut — the `hF_int` hypothesis of `hasDerivAt_integral_of_dominated_…`. -/
theorem swOmegaIntegrand_intervalIntegrable (Λ u : ℂ) (a b : ℝ)
    (hmem : ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ => swOmegaIntegrand Λ u (t : ℂ)) MeasureTheory.volume a b :=
  (swOmegaIntegrand_continuousOn_segment Λ u a b hmem).intervalIntegrable

end SeibergWitten.Physics
