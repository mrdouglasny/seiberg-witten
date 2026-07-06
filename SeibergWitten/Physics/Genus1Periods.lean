/-
# Genus-1 Seiberg–Witten periods, explicitly, on pure Mathlib

The reachable route to discharging the rank-1 `PeriodLayer` (`audit/GENUS1_PERIODS_PLAN.md`):
build the SU(2) periods as explicit elliptic integrals on **pure Mathlib** — no
`jacobian-challenge`/`jacobian-claude` dependency, no abstract de Rham / Gauss–Manin layer. This
file lays down **G0/G1** (the curve, the `dx/y` integrand), the concrete objects the period
construction integrates; holomorphy (G2), Picard–Fuchs (G3), and monodromy (G5) build on
`Physics/PeriodVariationProbe.lean` and the repo's modular-`λ` machinery — see the plan doc.
-/
import Mathlib

namespace SeibergWitten.Physics

open Polynomial Complex

/-- **G0 — the SU(2) fibre equation.** `y²` as a function of the modulus `u` and the fibre
coordinate `x`: the Seiberg–Witten curve `y² = (x²−u)² − Λ⁴` (same data as `swQuartic`,
evaluated). -/
noncomputable def swCurveValue (Λ u x : ℂ) : ℂ := (x ^ 2 - u) ^ 2 - Λ ^ 4

/-- The genus-one SW curve polynomial `(x²−u)² − Λ⁴` (relocated from the former
`SWFamily` layer with the jacobian-challenge decoupling; the hyperelliptic-data
packaging lives, unbuilt, in `HigherGenus/SWFamily.lean`). -/
noncomputable def swQuartic (Λ u : ℂ) : Polynomial ℂ := (X ^ 2 - C u) ^ 2 - C (Λ ^ 4)

@[simp] theorem swQuartic_natDegree (Λ u : ℂ) : (swQuartic Λ u).natDegree = 4 := by
  unfold swQuartic
  compute_degree!

/-- The fibre equation is the evaluation of the curve polynomial `swQuartic` (ties G0 to
`SWFamily`). -/
@[simp] theorem swCurveValue_eq_swQuartic (Λ u x : ℂ) :
    swCurveValue Λ u x = (swQuartic Λ u).eval x := by
  simp [swCurveValue, swQuartic]

/-- The fibre equation factors at the four branch points `x² = u ± Λ²`. -/
theorem swCurveValue_eq_factored (Λ u x : ℂ) :
    swCurveValue Λ u x = (x ^ 2 - (u + Λ ^ 2)) * (x ^ 2 - (u - Λ ^ 2)) := by
  simp only [swCurveValue]; ring

/-- **G0 — the branch locus.** `y² = 0` exactly at the branch points `x² = u ± Λ²`; off these
points the fibre is smooth. The contour-off-cut hypotheses of the period lemmas (and the G5
monodromy around `u = ±Λ²`) are about staying away from this locus. -/
theorem swCurveValue_eq_zero_iff (Λ u x : ℂ) :
    swCurveValue Λ u x = 0 ↔ x ^ 2 = u + Λ ^ 2 ∨ x ^ 2 = u - Λ ^ 2 := by
  rw [swCurveValue_eq_factored, mul_eq_zero, sub_eq_zero, sub_eq_zero]

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

/-- **G3 ingredient — the explicit second `u`-derivative of the integrand.**
`∂²/∂u² (y²)^(−1/2) = 3(x²−u)²(y²)^(−5/2) − (y²)^(−3/2)` off the branch cut. (Here the function
differentiated is the first-derivative integrand `(−1/2)(y²)^(−3/2)(−2(x²−u))`.) Feeds the
period's second derivative and the Picard–Fuchs ODE identity. -/
theorem swOmegaIntegrand_hasDeriv2_modulus (Λ x u₀ : ℂ)
    (h : swCurveValue Λ u₀ x ∈ Complex.slitPlane) :
    HasDerivAt
      (fun u => (-(2 : ℂ)⁻¹) * (swCurveValue Λ u x) ^ ((-(2 : ℂ)⁻¹) - 1) * (-(2 * (x ^ 2 - u))))
      (3 * (x ^ 2 - u₀) ^ 2 * (swCurveValue Λ u₀ x) ^ (-(5 : ℂ) / 2)
        - (swCurveValue Λ u₀ x) ^ (-(3 : ℂ) / 2)) u₀ := by
  have hsv := swCurveValue_hasDerivAt_modulus Λ x u₀
  have hP : HasDerivAt (fun u => (swCurveValue Λ u x) ^ ((-(2 : ℂ)⁻¹) - 1))
      (((-(2 : ℂ)⁻¹) - 1) * (swCurveValue Λ u₀ x) ^ (((-(2 : ℂ)⁻¹) - 1) - 1) *
        (-(2 * (x ^ 2 - u₀)))) u₀ := hsv.cpow_const h
  have hQ : HasDerivAt (fun u : ℂ => -(2 * (x ^ 2 - u))) 2 u₀ := by
    have h1 : HasDerivAt (fun u : ℂ => x ^ 2 - u) (-1) u₀ := by
      simpa using (hasDerivAt_id u₀).const_sub (x ^ 2)
    convert (h1.const_mul (2 : ℂ)).neg using 1
    norm_num
  have key := (hP.const_mul (-(2 : ℂ)⁻¹)).mul hQ
  rw [show (((-(2 : ℂ)⁻¹) - 1) - 1) = (-(5 : ℂ) / 2) by norm_num,
      show ((-(2 : ℂ)⁻¹) - 1) = (-(3 : ℂ) / 2) by norm_num] at key
  convert key using 1
  · funext u; simp only [Pi.mul_apply]; ring
  · ring

/-- **G3 ingredient — the integrand is twice `u`-differentiable.** The first `u`-derivative
integrand `(−1/2)(y²)^(−3/2)(−2(x²−u))` is itself differentiable in `u` off the branch cut — so
the period's second `u`-derivative exists (the input to the Picard–Fuchs derivation). -/
theorem swOmegaDerivIntegrand_differentiableAt_modulus (Λ x u₀ : ℂ)
    (h : swCurveValue Λ u₀ x ∈ Complex.slitPlane) :
    DifferentiableAt ℂ
      (fun u => (-(2 : ℂ)⁻¹) * (swCurveValue Λ u x) ^ ((-(2 : ℂ)⁻¹) - 1) *
        (-(2 * (x ^ 2 - u)))) u₀ := by
  apply DifferentiableAt.mul
  · exact (((swCurveValue_differentiable_modulus Λ x).differentiableAt).cpow_const h).const_mul _
  · fun_prop

/-- **G2 assembly block — derivative-integrand continuity.** The `u`-derivative integrand
`(−1/2)(y²)^(−3/2)(−2(x²−u))` is continuous along an off-cut contour — the `hF'_meas` source for
the dominated-derivative lemma (the last measurability hypothesis of the period-holomorphy
assembly). -/
theorem swOmegaDerivIntegrand_continuousOn_segment (Λ u : ℂ) (a b : ℝ)
    (hmem : ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane) :
    ContinuousOn (fun t : ℝ =>
        (-(2 : ℂ)⁻¹) * (swCurveValue Λ u (t : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1) *
          (-(2 * ((t : ℂ) ^ 2 - u)))) (Set.uIcc a b) := by
  intro t ht
  have hsv : ContinuousAt (fun s : ℝ => swCurveValue Λ u (s : ℂ)) t :=
    (swCurveValue_differentiable_fibre Λ u).continuous.continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have hcpow : ContinuousAt
      (fun s : ℝ => (swCurveValue Λ u (s : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1)) t :=
    hsv.cpow continuousAt_const (hmem t ht)
  have hpoly : ContinuousAt (fun s : ℝ => (-(2 * ((s : ℂ) ^ 2 - u)))) t := by fun_prop
  exact ((continuousAt_const.mul hcpow).mul hpoly).continuousWithinAt

/-- **G3 assembly block — derivative-integrand integrability.** The first `u`-derivative integrand
is interval-integrable on an off-cut contour — the `hF_int` hypothesis for the *second*-derivative
assembly (the period twice-differentiable, toward Picard–Fuchs). -/
theorem swOmegaDerivIntegrand_intervalIntegrable (Λ u : ℂ) (a b : ℝ)
    (hmem : ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ =>
        (-(2 : ℂ)⁻¹) * (swCurveValue Λ u (t : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1) *
          (-(2 * ((t : ℂ) ^ 2 - u)))) MeasureTheory.volume a b :=
  (swOmegaDerivIntegrand_continuousOn_segment Λ u a b hmem).intervalIntegrable

/-- **G3 assembly block — second-derivative-integrand continuity.** The integrand
`3(x²−u)²(y²)^(−5/2) − (y²)^(−3/2)` is continuous along an off-cut contour — the `hF'_meas` source
for the second-derivative assembly. -/
theorem swOmega2Integrand_continuousOn_segment (Λ u : ℂ) (a b : ℝ)
    (hmem : ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane) :
    ContinuousOn (fun t : ℝ =>
        3 * ((t : ℂ) ^ 2 - u) ^ 2 * (swCurveValue Λ u (t : ℂ)) ^ (-(5 : ℂ) / 2)
          - (swCurveValue Λ u (t : ℂ)) ^ (-(3 : ℂ) / 2)) (Set.uIcc a b) := by
  intro t ht
  have hsv : ContinuousAt (fun s : ℝ => swCurveValue Λ u (s : ℂ)) t :=
    (swCurveValue_differentiable_fibre Λ u).continuous.continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have h5 : ContinuousAt (fun s : ℝ => (swCurveValue Λ u (s : ℂ)) ^ (-(5 : ℂ) / 2)) t :=
    hsv.cpow continuousAt_const (hmem t ht)
  have h3 : ContinuousAt (fun s : ℝ => (swCurveValue Λ u (s : ℂ)) ^ (-(3 : ℂ) / 2)) t :=
    hsv.cpow continuousAt_const (hmem t ht)
  have hpoly : ContinuousAt (fun s : ℝ => 3 * ((s : ℂ) ^ 2 - u) ^ 2) t := by fun_prop
  exact ((hpoly.mul h5).sub h3).continuousWithinAt

/-- **G3 assembly block — second-derivative-integrand integrability.** Hence it is
interval-integrable on an off-cut contour (`hF_int` for the second-derivative assembly). -/
theorem swOmega2Integrand_intervalIntegrable (Λ u : ℂ) (a b : ℝ)
    (hmem : ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ =>
        3 * ((t : ℂ) ^ 2 - u) ^ 2 * (swCurveValue Λ u (t : ℂ)) ^ (-(5 : ℂ) / 2)
          - (swCurveValue Λ u (t : ℂ)) ^ (-(3 : ℂ) / 2)) MeasureTheory.volume a b :=
  (swOmega2Integrand_continuousOn_segment Λ u a b hmem).intervalIntegrable

/-- The genus-1 SW period over a real contour `[a,b]`: the holomorphic-differential period
`∫_a^b dx/y` (`= ∂a/∂u` up to normalization). The named object the period layer's holomorphy,
Picard–Fuchs (G3), and monodromy (G5) statements refer to. -/
noncomputable def swPeriodSeg (Λ : ℂ) (a b : ℝ) (u : ℂ) : ℂ :=
  ∫ t in a..b, swOmegaIntegrand Λ u (t : ℂ)

/-- **G2 — the period is holomorphic in the modulus (assembly).** Over a real contour `[a,b]` that
stays off the branch cut on a neighbourhood `s` of `u₀` (`hmem`), with the `u`-derivative integrand
dominated by an integrable `bound` (`hbd`), the period `u ↦ ∫_a^b (dx/y)` has the expected complex
derivative `∫_a^b ∂/∂u (dx/y)` — differentiation under the integral sign. All hypotheses are
discharged by the per-`x` helpers above through Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` (same engine as `model_period_differentiable`).
This is P1 for the genus-1 SW period along an off-cut contour; the remaining G2 piece is the
integrable `√`-singularity when the contour ends at branch points. -/
theorem swPeriodSeg_hasDerivAt (Λ : ℂ) (a b : ℝ) {u₀ : ℂ} {s : Set ℂ} (hs : s ∈ nhds u₀)
    (hmem : ∀ u ∈ s, ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane)
    (bound : ℝ → ℝ) (hbound_int : IntervalIntegrable bound MeasureTheory.volume a b)
    (hbd : ∀ t ∈ Set.uIoc a b, ∀ u ∈ s,
      ‖(-(2 : ℂ)⁻¹) * (swCurveValue Λ u (t : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1) *
          (-(2 * ((t : ℂ) ^ 2 - u)))‖ ≤ bound t) :
    HasDerivAt (swPeriodSeg Λ a b)
      (∫ t in a..b, (-(2 : ℂ)⁻¹) * (swCurveValue Λ u₀ (t : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1) *
          (-(2 * ((t : ℂ) ^ 2 - u₀)))) u₀ := by
  unfold swPeriodSeg
  have hu₀ : u₀ ∈ s := mem_of_mem_nhds hs
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (u : ℂ) (t : ℝ) => swOmegaIntegrand Λ u (t : ℂ))
    (F' := fun (u : ℂ) (t : ℝ) => (-(2 : ℂ)⁻¹) * (swCurveValue Λ u (t : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1) *
        (-(2 * ((t : ℂ) ^ 2 - u)))) (bound := bound) hs ?_ ?_ ?_ ?_ hbound_int ?_).2
  · exact Filter.eventually_of_mem hs fun u hu =>
      ((swOmegaIntegrand_continuousOn_segment Λ u a b (hmem u hu)).mono
        Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact swOmegaIntegrand_intervalIntegrable Λ u₀ a b (hmem u₀ hu₀)
  · exact ((swOmegaDerivIntegrand_continuousOn_segment Λ u₀ a b (hmem u₀ hu₀)).mono
      Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact MeasureTheory.ae_of_all _ fun t ht u hu => hbd t ht u hu
  · exact MeasureTheory.ae_of_all _ fun t ht u hu =>
      swOmegaIntegrand_hasDerivAt_modulus Λ (t : ℂ) u (hmem u hu t (Set.uIoc_subset_uIcc ht))

/-- **G2 — the off-cut period is holomorphic in the modulus** (`DifferentiableAt` packaging of
`swPeriodSeg_hasDerivAt`). -/
theorem swPeriodSeg_differentiableAt (Λ : ℂ) (a b : ℝ) {u₀ : ℂ} {s : Set ℂ} (hs : s ∈ nhds u₀)
    (hmem : ∀ u ∈ s, ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane)
    (bound : ℝ → ℝ) (hbound_int : IntervalIntegrable bound MeasureTheory.volume a b)
    (hbd : ∀ t ∈ Set.uIoc a b, ∀ u ∈ s,
      ‖(-(2 : ℂ)⁻¹) * (swCurveValue Λ u (t : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1) *
          (-(2 * ((t : ℂ) ^ 2 - u)))‖ ≤ bound t) :
    DifferentiableAt ℂ (swPeriodSeg Λ a b) u₀ :=
  (swPeriodSeg_hasDerivAt Λ a b hs hmem bound hbound_int hbd).differentiableAt

/-- **G3 — the period's derivative is itself differentiable (second-derivative assembly).** The
period's first-derivative function `u ↦ ∫_a^b ∂/∂u(dx/y)` has derivative `∫_a^b ∂²/∂u²(dx/y)` over
an off-cut contour with a dominated second-derivative integrand — i.e. the period is twice
holomorphic in `u`. Same dominated-derivative engine as `swPeriodSeg_hasDerivAt`, one level up,
with hypotheses discharged by the `swOmega2Integrand_*` / `swOmegaDerivIntegrand_*` helpers and the
explicit `swOmegaIntegrand_hasDeriv2_modulus`. Feeds the Picard–Fuchs ODE identity (G3). -/
theorem swPeriodSeg_deriv_hasDerivAt (Λ : ℂ) (a b : ℝ) {u₀ : ℂ} {s : Set ℂ} (hs : s ∈ nhds u₀)
    (hmem : ∀ u ∈ s, ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane)
    (bound : ℝ → ℝ) (hbound_int : IntervalIntegrable bound MeasureTheory.volume a b)
    (hbd : ∀ t ∈ Set.uIoc a b, ∀ u ∈ s,
      ‖3 * ((t : ℂ) ^ 2 - u) ^ 2 * (swCurveValue Λ u (t : ℂ)) ^ (-(5 : ℂ) / 2)
        - (swCurveValue Λ u (t : ℂ)) ^ (-(3 : ℂ) / 2)‖ ≤ bound t) :
    HasDerivAt
      (fun u => ∫ t in a..b, (-(2 : ℂ)⁻¹) * (swCurveValue Λ u (t : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1) *
        (-(2 * ((t : ℂ) ^ 2 - u))))
      (∫ t in a..b, 3 * ((t : ℂ) ^ 2 - u₀) ^ 2 * (swCurveValue Λ u₀ (t : ℂ)) ^ (-(5 : ℂ) / 2)
        - (swCurveValue Λ u₀ (t : ℂ)) ^ (-(3 : ℂ) / 2)) u₀ := by
  have hu₀ : u₀ ∈ s := mem_of_mem_nhds hs
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (u : ℂ) (t : ℝ) => (-(2 : ℂ)⁻¹) * (swCurveValue Λ u (t : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1) *
      (-(2 * ((t : ℂ) ^ 2 - u))))
    (F' := fun (u : ℂ) (t : ℝ) => 3 * ((t : ℂ) ^ 2 - u) ^ 2 *
        (swCurveValue Λ u (t : ℂ)) ^ (-(5 : ℂ) / 2) - (swCurveValue Λ u (t : ℂ)) ^ (-(3 : ℂ) / 2))
    (bound := bound) hs ?_ ?_ ?_ ?_ hbound_int ?_).2
  · exact Filter.eventually_of_mem hs fun u hu =>
      ((swOmegaDerivIntegrand_continuousOn_segment Λ u a b (hmem u hu)).mono
        Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact swOmegaDerivIntegrand_intervalIntegrable Λ u₀ a b (hmem u₀ hu₀)
  · exact ((swOmega2Integrand_continuousOn_segment Λ u₀ a b (hmem u₀ hu₀)).mono
      Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact MeasureTheory.ae_of_all _ fun t ht u hu => hbd t ht u hu
  · exact MeasureTheory.ae_of_all _ fun t ht u hu =>
      swOmegaIntegrand_hasDeriv2_modulus Λ (t : ℂ) u (hmem u hu t (Set.uIoc_subset_uIcc ht))

/-! ## R2a — the SW differential `λ_SW` and the special coordinate `a(u) = ∮ λ_SW`

The meromorphic Seiberg–Witten differential `λ_SW = x²·(dx/y)` (genus-1 / SU(2)); its `A`-period is
the special coordinate `a(u)`, and `∂a/∂u ∝ ∮ dx/y` (the holomorphic period, up to exact forms).
Built on the `swOmega*` dominated-derivative engine above with an extra polynomial factor `x²`. -/

/-- The SW differential integrand `λ_SW = x²·(dx/y) = x²·swCurveValue^{-1/2}`. -/
noncomputable def swLambdaIntegrand (Λ u x : ℂ) : ℂ := x ^ 2 * swOmegaIntegrand Λ u x

/-- `λ_SW` is continuous in the fibre coordinate on a contour off the branch cut. -/
theorem swLambdaIntegrand_continuousOn_segment (Λ u : ℂ) (a b : ℝ)
    (hmem : ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane) :
    ContinuousOn (fun t : ℝ => swLambdaIntegrand Λ u (t : ℂ)) (Set.uIcc a b) := by
  unfold swLambdaIntegrand
  exact ((Complex.continuous_ofReal.pow 2).continuousOn).mul
    (swOmegaIntegrand_continuousOn_segment Λ u a b hmem)

/-- Hence `λ_SW` is interval-integrable on a contour off the cut. -/
theorem swLambdaIntegrand_intervalIntegrable (Λ u : ℂ) (a b : ℝ)
    (hmem : ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ => swLambdaIntegrand Λ u (t : ℂ)) MeasureTheory.volume a b :=
  (swLambdaIntegrand_continuousOn_segment Λ u a b hmem).intervalIntegrable

/-- The `u`-derivative of the `λ_SW` integrand (`x²` is constant in `u`, so it scales the `dx/y`
derivative). -/
theorem swLambdaIntegrand_hasDerivAt_modulus (Λ x u₀ : ℂ)
    (h : swCurveValue Λ u₀ x ∈ Complex.slitPlane) :
    HasDerivAt (fun u => swLambdaIntegrand Λ u x)
      (x ^ 2 * ((-(2 : ℂ)⁻¹) * (swCurveValue Λ u₀ x) ^ ((-(2 : ℂ)⁻¹) - 1) *
        (-(2 * (x ^ 2 - u₀))))) u₀ := by
  simpa only [swLambdaIntegrand] using
    (swOmegaIntegrand_hasDerivAt_modulus Λ x u₀ h).const_mul (x ^ 2)

/-- **R2a — the SW special coordinate `a(u) = ∮ λ_SW`** over a real contour `[a,b]` (genus-1 /
SU(2)). The named object the period layer's special coordinate `a` refers to. -/
noncomputable def swLambdaSeg (Λ : ℂ) (a b : ℝ) (u : ℂ) : ℂ :=
  ∫ t in a..b, swLambdaIntegrand Λ u (t : ℂ)

/-- **R2a — the SW period `a(u)` is holomorphic in the modulus.** Same dominated-derivative engine
as `swPeriodSeg_hasDerivAt`, now for the `λ_SW = x²·(dx/y)` integrand: over an off-cut contour with
the
`u`-derivative integrand dominated by an integrable `bound`, `a(u)` has the expected derivative
`∮ ∂_u λ_SW`. -/
theorem swLambdaSeg_hasDerivAt (Λ : ℂ) (a b : ℝ) {u₀ : ℂ} {s : Set ℂ} (hs : s ∈ nhds u₀)
    (hmem : ∀ u ∈ s, ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane)
    (bound : ℝ → ℝ) (hbound_int : IntervalIntegrable bound MeasureTheory.volume a b)
    (hbd : ∀ t ∈ Set.uIoc a b, ∀ u ∈ s,
      ‖(t : ℂ) ^ 2 * ((-(2 : ℂ)⁻¹) * (swCurveValue Λ u (t : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1) *
          (-(2 * ((t : ℂ) ^ 2 - u))))‖ ≤ bound t) :
    HasDerivAt (swLambdaSeg Λ a b)
      (∫ t in a..b, (t : ℂ) ^ 2 * ((-(2 : ℂ)⁻¹) * (swCurveValue Λ u₀ (t : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1) *
          (-(2 * ((t : ℂ) ^ 2 - u₀))))) u₀ := by
  unfold swLambdaSeg
  have hu₀ : u₀ ∈ s := mem_of_mem_nhds hs
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (u : ℂ) (t : ℝ) => swLambdaIntegrand Λ u (t : ℂ))
    (F' := fun (u : ℂ) (t : ℝ) => (t : ℂ) ^ 2 * ((-(2 : ℂ)⁻¹) *
        (swCurveValue Λ u (t : ℂ)) ^ ((-(2 : ℂ)⁻¹) - 1) * (-(2 * ((t : ℂ) ^ 2 - u)))))
    (bound := bound) hs ?_ ?_ ?_ ?_ hbound_int ?_).2
  · exact Filter.eventually_of_mem hs fun u hu =>
      ((swLambdaIntegrand_continuousOn_segment Λ u a b (hmem u hu)).mono
        Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact swLambdaIntegrand_intervalIntegrable Λ u₀ a b (hmem u₀ hu₀)
  · exact (((Complex.continuous_ofReal.pow 2).continuousOn).mul
      (swOmegaDerivIntegrand_continuousOn_segment Λ u₀ a b (hmem u₀ hu₀))).mono
        Set.uIoc_subset_uIcc |>.aestronglyMeasurable measurableSet_uIoc
  · exact MeasureTheory.ae_of_all _ fun t ht u hu => hbd t ht u hu
  · exact MeasureTheory.ae_of_all _ fun t ht u hu =>
      swLambdaIntegrand_hasDerivAt_modulus Λ (t : ℂ) u (hmem u hu t (Set.uIoc_subset_uIcc ht))

/-! ## R2b — the special-geometry / Picard–Fuchs link via integration by parts

With `y² = swCurveValue`, `y' = 2x(x²−u)/y`, so `d/dx(−x/(2y)) = −1/(2y) + x²(x²−u)·y⁻³`. Hence the
`∂_u` integrand of `a = ∮ λ_SW`, namely `x²(x²−u)·y⁻³`, equals `½·(dx/y)` **plus an exact form**
`d/dx(−x/(2y))`. On a closed contour the exact form integrates to zero, giving the special-geometry
relation `∂a/∂u = ½ ∮ dx/y` (the holomorphic period) — the link between `swLambdaSeg` and
`swPeriodSeg` that feeds H1 (`τ = ∂a_D/∂a`). -/

/-- **R2b-i — the integration-by-parts identity** (pointwise, in the fibre coordinate `x`). The
auxiliary `−x/(2y)` has `x`-derivative `[∂_u λ_SW integrand] − ½·[dx/y integrand]`, i.e.
`x²(x²−u)·y⁻³ = ½·y⁻¹ + d/dx(−x/(2y))`. -/
theorem swLambda_ibp_hasDerivAt (Λ u x₀ : ℂ) (h : swCurveValue Λ u x₀ ∈ Complex.slitPlane) :
    HasDerivAt (fun x => -(x / 2) * swCurveValue Λ u x ^ (-(2 : ℂ)⁻¹))
      (x₀ ^ 2 * ((-(2 : ℂ)⁻¹) * swCurveValue Λ u x₀ ^ ((-(2 : ℂ)⁻¹) - 1) * (-(2 * (x₀ ^ 2 - u))))
        - (2 : ℂ)⁻¹ * swCurveValue Λ u x₀ ^ (-(2 : ℂ)⁻¹)) x₀ := by
  have h1 : HasDerivAt (fun x : ℂ => x ^ 2 - u) (2 * x₀) x₀ := by
    simpa using (hasDerivAt_pow 2 x₀).sub_const u
  have hcurve : HasDerivAt (fun x => swCurveValue Λ u x) (4 * x₀ * (x₀ ^ 2 - u)) x₀ := by
    have key : (fun x : ℂ => swCurveValue Λ u x) = fun x => (x ^ 2 - u) * (x ^ 2 - u) - Λ ^ 4 := by
      ext x; unfold swCurveValue; ring
    rw [key]
    convert (h1.mul h1).sub_const (Λ ^ 4) using 1
    ring
  have hpow := hcurve.cpow_const (c := -(2 : ℂ)⁻¹) h
  have hlin : HasDerivAt (fun x : ℂ => -(x / 2)) (-(2 : ℂ)⁻¹) x₀ := by
    simpa using ((hasDerivAt_id x₀).div_const 2).neg
  convert hlin.mul hpow using 1
  ring

/-- **R2b-ii — integrate the IBP identity (FTC).** Over a real contour `[a,b]` off the cut, the
integral of `∂_u λ_SW` minus `½·∮ dx/y` equals the boundary term `[−x/(2y)]ₐᵇ` (the exact form
integrates to its endpoints). On a *closed* contour (`a = b` after the cut, or matched branch-point
endpoints) the boundary term vanishes, giving the special-geometry relation `∂a/∂u = ½ ∮ dx/y`. -/
theorem swLambda_ibp_integral (Λ u : ℂ) (a b : ℝ)
    (hmem : ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane) :
    (∫ t in a..b, ((t : ℂ) ^ 2 * ((-(2 : ℂ)⁻¹) *
          swCurveValue Λ u (t : ℂ) ^ ((-(2 : ℂ)⁻¹) - 1) * (-(2 * ((t : ℂ) ^ 2 - u))))
        - (2 : ℂ)⁻¹ * swCurveValue Λ u (t : ℂ) ^ (-(2 : ℂ)⁻¹)))
      = -((b : ℂ) / 2) * swCurveValue Λ u (b : ℂ) ^ (-(2 : ℂ)⁻¹)
        - -((a : ℂ) / 2) * swCurveValue Λ u (a : ℂ) ^ (-(2 : ℂ)⁻¹) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -((t : ℂ) / 2) * swCurveValue Λ u (t : ℂ) ^ (-(2 : ℂ)⁻¹)) ?_ ?_
  · intro t ht
    exact (swLambda_ibp_hasDerivAt Λ u (t : ℂ) (hmem t ht)).comp_ofReal
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.sub ?_ ?_
    · exact ((Complex.continuous_ofReal.pow 2).continuousOn).mul
        (swOmegaDerivIntegrand_continuousOn_segment Λ u a b hmem)
    · exact continuousOn_const.mul (swOmegaIntegrand_continuousOn_segment Λ u a b hmem)

/-- **R2b-iii — the special-geometry relation** (segment form). Combining the IBP integral
(`swLambda_ibp_integral`) with the holomorphic period `swPeriodSeg = ∮ dx/y`: the integral of the
`∂_u λ_SW` integrand equals `½·∮ dx/y` plus the boundary term `[−x/(2y)]ₐᵇ`. This is `∂a/∂u =
½ ∮ dx/y` (the link to the holomorphic period / Picard–Fuchs); on a closed contour the boundary
term vanishes. -/
theorem swLambda_deriv_eq_half_period (Λ u : ℂ) (a b : ℝ)
    (hmem : ∀ t ∈ Set.uIcc a b, swCurveValue Λ u (t : ℂ) ∈ Complex.slitPlane) :
    (∫ t in a..b, (t : ℂ) ^ 2 * ((-(2 : ℂ)⁻¹) *
        swCurveValue Λ u (t : ℂ) ^ ((-(2 : ℂ)⁻¹) - 1) * (-(2 * ((t : ℂ) ^ 2 - u)))))
      = (2 : ℂ)⁻¹ * swPeriodSeg Λ a b u
        + (-((b : ℂ) / 2) * swCurveValue Λ u (b : ℂ) ^ (-(2 : ℂ)⁻¹)
          - -((a : ℂ) / 2) * swCurveValue Λ u (a : ℂ) ^ (-(2 : ℂ)⁻¹)) := by
  have hAint : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ 2 * ((-(2 : ℂ)⁻¹) *
      swCurveValue Λ u (t : ℂ) ^ ((-(2 : ℂ)⁻¹) - 1) * (-(2 * ((t : ℂ) ^ 2 - u)))))
      MeasureTheory.volume a b :=
    (((Complex.continuous_ofReal.pow 2).continuousOn).mul
      (swOmegaDerivIntegrand_continuousOn_segment Λ u a b hmem)).intervalIntegrable
  have hBint : IntervalIntegrable
      (fun t : ℝ => (2 : ℂ)⁻¹ * swCurveValue Λ u (t : ℂ) ^ (-(2 : ℂ)⁻¹)) MeasureTheory.volume a b :=
    (continuousOn_const.mul (swOmegaIntegrand_continuousOn_segment Λ u a b hmem)).intervalIntegrable
  have hP : swPeriodSeg Λ a b u = ∫ t in a..b, swCurveValue Λ u (t : ℂ) ^ (-(2 : ℂ)⁻¹) := by
    simp only [swPeriodSeg, swOmegaIntegrand]
  have key := swLambda_ibp_integral Λ u a b hmem
  rw [intervalIntegral.integral_sub hAint hBint, intervalIntegral.integral_const_mul,
    ← hP] at key
  linear_combination key

end SeibergWitten.Physics
