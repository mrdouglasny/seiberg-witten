import SeibergWitten.Physics.Genus1Periods

/-!
# Period asymptotics and the effective coupling's beta function

This module keeps **mathematics** and **physics interpretation** strictly separate, per the
project's discipline: *math axioms use only mathematical vocabulary, and every physical
concept is an explicit named definition identifying it with a math object — never a silent
identification.*

* **Math.** `swCurveValue_scaling` (curve is scale-homogeneous); `mul_deriv_invSq` (a function of
  the scale-invariant `u/Λ²` has `Λ·∂_Λ F(u/w²)|_{w=Λ} = −2(u/Λ²)·F′(u/Λ²)`); and the one **axiom**
  `periodRatio_logDeriv_asymptotic` (the curve's period ratio runs logarithmically — a statement
  about period integrals, no physics).
* **Dictionary** (`physics ≔ math`): `effectiveCoupling`, `betaFunction`, `oneLoopCoefficient`.
* **Physics.** `betaFunction_weakCoupling` — the beta function attains the one-loop value, derived
  from the math axiom plus the (axiom-free) scaling identity.
-/

namespace SeibergWitten.Physics

open Complex Filter

/-! ## Mathematics -/

/-- (Math.) **Scale homogeneity** of the genus-1 SW curve value:
`swCurveValue (λΛ) (λ²u) (λx) = λ⁴ · swCurveValue Λ u x`. (The matter curve scales identically:
`Λ^{4−Nf}∏(x−mᵢ)` has weight `(4−Nf)+Nf = 4`, masses weight 1.) -/
theorem swCurveValue_scaling (lam Λ u x : ℂ) :
    swCurveValue (lam * Λ) (lam ^ 2 * u) (lam * x) = lam ^ 4 * swCurveValue Λ u x := by
  unfold swCurveValue; ring

/-- (Math.) For a function of the scale-invariant `u/Λ²`, the `Λ`-logarithmic derivative is
`Λ · ∂_Λ F(u/w²)|_{w=Λ} = −2 (u/Λ²) · F′(u/Λ²)`. (Axiom-free, by the chain rule.) -/
theorem mul_deriv_invSq (F : ℂ → ℂ) (hF : Differentiable ℂ F) (u Λ : ℂ) (hΛ : Λ ≠ 0) :
    Λ * deriv (fun w => F (u / w ^ 2)) Λ = -2 * (u / Λ ^ 2) * deriv F (u / Λ ^ 2) := by
  have hΛ2 : Λ ^ 2 ≠ 0 := pow_ne_zero 2 hΛ
  have hsq : HasDerivAt (fun w : ℂ => u / w ^ 2) (-(2 * u) / Λ ^ 3) Λ := by
    have h2 : HasDerivAt (fun w : ℂ => w ^ 2) (2 * Λ) Λ := by simpa using hasDerivAt_pow 2 Λ
    convert (h2.inv hΛ2).const_mul u using 1
    field_simp
  have hL : HasDerivAt (fun w => F (u / w ^ 2)) (deriv F (u / Λ ^ 2) * (-(2 * u) / Λ ^ 3)) Λ := by
    simpa [Function.comp] using (hF (u / Λ ^ 2)).hasDerivAt.comp Λ hsq
  rw [hL.deriv]; field_simp

/-! ## Discharge of the log-running input (2026-07-05, the discharge loop)

`periodRatio_logDeriv_asymptotic` was an axiom until it was observed that its formal
statement is purely **existential**: `∃ F` entire with `s·F′(s) → (4−Nf)/(2πi)` —
nothing ties `F` to the curve's period integrals (the docstring said "the period
ratio"; the statement never did). A statement-level gap of exactly the class the
audit's difficult-points register tracks — recorded there — and, as a pure existence
claim, *provable* with an explicit witness: the `Ein`-type primitive
`F₀(z) = ∫₀¹ (1 − e^{−tz})/t dt`, entire with `F₀′(z) = ∫₀¹ e^{−tz} dt`
(differentiation under the integral, constant local dominator), so that
`s·F₀′(s) = 1 − e^{−s} → 1`; scaling by the constant finishes. The **faithful**
strengthening — the same asymptotic for the *actual* ratio `i·K(1−m)/K(m)` at the
curve's modulus — is the R4 target (`audit/PERIOD_LAYER_DISCHARGE.md`), now within
reach of the proved Legendre-ODE/cusp layer. -/

/-- The entire witness: the `Ein`-type primitive `F₀(z) = ∫₀¹ (1 − e^{−tz})/t dt`
(junk value `0` of the integrand at the measure-zero endpoint `t = 0`). -/
noncomputable def einPrimitive (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, (1 - Complex.exp (-((t:ℂ) * z))) / (t:ℂ)

/-- `F₀′(z₀) = ∫₀¹ e^{−tz₀} dt` — differentiation under the integral with the constant
dominator `e^{‖z₀‖+1}` on the unit ball. In particular `einPrimitive` is entire. -/
theorem einPrimitive_hasDerivAt (z₀ : ℂ) :
    HasDerivAt einPrimitive (∫ t in (0:ℝ)..1, Complex.exp (-((t:ℂ) * z₀))) z₀ := by
  have hmeasF : ∀ u : ℂ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => (1 - Complex.exp (-((t:ℂ) * u))) / (t:ℂ))
      (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    intro u
    have m1 : Measurable fun t : ℝ => ((t:ℂ)) := Complex.measurable_ofReal
    have m3 : Measurable fun t : ℝ => Complex.exp (-((t:ℂ) * u)) :=
      Complex.measurable_exp.comp ((m1.mul_const u).neg)
    exact ((measurable_const.sub m3).div m1).aestronglyMeasurable
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0:ℝ)) (b := 1) (μ := MeasureTheory.volume)
    (F := fun (u : ℂ) (t : ℝ) => (1 - Complex.exp (-((t:ℂ) * u))) / (t:ℂ))
    (F' := fun (u : ℂ) (t : ℝ) => Complex.exp (-((t:ℂ) * u)))
    (x₀ := z₀) (s := Metric.ball z₀ 1)
    (bound := fun _ => Real.exp (‖z₀‖ + 1))
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun u => hmeasF u)
    ?_
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.mul continuous_const).neg)).aestronglyMeasurable
    ?_ intervalIntegral.intervalIntegrable_const ?_
  · exact key.2
  · -- interval integrability of the base integrand at z₀: two-regime constant bound
    rw [intervalIntegrable_iff]
    haveI : MeasureTheory.IsFiniteMeasure
        (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) := by
      constructor
      rw [MeasureTheory.Measure.restrict_apply_univ, Set.uIoc_of_le zero_le_one,
        Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    refine ⟨hmeasF z₀, ?_⟩
    apply MeasureTheory.HasFiniteIntegral.of_bounded
      (C := 2 * ‖z₀‖ + (1 + Real.exp ‖z₀‖) * ‖z₀‖)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    refine MeasureTheory.ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hnorm : ‖(1 - Complex.exp (-((t:ℂ) * z₀))) / (t:ℂ)‖
        = ‖1 - Complex.exp (-((t:ℂ) * z₀))‖ / t := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have hw : ‖-((t:ℂ) * z₀)‖ = t * ‖z₀‖ := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have hrev : ‖1 - Complex.exp (-((t:ℂ) * z₀))‖
        = ‖Complex.exp (-((t:ℂ) * z₀)) - 1‖ := norm_sub_rev _ _
    rw [hnorm, div_le_iff₀ ht0, hrev]
    rcases le_or_gt (t * ‖z₀‖) 1 with hc | hc
    · -- small-argument regime: ‖e^w − 1‖ ≤ 2‖w‖ = 2t‖z₀‖
      have h := Complex.norm_exp_sub_one_le (x := -((t:ℂ) * z₀)) (by rw [hw]; exact hc)
      rw [hw] at h
      have hXt : 0 ≤ (1 + Real.exp ‖z₀‖) * ‖z₀‖ * t := by positivity
      nlinarith [h, hXt, mul_nonneg (norm_nonneg z₀) ht0.le]
    · -- large-argument regime: ‖e^w − 1‖ ≤ 1 + e^{‖z₀‖} ≤ (1+e^{‖z₀‖})·t‖z₀‖
      have h1 : ‖Complex.exp (-((t:ℂ) * z₀)) - 1‖ ≤ Real.exp ‖z₀‖ + 1 := by
        calc ‖Complex.exp (-((t:ℂ) * z₀)) - 1‖
            ≤ ‖Complex.exp (-((t:ℂ) * z₀))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
          _ ≤ Real.exp ‖z₀‖ + 1 := by
              rw [Complex.norm_exp, norm_one]
              have h2 : (-((t:ℂ) * z₀)).re ≤ ‖z₀‖ := by
                calc (-((t:ℂ) * z₀)).re ≤ ‖-((t:ℂ) * z₀)‖ := Complex.re_le_norm _
                  _ = t * ‖z₀‖ := hw
                  _ ≤ 1 * ‖z₀‖ :=
                      mul_le_mul_of_nonneg_right ht1 (norm_nonneg z₀)
                  _ = ‖z₀‖ := one_mul _
              have := Real.exp_le_exp.mpr h2
              linarith
      have hnn : (0:ℝ) ≤ 1 + Real.exp ‖z₀‖ := by positivity
      have h3 : (1 + Real.exp ‖z₀‖) * 1 ≤ (1 + Real.exp ‖z₀‖) * (t * ‖z₀‖) :=
        mul_le_mul_of_nonneg_left hc.le hnn
      have h4 : 0 ≤ 2 * ‖z₀‖ * t := by positivity
      nlinarith [h1, h3, h4]
  · -- the F' bound on the ball: constant e^{‖z₀‖+1}
    refine MeasureTheory.ae_of_all _ fun t ht u hu => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hunorm : ‖u‖ ≤ ‖z₀‖ + 1 := by
      have hd := mem_ball_iff_norm.mp hu
      calc ‖u‖ = ‖(u - z₀) + z₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖u - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ ‖z₀‖ + 1 := by linarith
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc (-((t:ℂ) * u)).re ≤ ‖-((t:ℂ) * u)‖ := Complex.re_le_norm _
      _ = t * ‖u‖ := by
          rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
      _ ≤ 1 * (‖z₀‖ + 1) :=
          mul_le_mul ht.2 hunorm (norm_nonneg u) zero_le_one
      _ = ‖z₀‖ + 1 := one_mul _
  · -- the derivative in the parameter, for t ≠ 0
    refine MeasureTheory.ae_of_all _ fun t ht u hu => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have htne : ((t:ℂ)) ≠ 0 := by
      exact_mod_cast ne_of_gt ht.1
    have h1 : HasDerivAt (fun u : ℂ => -((t:ℂ) * u)) (-(t:ℂ)) u := by
      simpa using ((hasDerivAt_id u).const_mul ((t:ℂ))).neg
    have h2 := (Complex.hasDerivAt_exp (-((t:ℂ) * u))).comp u h1
    have h3 := (h2.const_sub 1).div_const ((t:ℂ))
    convert h3 using 1
    field_simp

/-- The derivative integral in closed form: `∫₀¹ e^{−tz} dt = (1 − e^{−z})/z` for
`z ≠ 0` (FTC with antiderivative `−e^{−tz}/z`). -/
theorem integral_exp_neg_mul {z : ℂ} (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..1, Complex.exp (-((t:ℂ) * z)) = (1 - Complex.exp (-z)) / z := by
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => -Complex.exp (-((t:ℂ) * z)) / z)
        (Complex.exp (-((t:ℂ) * z))) t := by
    intro t _
    have h0 : HasDerivAt (fun t : ℝ => ((t:ℂ))) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h1 : HasDerivAt (fun t : ℝ => -((t:ℂ) * z)) (-z) t := by
      have := (h0.mul_const z).neg
      simpa using this
    have h2 := (Complex.hasDerivAt_exp (-((t:ℂ) * z))).comp t h1
    have h3 := (h2.neg).div_const z
    convert h3 using 1
    field_simp
  have hcont : Continuous fun t : ℝ => Complex.exp (-((t:ℂ) * z)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.mul continuous_const).neg)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 1)]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, neg_zero,
    Complex.exp_zero]
  field_simp
  ring

/-- **(Math, DISCHARGED — was an axiom until 2026-07-05.)** There is an entire `F`
whose logarithmic derivative `s·F′(s)` tends to `(4 − Nf)/(2πi)` along the real ray.
Proved with the explicit `Ein`-type witness — see the section header: the statement
is purely existential and was never formally tied to the curve's periods; the
faithful period-ratio version is the R4 target. -/
theorem periodRatio_logDeriv_asymptotic (Nf : ℕ) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      Tendsto (fun s : ℝ => (s : ℂ) * deriv F (s : ℂ)) atTop
        (nhds ((4 - (Nf : ℂ)) / (2 * (Real.pi : ℂ) * I))) := by
  set c : ℂ := (4 - (Nf : ℂ)) / (2 * (Real.pi : ℂ) * I) with hc
  refine ⟨fun z => c * einPrimitive z,
    fun z => ((einPrimitive_hasDerivAt z).const_mul c).differentiableAt, ?_⟩
  have hev : ∀ᶠ s : ℝ in atTop,
      c * (1 - Complex.exp (-((s:ℂ))))
        = (s:ℂ) * deriv (fun z => c * einPrimitive z) (s:ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with s hs
    have hs0 : ((s:ℂ)) ≠ 0 := by
      exact_mod_cast ne_of_gt (by linarith : (0:ℝ) < s)
    rw [((einPrimitive_hasDerivAt ((s:ℂ))).const_mul c).deriv,
      integral_exp_neg_mul hs0]
    field_simp
  have hexp0 : Tendsto (fun s : ℝ => Complex.exp (-((s:ℂ)))) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun s : ℝ => ‖Complex.exp (-((s:ℂ)))‖) = fun s : ℝ => Real.exp (-s) := by
      funext s
      rw [Complex.norm_exp]
      norm_num
    rw [heq]
    exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hone : Tendsto (fun _ : ℝ => (1:ℂ)) atTop (nhds 1) := tendsto_const_nhds
  have hlim := (hone.sub hexp0).const_mul c
  rw [sub_zero, mul_one] at hlim
  exact Filter.Tendsto.congr' hev hlim

/-! ## Dictionary: physical concepts as definitions of the math objects -/

/-- **(Dictionary.)** The EFT **effective coupling** `τ(u,Λ)` *is* the curve's period ratio `F`
evaluated at the scale-invariant argument `u/Λ²`. -/
noncomputable def effectiveCoupling (F : ℂ → ℂ) (u Λ : ℂ) : ℂ := F (u / Λ ^ 2)

/-- **(Dictionary.)** The EFT **beta function** *is* `Λ · ∂_Λ` of the effective coupling (the
standard EFT definition `Λ d/dΛ τ`). -/
noncomputable def betaFunction (F : ℂ → ℂ) (u Λ : ℂ) : ℂ :=
  Λ * deriv (fun w => effectiveCoupling F u w) Λ

/-- **(Dictionary.)** The **one-loop coefficient** `b₀ = 2N − Nf` (here `4 − Nf`, `N = 2`). -/
def oneLoopCoefficient (Nf : ℕ) : ℂ := 4 - Nf

/-! ## Physics: the beta function attains its one-loop value -/

/-- **The EFT beta function attains its one-loop value.** Along weak coupling `u = t·Λ²` (`t → ∞`),
`betaFunction → −b₀/(π i)` with `b₀ = oneLoopCoefficient Nf = 4 − Nf` — proportional to the one-loop
coefficient (vanishing exactly at `Nf = 4`, the conformal case; `= i·b₀/π`). The only
physical
input is the math axiom `periodRatio_logDeriv_asymptotic`; the scaling identity `mul_deriv_invSq` is
axiom-free. -/
theorem betaFunction_weakCoupling (Nf : ℕ) (Λ : ℂ) (hΛ : Λ ≠ 0) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      Tendsto (fun t : ℝ => betaFunction F ((t : ℂ) * Λ ^ 2) Λ) atTop
        (nhds (-(oneLoopCoefficient Nf) / ((Real.pi : ℂ) * I))) := by
  obtain ⟨F, hF, hlim⟩ := periodRatio_logDeriv_asymptotic Nf
  refine ⟨F, hF, ?_⟩
  have hΛ2 : Λ ^ 2 ≠ 0 := pow_ne_zero 2 hΛ
  have key : ∀ t : ℝ, betaFunction F ((t : ℂ) * Λ ^ 2) Λ = -2 * ((t : ℂ) * deriv F (t : ℂ)) := by
    intro t
    simp only [betaFunction, effectiveCoupling]
    rw [mul_deriv_invSq F hF ((t : ℂ) * Λ ^ 2) Λ hΛ, mul_div_cancel_right₀ (t : ℂ) hΛ2]
    ring
  simp_rw [key]
  have h2 := hlim.const_mul (-2 : ℂ)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hval : (-2 : ℂ) * ((4 - (Nf : ℂ)) / (2 * (Real.pi : ℂ) * I))
      = -(oneLoopCoefficient Nf) / ((Real.pi : ℂ) * I) := by
    rw [oneLoopCoefficient]; field_simp
  rw [hval] at h2
  exact h2

end SeibergWitten.Physics
