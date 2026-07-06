import Mathlib
import SeibergWitten.Physics.ThetaLambda

/-!
# Complete elliptic integrals and the C-route classical axioms (rank 1)

The C-route (`audit/GENUS1_PERIODS_PLAN.md`, revision 2026-07-04) replaces the coarse
`periodRigidityAxiom` at rank 1 by **classical, citable, numerically vetted** axioms about
complete elliptic integrals, so the SU(2) headline stops resembling its own hypothesis.

This file is milestone **C0**: the definitions (`ellipticKm`, `ellipticEm`, the parameter
cut plane) and the four axioms C1–C4, exactly as vetted:

* numerically — `audit/numerical/validate_elliptic.py`, **84/84 at `dps = 40`** (the
  integral definitions against `mpmath.ellipk/ellipe`; the C1 witness formula in all four
  quadrants of the cut plane; Legendre; the cusp limits; both C4 cusp-monodromy checks);
* adversarially — GR review 2026-07-04 (`audit/C_ROUTE_REVIEW_PROMPT.md`): v1 was NO-GO;
  this is the corrected **v2** (explicit `K ≠ 0` in C1; the `E` limits in C3; the new C4
  cusp labeling; holomorphy deliberately a *lemma target*, `C1h`, not an axiom).

References: Whittaker–Watson, *A Course of Modern Analysis*, §§21–22.
-/

open Filter Topology intervalIntegral

namespace SeibergWitten.Physics

/-- The parameter cut plane `ℂ ∖ ((−∞,0] ∪ [1,∞))`: the domain on which the principal
branches below are single-valued. Symmetric under `m ↦ 1 − m` (proved:
`one_sub_mem_ellipticParamDomain`). -/
def EllipticParamDomain : Set ℂ := {m | ¬ (m.im = 0 ∧ (m.re ≤ 0 ∨ 1 ≤ m.re))}

/-- **Complete elliptic integral of the first kind** in the parameter `m = k²`:
`K(m) = ∫₀^{π/2} (1 − m sin²θ)^{−1/2} dθ` (principal-branch `cpow`). -/
noncomputable def ellipticKm (m : ℂ) : ℂ :=
  ∫ θ in (0:ℝ)..(Real.pi / 2), ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)

/-- **Complete elliptic integral of the second kind** in the parameter `m`. -/
noncomputable def ellipticEm (m : ℂ) : ℂ :=
  ∫ θ in (0:ℝ)..(Real.pi / 2), ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)

/-- The cut plane is symmetric under the modulus involution `m ↦ 1 − m` (so every axiom
below may be applied at `1 − m` as well). -/
theorem one_sub_mem_ellipticParamDomain {m : ℂ} (hm : m ∈ EllipticParamDomain) :
    (1 - m) ∈ EllipticParamDomain := by
  simp only [EllipticParamDomain, Set.mem_setOf_eq, Complex.sub_im, Complex.one_im,
    Complex.sub_re, Complex.one_re, zero_sub, neg_eq_zero, not_and, not_or] at hm ⊢
  intro him
  have := hm him
  constructor <;> intro h <;> [exact absurd (by linarith : (1:ℝ) ≤ m.re) this.2;
    exact absurd (by linarith : m.re ≤ 0) this.1]

/-- The cut plane is nonempty (`m = ½` — the numerically anchored center point). -/
theorem half_mem_ellipticParamDomain : (1/2 : ℂ) ∈ EllipticParamDomain := by
  simp only [EllipticParamDomain, Set.mem_setOf_eq, not_and, not_or]
  intro _
  norm_num

/-- The cut plane is open (complement of the two closed rays). -/
theorem isOpen_ellipticParamDomain : IsOpen EllipticParamDomain := by
  have h : EllipticParamDomain =
      ({m : ℂ | m.im = 0} ∩ ({m | m.re ≤ 0} ∪ {m | 1 ≤ m.re}))ᶜ := by
    ext m
    simp [EllipticParamDomain, Set.mem_setOf_eq]
  rw [h]
  exact ((isClosed_eq Complex.continuous_im continuous_const).inter
    ((isClosed_le Complex.continuous_re continuous_const).union
      (isClosed_le continuous_const Complex.continuous_re))).isOpen_compl

/-- **The branch never hits the cut**: for `m` in the cut plane and any real `θ`, the
`cpow` base `1 − m·sin²θ` lies in the slit plane `ℂ ∖ (−∞, 0]` — the analytically
load-bearing fact behind every holomorphy statement about `ellipticKm`/`ellipticEm`
(cf. `audit/DIFFICULT_POINTS.md` A3). -/
theorem one_sub_mul_sin_sq_mem_slitPlane {m : ℂ} (hm : m ∈ EllipticParamDomain) (θ : ℝ) :
    (1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2 ∈ Complex.slitPlane := by
  have hs0 : (0:ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hs1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  rw [Complex.mem_slitPlane_iff]
  have hcast : ((Real.sin θ : ℂ)) ^ 2 = ((Real.sin θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hre : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2).re = 1 - m.re * Real.sin θ ^ 2 := by
    rw [hcast]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have him : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2).im = -(m.im * Real.sin θ ^ 2) := by
    rw [hcast]
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add, zero_sub]
  by_cases h0 : m.im = 0
  · -- real parameter: the domain forces `0 < m.re < 1`, so the base has positive real part
    left
    simp only [EllipticParamDomain, Set.mem_setOf_eq, not_and, not_or] at hm
    obtain ⟨h1, h2⟩ := hm h0
    rw [hre]
    nlinarith [mul_le_mul_of_nonneg_left hs1 (le_of_lt (not_le.mp h1))]
  · -- genuinely complex parameter: either `sin θ = 0` (base is `1`) or the base has im ≠ 0
    by_cases hsz : Real.sin θ ^ 2 = 0
    · left; rw [hre, hsz]; norm_num
    · right; rw [him]
      exact neg_ne_zero.mpr (mul_ne_zero h0 hsz)

/-- **Small parameters clear the cut too**: for `‖m‖ < 1` the base `1 − m·sin²θ` has
positive real part. This second slit-plane regime (a neighborhood of `m = 0`, overlapping
the cut plane) is what lets the cusp values `K(0) = E(0) = π/2` be *proved* rather than
assumed. -/
theorem one_sub_mul_sin_sq_mem_slitPlane_of_norm_lt {m : ℂ} (hm : ‖m‖ < 1) (θ : ℝ) :
    (1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2 ∈ Complex.slitPlane := by
  have hs0 : (0:ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hs1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  rw [Complex.mem_slitPlane_iff]
  left
  have hcast : ((Real.sin θ : ℂ)) ^ 2 = ((Real.sin θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hre : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2).re = 1 - m.re * Real.sin θ ^ 2 := by
    rw [hcast]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre]
  have habs : |m.re| ≤ ‖m‖ := Complex.abs_re_le_norm m
  nlinarith [abs_le.mp habs]

/-- The elliptic integrand `(1 − m sin²θ)^c` is continuous in `θ` whenever the base stays
in the slit plane (hence the integrals defining `ellipticKm`/`ellipticEm` are honest). -/
theorem integrand_cpow_continuous_of_slit {m : ℂ}
    (hm : ∀ θ : ℝ, (1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2 ∈ Complex.slitPlane) (c : ℂ) :
    Continuous fun θ : ℝ => ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ c := by
  refine Continuous.cpow ?_ continuous_const hm
  fun_prop

/-- Specialization to the cut plane. -/
theorem integrand_cpow_continuous {m : ℂ} (hm : m ∈ EllipticParamDomain) (c : ℂ) :
    Continuous fun θ : ℝ => ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ c :=
  integrand_cpow_continuous_of_slit (one_sub_mul_sin_sq_mem_slitPlane hm) c

/-- **C1h engine — differentiation under the integral for the elliptic family.** The
parameter integral `m ↦ ∫₀^{π/2} (1 − m sin²θ)^c dθ` has a complex derivative at every
point of the cut plane, with the expected integrand derivative — the holomorphy the
adversarial review demanded (a pointwise `∃` carries no analytic structure;
`audit/DIFFICULT_POINTS.md` A1), proved rather than axiomatized. -/
theorem cpow_param_integral_hasDerivAt_of_slit (c : ℂ) {S : Set ℂ} (hSo : IsOpen S)
    (hslit : ∀ m ∈ S, ∀ θ : ℝ, (1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2 ∈ Complex.slitPlane)
    {m₀ : ℂ} (hm₀ : m₀ ∈ S) :
    HasDerivAt (fun m : ℂ => ∫ θ in (0:ℝ)..(Real.pi / 2),
        ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ c)
      (∫ θ in (0:ℝ)..(Real.pi / 2),
        c * ((1 : ℂ) - m₀ * (Real.sin θ : ℂ) ^ 2) ^ (c - 1) * (-((Real.sin θ : ℂ) ^ 2)))
      m₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hSo m₀ hm₀
  have hhalf : (0:ℝ) < ε / 2 := by linarith
  have hball' : Metric.ball m₀ (ε / 2) ⊆ S :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  have hcball : Metric.closedBall m₀ (ε / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  -- the uniform bound on the derivative integrand, from compactness
  set G : ℂ × ℝ → ℂ := fun p =>
    c * ((1 : ℂ) - p.1 * (Real.sin p.2 : ℂ) ^ 2) ^ (c - 1) * (-((Real.sin p.2 : ℂ) ^ 2))
    with hG
  have hScompact : IsCompact
      ((Metric.closedBall m₀ (ε / 2)) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2))) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hGcont : ContinuousOn G
      ((Metric.closedBall m₀ (ε / 2)) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2))) := by
    refine (continuousOn_const.mul (ContinuousOn.cpow ?_ continuousOn_const ?_)).mul
      (Continuous.continuousOn (by fun_prop))
    · fun_prop
    · rintro ⟨u, θ⟩ ⟨hu, -⟩
      exact hslit _ (hcball hu) θ
  obtain ⟨C, hC⟩ := hScompact.exists_bound_of_continuousOn hGcont
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0:ℝ)) (b := Real.pi / 2) (μ := MeasureTheory.volume)
    (F := fun (u : ℂ) (θ : ℝ) => ((1 : ℂ) - u * (Real.sin θ : ℂ) ^ 2) ^ c)
    (F' := fun (u : ℂ) (θ : ℝ) =>
      c * ((1 : ℂ) - u * (Real.sin θ : ℂ) ^ 2) ^ (c - 1) * (-((Real.sin θ : ℂ) ^ 2)))
    (x₀ := m₀) (s := Metric.ball m₀ (ε / 2)) (bound := fun _ => C)
    (Metric.ball_mem_nhds m₀ hhalf)
    (((hSo.eventually_mem hm₀).mono fun u hu =>
      (integrand_cpow_continuous_of_slit (hslit u hu) c).aestronglyMeasurable))
    ((integrand_cpow_continuous_of_slit (hslit m₀ hm₀) c).intervalIntegrable 0 (Real.pi / 2))
    (((continuous_const.mul (integrand_cpow_continuous_of_slit (hslit m₀ hm₀) (c - 1))).mul
      (by fun_prop : Continuous fun θ : ℝ => -((Real.sin θ : ℂ) ^ 2))).aestronglyMeasurable)
    (by
      refine MeasureTheory.ae_of_all _ fun θ hθ u hu => ?_
      have hθIcc : θ ∈ Set.Icc (0:ℝ) (Real.pi / 2) := by
        rw [Set.mem_uIoc] at hθ
        rcases hθ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;>
          [linarith; linarith; linarith [Real.pi_pos]; linarith [Real.pi_pos]]
      exact hC (u, θ) ⟨Metric.ball_subset_closedBall hu, hθIcc⟩)
    intervalIntegral.intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ u hu => by
      have hbase : HasDerivAt (fun x : ℂ => (1 : ℂ) - x * (Real.sin θ : ℂ) ^ 2)
          (-((Real.sin θ : ℂ) ^ 2)) u := by
        simpa using ((hasDerivAt_id u).mul_const ((Real.sin θ : ℂ) ^ 2)).const_sub 1
      simpa using hbase.cpow_const (hslit _ (hball' hu) θ))
  exact key.2

/-- The cut-plane specialization (the original C1h engine statement). -/
theorem cpow_param_integral_hasDerivAt (c : ℂ) {m₀ : ℂ} (hm₀ : m₀ ∈ EllipticParamDomain) :
    HasDerivAt (fun m : ℂ => ∫ θ in (0:ℝ)..(Real.pi / 2),
        ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ c)
      (∫ θ in (0:ℝ)..(Real.pi / 2),
        c * ((1 : ℂ) - m₀ * (Real.sin θ : ℂ) ^ 2) ^ (c - 1) * (-((Real.sin θ : ℂ) ^ 2)))
      m₀ :=
  cpow_param_integral_hasDerivAt_of_slit c isOpen_ellipticParamDomain
    (fun _ hm => one_sub_mul_sin_sq_mem_slitPlane hm) hm₀

/-- `K` and `E` are differentiable on the unit ball too (the second slit regime) —
in particular **continuous at `m = 0`**, where the cut plane's boundary point sits. -/
theorem cpow_param_integral_continuousAt_zero (c : ℂ) :
    ContinuousAt (fun m : ℂ => ∫ θ in (0:ℝ)..(Real.pi / 2),
      ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ c) 0 := by
  have h := cpow_param_integral_hasDerivAt_of_slit c (S := Metric.ball (0:ℂ) 1)
    Metric.isOpen_ball
    (fun m hm θ => one_sub_mul_sin_sq_mem_slitPlane_of_norm_lt
      (by simpa using mem_ball_zero_iff.mp hm) θ)
    (mem_ball_zero_iff.mpr (by norm_num : ‖(0:ℂ)‖ < 1))
  exact h.continuousAt

/-- **The cusp value, proved:** `K(0) = π/2` (the integrand collapses to `1`). -/
theorem ellipticKm_zero : ellipticKm 0 = ((Real.pi / 2 : ℝ) : ℂ) := by
  unfold ellipticKm
  simp only [zero_mul, sub_zero, Complex.one_cpow]
  rw [intervalIntegral.integral_const]
  simp

/-- **The cusp value, proved:** `E(0) = π/2`. -/
theorem ellipticEm_zero : ellipticEm 0 = ((Real.pi / 2 : ℝ) : ℂ) := by
  unfold ellipticEm
  simp only [zero_mul, sub_zero, Complex.one_cpow]
  rw [intervalIntegral.integral_const]
  simp

/-- **Former C3 clause, now a THEOREM:** `K(m) → π/2` as `m → 0` (continuity at `0` from
the ball-regime C1h engine + the computed value). -/
theorem ellipticKm_tendsto_zero :
    Tendsto ellipticKm (𝓝 0) (𝓝 ((Real.pi / 2 : ℝ) : ℂ)) := by
  have h := cpow_param_integral_continuousAt_zero (-(1/2) : ℂ)
  rw [ContinuousAt] at h
  have hval : (∫ θ in (0:ℝ)..(Real.pi / 2),
      ((1 : ℂ) - (0:ℂ) * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)) = ((Real.pi / 2 : ℝ) : ℂ) :=
    ellipticKm_zero
  rwa [hval] at h

/-- **Former C3 clause, now a THEOREM:** `E(m) → π/2` as `m → 0`. -/
theorem ellipticEm_tendsto_zero :
    Tendsto ellipticEm (𝓝 0) (𝓝 ((Real.pi / 2 : ℝ) : ℂ)) := by
  have h := cpow_param_integral_continuousAt_zero ((1/2) : ℂ)
  rw [ContinuousAt] at h
  have hval : (∫ θ in (0:ℝ)..(Real.pi / 2),
      ((1 : ℂ) - (0:ℂ) * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)) = ((Real.pi / 2 : ℝ) : ℂ) :=
    ellipticEm_zero
  rwa [hval] at h

/-- Norm domination for the square-root power: `‖x^{1/2}‖ ≤ max 1 ‖x‖` (junk-safe). -/
theorem norm_cpow_half_le' (x : ℂ) : ‖x ^ ((1/2 : ℝ) : ℂ)‖ ≤ max 1 ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Complex.zero_cpow (by norm_num : (((1/2 : ℝ)) : ℂ) ≠ 0)]
    simp
  · rw [Complex.norm_cpow_of_ne_zero hx]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, Real.exp_zero, div_one]
    rcases le_total ‖x‖ 1 with h | h
    · exact le_max_of_le_left (Real.rpow_le_one (norm_nonneg x) h (by norm_num))
    · refine le_max_of_le_right ?_
      calc ‖x‖ ^ ((1:ℝ)/2) ≤ ‖x‖ ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h (by norm_num)
        _ = ‖x‖ := Real.rpow_one _

/-- **The cusp value at `m = 1`, proved:** `E(1) = 1` — the integrand collapses to
`(cos²θ)^{1/2} = cos θ` on `[0, π/2]`, and `∫₀^{π/2} cos = 1`. -/
theorem ellipticEm_one : ellipticEm 1 = 1 := by
  unfold ellipticEm
  have hcongr : Set.EqOn
      (fun θ : ℝ => ((1 : ℂ) - 1 * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ))
      (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ)) (Set.uIcc (0:ℝ) (Real.pi / 2)) := by
    intro θ hθ
    rw [Set.uIcc_of_le (by positivity)] at hθ
    have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hr : (1 : ℝ) - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hbase : (1 : ℂ) - 1 * (Real.sin θ : ℂ) ^ 2 = ((Real.cos θ ^ 2 : ℝ) : ℂ) := by
      calc (1 : ℂ) - 1 * (Real.sin θ : ℂ) ^ 2
          = ((1 - Real.sin θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
        _ = ((Real.cos θ ^ 2 : ℝ) : ℂ) := by rw [hr]
    simp only []
    rw [hbase, show ((1/2 : ℂ)) = (((1/2 : ℝ)) : ℂ) from by norm_num,
      ← Complex.ofReal_cpow (sq_nonneg _)]
    congr 1
    rw [show ((1/2 : ℝ)) = (((2:ℕ) : ℝ))⁻¹ from by norm_num,
      Real.pow_rpow_inv_natCast hcos two_ne_zero]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal,
    integral_cos]
  simp

/-- **Former C3 clause, now a THEOREM:** `E(1−m) → 1` as `m → 0` within the cut plane —
dominated convergence across the `θ = π/2` endpoint (where the slit-plane argument
fails; a.e. pointwise convergence suffices, the endpoint being null). -/
theorem ellipticEm_one_sub_tendsto :
    Tendsto (fun m : ℂ => ellipticEm (1 - m)) (𝓝[EllipticParamDomain] 0) (𝓝 1) := by
  have key := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := Real.pi / 2)
    (l := 𝓝[EllipticParamDomain] (0:ℂ))
    (F := fun (m : ℂ) (θ : ℝ) => ((1 : ℂ) - (1 - m) * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ))
    (f := fun θ : ℝ => ((1 : ℂ) - 1 * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ))
    (bound := fun _ => (3/2 : ℝ))
    ?_ ?_ ?_ ?_
  · have hval : (∫ θ in (0:ℝ)..(Real.pi / 2),
        ((1 : ℂ) - 1 * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)) = 1 := by
      have h1 : ellipticEm 1 = ∫ θ in (0:ℝ)..(Real.pi / 2),
          ((1 : ℂ) - 1 * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ) := rfl
      rw [← h1, ellipticEm_one]
    rw [hval] at key
    exact key
  · -- measurability, eventually in the filter
    filter_upwards [self_mem_nhdsWithin] with m hm
    exact ((integrand_cpow_continuous (one_sub_mem_ellipticParamDomain hm)
      ((1/2) : ℂ))).aestronglyMeasurable
  · -- uniform bound for ‖m‖ ≤ 1/2
    have hsmall : ∀ᶠ m in 𝓝[EllipticParamDomain] (0:ℂ), ‖m‖ < 1/2 := by
      have : ∀ᶠ m in 𝓝 (0:ℂ), ‖m‖ < 1/2 := by
        have := Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1/2)
        filter_upwards [this] with m hm
        simpa using mem_ball_zero_iff.mp hm
      exact this.filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall] with m hm
    refine MeasureTheory.ae_of_all _ fun θ _ => ?_
    have hs0 : (0:ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
    have hs1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hbn : ‖(1 : ℂ) - (1 - m) * (Real.sin θ : ℂ) ^ 2‖ ≤ 3/2 := by
      have hsplit : (1 : ℂ) - (1 - m) * (Real.sin θ : ℂ) ^ 2
          = ((1 - Real.sin θ ^ 2 : ℝ) : ℂ) + m * ((Real.sin θ ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hsplit]
      calc ‖((1 - Real.sin θ ^ 2 : ℝ) : ℂ) + m * ((Real.sin θ ^ 2 : ℝ) : ℂ)‖
          ≤ ‖((1 - Real.sin θ ^ 2 : ℝ) : ℂ)‖ + ‖m * ((Real.sin θ ^ 2 : ℝ) : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ 1 + 1/2 * 1 := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real]
            gcongr
            · rw [Real.norm_of_nonneg (by linarith)]; linarith
            · rw [Real.norm_of_nonneg hs0]; exact hs1
        _ = 3/2 := by norm_num
    have hhalf : ((1/2 : ℂ)) = (((1/2 : ℝ)) : ℂ) := by norm_num
    rw [hhalf]
    calc ‖((1 : ℂ) - (1 - m) * (Real.sin θ : ℂ) ^ 2) ^ (((1/2 : ℝ)) : ℂ)‖
        ≤ max 1 ‖(1 : ℂ) - (1 - m) * (Real.sin θ : ℂ) ^ 2‖ := norm_cpow_half_le' _
      _ ≤ 3/2 := max_le (by norm_num) hbn
  · exact intervalIntegral.intervalIntegrable_const
  · -- a.e. pointwise convergence (excluding the null endpoint θ = π/2)
    have hae : ∀ᵐ (θ : ℝ) ∂MeasureTheory.volume, θ ≠ Real.pi / 2 := by
      refine MeasureTheory.ae_iff.mpr ?_
      have hset : {θ : ℝ | ¬ θ ≠ Real.pi / 2} = {Real.pi / 2} := by
        ext θ; simp
      rw [hset]
      exact MeasureTheory.measure_singleton _
    filter_upwards [hae] with θ hθne hθmem
    have hθIoc : θ ∈ Set.Ioc (0:ℝ) (Real.pi / 2) := by
      rwa [Set.uIoc_of_le (by positivity)] at hθmem
    have hcos : 0 < Real.cos θ := by
      have := Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) from
        ⟨by linarith [hθIoc.1, Real.pi_pos], lt_of_le_of_ne hθIoc.2 hθne⟩)
      exact this
    -- the limiting base is the positive real cos²θ, inside the slit plane
    have hbase0 : ((1 : ℂ) - 1 * (Real.sin θ : ℂ) ^ 2) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      have hr : (1 : ℝ) - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq θ]
      have : ((1 : ℂ) - 1 * (Real.sin θ : ℂ) ^ 2).re = 1 - Real.sin θ ^ 2 := by
        have hcast : (1 : ℂ) - 1 * (Real.sin θ : ℂ) ^ 2
            = ((1 - Real.sin θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, Complex.ofReal_re]
      rw [this, hr]
      positivity
    have hcont : ContinuousAt (fun z : ℂ => z ^ ((1/2) : ℂ))
        ((1 : ℂ) - 1 * (Real.sin θ : ℂ) ^ 2) :=
      ((hasDerivAt_id _).cpow_const hbase0).continuousAt
    have hbasem : Tendsto (fun m : ℂ => (1 : ℂ) - (1 - m) * (Real.sin θ : ℂ) ^ 2)
        (𝓝[EllipticParamDomain] 0) (𝓝 ((1 : ℂ) - 1 * (Real.sin θ : ℂ) ^ 2)) := by
      have h1 : Tendsto (fun m : ℂ => (1 : ℂ) - (1 - m) * (Real.sin θ : ℂ) ^ 2)
          (𝓝 (0:ℂ)) (𝓝 ((1 : ℂ) - (1 - 0) * (Real.sin θ : ℂ) ^ 2)) :=
        ((continuous_const.sub ((continuous_const.sub continuous_id).mul
          continuous_const)).tendsto 0)
      have h2 := h1.mono_left (nhdsWithin_le_nhds :
        𝓝[EllipticParamDomain] (0:ℂ) ≤ 𝓝 (0:ℂ))
      simpa using h2
    exact hcont.tendsto.comp hbasem

/-- The cut plane excludes the origin. -/
theorem zero_notMem_ellipticParamDomain : (0:ℂ) ∉ EllipticParamDomain := by
  simp [EllipticParamDomain]

/-- Parameters in the cut plane are nonzero. -/
theorem ne_zero_of_mem_ellipticParamDomain {m : ℂ} (hm : m ∈ EllipticParamDomain) :
    m ≠ 0 := fun h => zero_notMem_ellipticParamDomain (h ▸ hm)

/-- Slit-plane members are nonzero. -/
theorem slitPlane_ne_zero' {z : ℂ} (hz : z ∈ Complex.slitPlane) : z ≠ 0 := by
  rintro rfl
  rw [Complex.mem_slitPlane_iff] at hz
  simp at hz

/-- **The Legendre ODE for `E`, proved:** `dE/dm = (E − K)/(2m)` on the cut plane.
Pure `Δ`-algebra on the C1h engine's derivative integral: with `Δ = 1 − m sin²θ`,
`sin²θ = (1−Δ)/m` converts both the derivative integrand and `E − K` into the same
`∫ sin²·Δ^{−1/2}` — no integration by parts needed. First of the two Legendre ODEs
(the `K` one needs the IBP identity; it is the route to discharging C2). -/
theorem ellipticEm_hasDerivAt {m : ℂ} (hm : m ∈ EllipticParamDomain) :
    HasDerivAt ellipticEm ((ellipticEm m - ellipticKm m) / (2 * m)) m := by
  have hm0 : m ≠ 0 := ne_zero_of_mem_ellipticParamDomain hm
  have h := cpow_param_integral_hasDerivAt ((1/2) : ℂ) hm
  -- the common integral: I = ∫ sin²·Δ^{−1/2}
  set I : ℂ := ∫ θ in (0:ℝ)..(Real.pi / 2),
    ((Real.sin θ : ℂ) ^ 2) * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ) with hI
  have hIcont : Continuous fun θ : ℝ =>
      ((Real.sin θ : ℂ) ^ 2) * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ) :=
    (by fun_prop : Continuous fun θ : ℝ => ((Real.sin θ : ℂ) ^ 2)).mul
      (integrand_cpow_continuous hm (-(1/2) : ℂ))
  -- the engine's derivative equals −(1/2)·I
  have hderiv_eq : (∫ θ in (0:ℝ)..(Real.pi / 2),
      ((1/2) : ℂ) * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (((1/2) : ℂ) - 1)
        * (-((Real.sin θ : ℂ) ^ 2))) = -(1/2) * I := by
    rw [hI, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hexp : (((1/2) : ℂ) - 1) = (-(1/2) : ℂ) := by ring
    rw [hexp]
    ring
  -- E − K = −m·I  (the Δ-algebra identity)
  have hEK : ellipticEm m - ellipticKm m = -m * I := by
    have hsub : ellipticEm m - ellipticKm m = ∫ θ in (0:ℝ)..(Real.pi / 2),
        (((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)
          - ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)) := by
      rw [ellipticEm, ellipticKm, ← intervalIntegral.integral_sub
        ((integrand_cpow_continuous hm ((1/2) : ℂ)).intervalIntegrable _ _)
        ((integrand_cpow_continuous hm (-(1/2) : ℂ)).intervalIntegrable _ _)]
    rw [hsub, hI, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hslit := one_sub_mul_sin_sq_mem_slitPlane hm θ
    have hne : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ≠ 0 := slitPlane_ne_zero' hslit
    have hhalf : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)
        = ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2)
          * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ) := by
      conv_lhs => rw [show ((1/2) : ℂ) = 1 + (-(1/2) : ℂ) from by ring]
      rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
    rw [hhalf]
    ring
  -- assemble
  have hfinal : (ellipticEm m - ellipticKm m) / (2 * m) = -(1/2) * I := by
    rw [hEK]
    field_simp
  rw [hfinal, ← hderiv_eq]
  exact h

/-- Parameters in the cut plane differ from `1`. -/
theorem ne_one_of_mem_ellipticParamDomain {m : ℂ} (hm : m ∈ EllipticParamDomain) :
    m ≠ 1 := by
  rintro rfl
  simp [EllipticParamDomain] at hm

/-- **The IBP identity:** `(1−m)·∫₀^{π/2} Δ^{−3/2} = E(m)` — the fundamental theorem of
calculus on `g(θ) = sin θ cos θ·Δ^{−1/2}` (vanishing boundary), with the `Δ`-algebra
`m·g′ = Δ^{1/2} − (1−m)Δ^{−3/2}`. The engine behind the `K` Legendre ODE. -/
theorem one_sub_mul_integral_cpow_neg_three_halves {m : ℂ}
    (hm : m ∈ EllipticParamDomain) :
    (1 - m) * (∫ θ in (0:ℝ)..(Real.pi / 2),
        ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(3/2) : ℂ)) = ellipticEm m := by
  have hm0 : m ≠ 0 := ne_zero_of_mem_ellipticParamDomain hm
  set g : ℝ → ℂ := fun θ => (Real.sin θ : ℂ) * (Real.cos θ : ℂ)
    * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ) with hg
  set g' : ℝ → ℂ := fun θ =>
    ((Real.cos θ : ℂ) ^ 2 - (Real.sin θ : ℂ) ^ 2)
      * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)
    + m * (Real.sin θ : ℂ) ^ 2 * (Real.cos θ : ℂ) ^ 2
      * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(3/2) : ℂ) with hg'
  have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ := by
    intro θ _
    have hsin : HasDerivAt (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ))
        ((Real.cos θ : ℝ) : ℂ) θ := (Real.hasDerivAt_sin θ).ofReal_comp
    have hcos : HasDerivAt (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ))
        (-((Real.sin θ : ℝ) : ℂ)) θ := by
      simpa using (Real.hasDerivAt_cos θ).ofReal_comp
    have hsq : HasDerivAt (fun θ : ℝ => ((Real.sin θ : ℂ)) ^ 2)
        (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)) θ := by
      have h := hsin.pow 2
      simpa [pow_one, mul_comm, mul_assoc] using h
    have hΔ : HasDerivAt (fun θ : ℝ => (1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2)
        (-(m * (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)))) θ := by
      simpa using ((hsq.const_mul m).const_sub 1)
    have hslitθ := one_sub_mul_sin_sq_mem_slitPlane hm θ
    have hcpow : HasDerivAt (fun z : ℂ => z ^ (-(1/2) : ℂ))
        ((-(1/2) : ℂ) * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((-(1/2) : ℂ) - 1))
        ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2)).cpow_const hslitθ
    have hW : HasDerivAt (fun θ : ℝ =>
        ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ))
        ((-(1/2) : ℂ) * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((-(1/2) : ℂ) - 1)
          * (-(m * (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ))))) θ := by
      simpa only [Function.comp_def] using HasDerivAt.comp θ hcpow hΔ
    have hprod := (hsin.mul hcos).mul hW
    have hexp : ((-(1/2) : ℂ) - 1) = (-(3/2) : ℂ) := by ring
    rw [hexp] at hprod
    convert hprod using 1
    simp only [hg', Pi.mul_apply]
    ring
  have hgcont : Continuous g' := by
    have h1 := integrand_cpow_continuous hm (-(1/2) : ℂ)
    have h3 := integrand_cpow_continuous hm (-(3/2) : ℂ)
    exact ((by fun_prop : Continuous fun θ : ℝ =>
        ((Real.cos θ : ℂ) ^ 2 - (Real.sin θ : ℂ) ^ 2)).mul h1).add
      ((by fun_prop : Continuous fun θ : ℝ =>
        m * (Real.sin θ : ℂ) ^ 2 * (Real.cos θ : ℂ) ^ 2).mul h3)
  have hibp : (∫ θ in (0:ℝ)..(Real.pi / 2), g' θ) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hgcont.intervalIntegrable _ _)]
    simp [hg]
  -- pointwise: Δ^{1/2} − (1−m)Δ^{−3/2} = m·g′
  have hkey : (∫ θ in (0:ℝ)..(Real.pi / 2),
      (((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)
        - (1 - m) * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(3/2) : ℂ))) = 0 := by
    have hcongr : Set.EqOn
        (fun θ : ℝ => (((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)
          - (1 - m) * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(3/2) : ℂ)))
        (fun θ => m * g' θ) (Set.uIcc (0:ℝ) (Real.pi / 2)) := by
      intro θ _
      have hne : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ≠ 0 :=
        slitPlane_ne_zero' (one_sub_mul_sin_sq_mem_slitPlane hm θ)
      have hcs : ((Real.cos θ : ℂ)) ^ 2 = 1 - ((Real.sin θ : ℂ)) ^ 2 := by
        have h2 : ((Real.sin θ : ℂ)) ^ 2 + ((Real.cos θ : ℂ)) ^ 2 = 1 := by
          exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (Real.sin_sq_add_cos_sq θ)
        linear_combination h2
      have hposhalf : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)
          = ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (2 : ℕ)
            * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(3/2) : ℂ) := by
        conv_lhs => rw [show ((1/2) : ℂ) = ((2:ℕ) : ℂ) + (-(3/2) : ℂ) from by norm_num]
        rw [Complex.cpow_add _ _ hne, Complex.cpow_natCast]
      have hneghalf : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)
          = ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2)
            * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(3/2) : ℂ) := by
        conv_lhs => rw [show (-(1/2) : ℂ) = 1 + (-(3/2) : ℂ) from by ring]
        rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
      simp only [hg']
      rw [hposhalf, hneghalf, hcs]
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
      hibp, mul_zero]
  -- unpack: E − (1−m)·J = 0
  have hsplit : (∫ θ in (0:ℝ)..(Real.pi / 2),
      (((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)
        - (1 - m) * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(3/2) : ℂ)))
      = ellipticEm m - (1 - m) * (∫ θ in (0:ℝ)..(Real.pi / 2),
        ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(3/2) : ℂ)) := by
    rw [intervalIntegral.integral_sub
      ((integrand_cpow_continuous hm ((1/2) : ℂ)).intervalIntegrable _ _)
      (((integrand_cpow_continuous hm (-(3/2) : ℂ)).const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
    rfl
  rw [hsplit] at hkey
  linear_combination -hkey

/-- **The Legendre ODE for `K`, proved:** `dK/dm = (E − (1−m)K)/(2m(1−m))` on the cut
plane — the C1h engine's derivative integral, collapsed by the IBP identity and
`Δ`-algebra. With `ellipticEm_hasDerivAt` this is the full first-order Legendre system,
the input to the C2 (Legendre relation) discharge and to S1. -/
theorem ellipticKm_hasDerivAt {m : ℂ} (hm : m ∈ EllipticParamDomain) :
    HasDerivAt ellipticKm
      ((ellipticEm m - (1 - m) * ellipticKm m) / (2 * m * (1 - m))) m := by
  have hm0 : m ≠ 0 := ne_zero_of_mem_ellipticParamDomain hm
  have hm1 : (1 : ℂ) - m ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_one_of_mem_ellipticParamDomain hm))
  have h := cpow_param_integral_hasDerivAt (-(1/2) : ℂ) hm
  set J : ℂ := ∫ θ in (0:ℝ)..(Real.pi / 2),
    ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(3/2) : ℂ) with hJ
  -- the engine derivative equals (1/(2m))·(J − K)
  have hderiv_eq : (∫ θ in (0:ℝ)..(Real.pi / 2),
      (-(1/2) : ℂ) * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((-(1/2) : ℂ) - 1)
        * (-((Real.sin θ : ℂ) ^ 2)))
      = (1 / (2 * m)) * (J - ellipticKm m) := by
    have hcongr : Set.EqOn
        (fun θ : ℝ => (-(1/2) : ℂ) * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((-(1/2) : ℂ) - 1)
          * (-((Real.sin θ : ℂ) ^ 2)))
        (fun θ => (1 / (2 * m)) * (((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(3/2) : ℂ)
          - ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)))
        (Set.uIcc (0:ℝ) (Real.pi / 2)) := by
      intro θ _
      dsimp only
      have hne : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ≠ 0 :=
        slitPlane_ne_zero' (one_sub_mul_sin_sq_mem_slitPlane hm θ)
      have hexp : ((-(1/2) : ℂ) - 1) = (-(3/2) : ℂ) := by ring
      have hneghalf : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)
          = ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2)
            * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(3/2) : ℂ) := by
        conv_lhs => rw [show (-(1/2) : ℂ) = 1 + (-(3/2) : ℂ) from by ring]
        rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
      rw [hexp, hneghalf]
      field_simp
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul, hJ]
    rw [intervalIntegral.integral_sub
      ((integrand_cpow_continuous hm (-(3/2) : ℂ)).intervalIntegrable _ _)
      ((integrand_cpow_continuous hm (-(1/2) : ℂ)).intervalIntegrable _ _)]
    rfl
  -- substitute (1−m)·J = E
  have hJE : (1 - m) * J = ellipticEm m := one_sub_mul_integral_cpow_neg_three_halves hm
  have hfinal : (ellipticEm m - (1 - m) * ellipticKm m) / (2 * m * (1 - m))
      = (1 / (2 * m)) * (J - ellipticKm m) := by
    rw [← hJE]
    field_simp
  rw [hfinal, ← hderiv_eq]
  exact h

/-- **The Legendre combination is critical everywhere (C2's analytic heart, proved):**
`L(m) = E·K′ + E′·K − K·K′` (primes denoting the complementary argument `1−m`) has
vanishing derivative on the whole cut plane — from the two proved Legendre ODEs; the
numerator collapses by `(a−b)(d−c) + (c−d)(a−b) = 0`. What remains for the full C2
discharge: constancy on the (star-shaped) domain and pinning the constant to `π/2` at
the `m → 0` cusp. -/
theorem legendreRelation_hasDerivAt_zero {m : ℂ} (hm : m ∈ EllipticParamDomain) :
    HasDerivAt (fun m : ℂ => ellipticEm m * ellipticKm (1 - m)
      + ellipticEm (1 - m) * ellipticKm m - ellipticKm m * ellipticKm (1 - m)) 0 m := by
  have hs : (1 - m) ∈ EllipticParamDomain := one_sub_mem_ellipticParamDomain hm
  have hm0 : m ≠ 0 := ne_zero_of_mem_ellipticParamDomain hm
  have hm1 : (1 : ℂ) - m ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (ne_one_of_mem_ellipticParamDomain hm))
  have hinner : HasDerivAt (fun m : ℂ => 1 - m) (-1) m := by
    simpa using (hasDerivAt_id m).const_sub 1
  have hE := ellipticEm_hasDerivAt hm
  have hK := ellipticKm_hasDerivAt hm
  have hE1 : HasDerivAt (fun m : ℂ => ellipticEm (1 - m))
      (-((ellipticEm (1 - m) - ellipticKm (1 - m)) / (2 * (1 - m)))) m := by
    have h := HasDerivAt.comp m (ellipticEm_hasDerivAt hs) hinner
    simpa only [Function.comp_def, mul_neg_one] using h
  have hK1 : HasDerivAt (fun m : ℂ => ellipticKm (1 - m))
      (-((ellipticEm (1 - m) - (1 - (1 - m)) * ellipticKm (1 - m))
        / (2 * (1 - m) * (1 - (1 - m))))) m := by
    have h := HasDerivAt.comp m (ellipticKm_hasDerivAt hs) hinner
    simpa only [Function.comp_def, mul_neg_one] using h
  have hL := ((hE.mul hK1).add (hE1.mul hK)).sub (hK.mul hK1)
  convert hL using 1
  have hmm : (1 : ℂ) - (1 - m) = m := by ring
  rw [hmm]
  field_simp
  ring

/-- **The Legendre combination** `L(m) = E·K′ + E′·K − K·K′` (primes = complementary
argument), packaged. C2 asserts `L ≡ π/2`; `legendreRelation_hasDerivAt_zero` gives
`L′ = 0`, and `legendreL_eq_half` gives constancy on the star-shaped cut plane. -/
noncomputable def legendreL (m : ℂ) : ℂ :=
  ellipticEm m * ellipticKm (1 - m) + ellipticEm (1 - m) * ellipticKm m
    - ellipticKm m * ellipticKm (1 - m)

/-- **Constancy of the Legendre combination (proved):** `L(m) = L(½)` on the cut plane.
The domain is star-shaped about `½` (segment membership proved inline from the
cut-plane structure), `L` has vanishing derivative along every ray by
`legendreRelation_hasDerivAt_zero`, and the one-dimensional mean value theorem
transports the value from the center. With the `m → 0` cusp limit this pins `L ≡ π/2`
and discharges C2. -/
theorem legendreL_eq_half {m : ℂ} (hm : m ∈ EllipticParamDomain) :
    legendreL m = legendreL (1/2 : ℂ) := by
  rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) from by norm_num]
  set c : ℂ := ((1/2 : ℝ) : ℂ) with hc
  set w : ℂ := m - c with hw
  set ψ : ℝ → ℂ := fun t => c + (t : ℂ) * w with hψ
  have hre : ∀ t : ℝ, (ψ t).re = 1/2 + t * (m.re - 1/2) := by
    intro t
    simp [hψ, hw, hc, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im]
  have him : ∀ t : ℝ, (ψ t).im = t * m.im := by
    intro t
    simp [hψ, hw, hc, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im]
  have hψz : ∀ t ∈ Set.Icc (0:ℝ) 1, ψ t ∈ EllipticParamDomain := by
    intro t ht
    simp only [EllipticParamDomain, Set.mem_setOf_eq, not_and, not_or]
    intro himψ
    rw [him] at himψ
    by_cases him0 : m.im = 0
    · have hb := hm
      simp only [EllipticParamDomain, Set.mem_setOf_eq, not_and, not_or, not_le] at hb
      obtain ⟨h1, h2⟩ := hb him0
      rcases eq_or_lt_of_le ht.2 with rfl | htlt
      · refine ⟨?_, ?_⟩
        · rw [not_le, hre]; linarith
        · rw [not_le, hre]; linarith
      · refine ⟨?_, ?_⟩
        · rw [not_le, hre]; nlinarith [mul_nonneg ht.1 h1.le]
        · rw [not_le, hre]; nlinarith [mul_le_mul_of_nonneg_left h2.le ht.1]
    · have ht0 : t = 0 := by
        rcases mul_eq_zero.mp himψ with h | h
        · exact h
        · exact absurd h him0
      subst ht0
      refine ⟨?_, ?_⟩
      · rw [not_le, hre]; norm_num
      · rw [not_le, hre]; norm_num
  have hψd : ∀ t : ℝ, HasDerivAt ψ w t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h2 := (h1.mul_const w).const_add c
    rw [one_mul] at h2
    exact h2
  have hφd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun t => legendreL (ψ t)) 0 t := by
    intro t ht
    have h0 : HasDerivAt legendreL 0 (ψ t) :=
      legendreRelation_hasDerivAt_zero (hψz t ht)
    have h3 := HasDerivAt.comp t h0 (hψd t)
    simpa [Function.comp_def] using h3
  have hcont : ContinuousOn (fun t => legendreL (ψ t)) (Set.Icc 0 1) :=
    fun t ht => ((hφd t ht).continuousAt).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun t ht => ((hφd t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt))
  have h1 := hconst 1 (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)
  have hψ1 : ψ 1 = m := by simp [hψ, hw]
  have hψ0 : ψ 0 = c := by simp [hψ]
  simpa [hψ1, hψ0] using h1

/-- **The exact first-order difference identity:** `E − K = −m·∫ sin²·Δ^{−1/2}` (the
standalone form of the `Δ`-algebra inside the `E` ODE proof). -/
theorem ellipticEm_sub_ellipticKm {m : ℂ} (hm : m ∈ EllipticParamDomain) :
    ellipticEm m - ellipticKm m = -m * ∫ θ in (0:ℝ)..(Real.pi / 2),
      ((Real.sin θ : ℂ) ^ 2) * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ) := by
  have hsub : ellipticEm m - ellipticKm m = ∫ θ in (0:ℝ)..(Real.pi / 2),
      (((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)
        - ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)) := by
    rw [ellipticEm, ellipticKm, ← intervalIntegral.integral_sub
      ((integrand_cpow_continuous hm ((1/2) : ℂ)).intervalIntegrable _ _)
      ((integrand_cpow_continuous hm (-(1/2) : ℂ)).intervalIntegrable _ _)]
  rw [hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hne : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ≠ 0 :=
    slitPlane_ne_zero' (one_sub_mul_sin_sq_mem_slitPlane hm θ)
  have hhalf : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)
      = ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2)
        * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ) := by
    conv_lhs => rw [show ((1/2) : ℂ) = 1 + (-(1/2) : ℂ) from by ring]
    rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
  rw [hhalf]
  ring

/-- Small parameters bound the `K`-integrand uniformly: for `‖m‖ ≤ ½`,
`‖Δ^{−1/2}‖ ≤ √2` — proved by squaring (`Δ^{−1/2}·Δ^{−1/2} = Δ^{−1}`), no `rpow`. -/
theorem norm_integrand_cpow_neg_half_le {m : ℂ} (hm2 : ‖m‖ ≤ 1/2) (θ : ℝ) :
    ‖((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)‖ ≤ Real.sqrt 2 := by
  have hnorm2 : ‖m * (Real.sin θ : ℂ) ^ 2‖ ≤ 1/2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc ‖m‖ * Real.sin θ ^ 2 ≤ (1/2) * 1 :=
          mul_le_mul hm2 (Real.sin_sq_le_one θ) (sq_nonneg _) (by norm_num)
      _ = 1/2 := by norm_num
  have hlow : (1/2 : ℝ) ≤ ‖(1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (m * (Real.sin θ : ℂ) ^ 2)
    rw [norm_one] at h1
    linarith
  have hne : ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  have hsq : ‖((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)‖ ^ 2
      = ‖(1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2‖⁻¹ := by
    rw [sq, ← norm_mul, ← Complex.cpow_add _ _ hne,
      show ((-(1/2) : ℂ) + (-(1/2) : ℂ)) = (-1 : ℂ) from by ring,
      Complex.cpow_neg_one, norm_inv]
  have hsqle : ‖((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)‖ ^ 2 ≤ 2 := by
    rw [hsq]
    calc ‖(1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2‖⁻¹ ≤ (1/2 : ℝ)⁻¹ := by
          gcongr
      _ = 2 := by norm_num
  have h0 : (0:ℝ) ≤ ‖((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)‖ := norm_nonneg _
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, hsqle, h0]

/-- The quantitative vanishing `‖E − K‖ ≤ ‖m‖·√2·(π/2)` for `‖m‖ ≤ ½` — the rate that
controls the divergent product `(E−K)·K′` at the cusp. -/
theorem norm_ellipticEm_sub_ellipticKm_le {m : ℂ} (hm : m ∈ EllipticParamDomain)
    (hm2 : ‖m‖ ≤ 1/2) :
    ‖ellipticEm m - ellipticKm m‖ ≤ ‖m‖ * (Real.sqrt 2 * (Real.pi / 2)) := by
  rw [ellipticEm_sub_ellipticKm hm, norm_mul, norm_neg]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg m)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Real.sqrt 2)
    (f := fun θ : ℝ => ((Real.sin θ : ℂ) ^ 2)
      * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ))
    (a := (0:ℝ)) (b := Real.pi / 2) ?_
  · calc ‖∫ θ in (0:ℝ)..(Real.pi / 2), ((Real.sin θ : ℂ) ^ 2)
        * ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)‖
        ≤ Real.sqrt 2 * |Real.pi / 2 - 0| := hbound
      _ = Real.sqrt 2 * (Real.pi / 2) := by
          rw [sub_zero, abs_of_nonneg (by positivity)]
  · intro θ _
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc Real.sin θ ^ 2 * ‖((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)‖
        ≤ 1 * Real.sqrt 2 := by
          apply mul_le_mul (Real.sin_sq_le_one θ) (norm_integrand_cpow_neg_half_le hm2 θ)
            (norm_nonneg _) (by norm_num)
      _ = Real.sqrt 2 := one_mul _

/-- **`m·log m → 0`** within the cut plane — the elementary squeeze
`r·(−log r) ≤ 2√r` (from `log x ≤ x − 1`), with `|arg| ≤ π` handling the phase. -/
theorem tendsto_mul_log_zero :
    Tendsto (fun m : ℂ => m * Complex.log m) (𝓝[EllipticParamDomain] 0) (𝓝 0) := by
  have hbound : ∀ᶠ m in 𝓝[EllipticParamDomain] (0:ℂ),
      ‖m * Complex.log m‖ ≤ 2 * Real.sqrt ‖m‖ + Real.pi * ‖m‖ := by
    have h1 : ∀ᶠ m in 𝓝 (0:ℂ), ‖m‖ ≤ 1 := by
      filter_upwards [Metric.closedBall_mem_nhds (0:ℂ) one_pos] with x hx
      simpa using mem_closedBall_zero_iff.mp hx
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with x hx1 hxdom
    have hx0 : x ≠ 0 := ne_zero_of_mem_ellipticParamDomain hxdom
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hlog : ‖Complex.log x‖ ≤ -Real.log ‖x‖ + Real.pi := by
      have h2 := Complex.norm_le_abs_re_add_abs_im (Complex.log x)
      rw [Complex.log_re, Complex.log_im] at h2
      have harg := Complex.abs_arg_le_pi x
      have habs : |Real.log ‖x‖| = -Real.log ‖x‖ :=
        abs_of_nonpos (Real.log_nonpos (norm_nonneg x) hx1)
      calc ‖Complex.log x‖ ≤ |Real.log ‖x‖| + |Complex.arg x| := h2
        _ ≤ -Real.log ‖x‖ + Real.pi := by rw [habs]; linarith
    have hr : ‖x‖ * (-Real.log ‖x‖) ≤ 2 * Real.sqrt ‖x‖ := by
      have hsqpos : 0 < Real.sqrt ‖x‖ := Real.sqrt_pos.mpr hxpos
      have hlog2 : -Real.log ‖x‖ = 2 * -Real.log (Real.sqrt ‖x‖) := by
        rw [Real.log_sqrt (norm_nonneg x)]
        ring
      have hle : -Real.log (Real.sqrt ‖x‖) ≤ (Real.sqrt ‖x‖)⁻¹ := by
        rw [← Real.log_inv]
        have h3 := Real.log_le_sub_one_of_pos (inv_pos.mpr hsqpos)
        linarith
      have h6 : ‖x‖ * (Real.sqrt ‖x‖)⁻¹ = Real.sqrt ‖x‖ := by
        rw [inv_eq_one_div, mul_one_div, Real.div_sqrt]
      calc ‖x‖ * (-Real.log ‖x‖) = 2 * (‖x‖ * -Real.log (Real.sqrt ‖x‖)) := by
            rw [hlog2]; ring
        _ ≤ 2 * (‖x‖ * (Real.sqrt ‖x‖)⁻¹) := by
            have := mul_le_mul_of_nonneg_left hle (norm_nonneg x)
            linarith
        _ = 2 * Real.sqrt ‖x‖ := by rw [h6]
    calc ‖x * Complex.log x‖ = ‖x‖ * ‖Complex.log x‖ := norm_mul _ _
      _ ≤ ‖x‖ * (-Real.log ‖x‖ + Real.pi) :=
          mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
      _ = ‖x‖ * (-Real.log ‖x‖) + Real.pi * ‖x‖ := by ring
      _ ≤ 2 * Real.sqrt ‖x‖ + Real.pi * ‖x‖ := by linarith
  have hnorm : Tendsto (fun m : ℂ => ‖m‖) (𝓝[EllipticParamDomain] (0:ℂ)) (𝓝 0) := by
    have h := (continuous_norm.tendsto (0:ℂ))
    rw [norm_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun m : ℂ => 2 * Real.sqrt ‖m‖ + Real.pi * ‖m‖)
      (𝓝[EllipticParamDomain] 0) (𝓝 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hnorm
    rw [Real.sqrt_zero] at hsqrt
    have h2 := (hsqrt.const_mul (2:ℝ)).add (hnorm.const_mul Real.pi)
    simpa using h2
  exact squeeze_zero_norm' hbound hg

/-- **C1h for `K`**: `ellipticKm` is holomorphic on the cut plane — the review's blocking
requirement for rigidity, delivered as a theorem (standard-3), not an axiom. -/
theorem ellipticKm_differentiableOn :
    DifferentiableOn ℂ ellipticKm EllipticParamDomain := fun _ hm =>
  ((cpow_param_integral_hasDerivAt (-(1/2)) hm).differentiableAt).differentiableWithinAt

/-- **C1h for `E`**: `ellipticEm` is holomorphic on the cut plane. -/
theorem ellipticEm_differentiableOn :
    DifferentiableOn ℂ ellipticEm EllipticParamDomain := fun _ hm =>
  ((cpow_param_integral_hasDerivAt (1/2) hm).differentiableAt).differentiableWithinAt

/-- **C1 — Jacobi inversion / the θ-bridge** (Whittaker–Watson §§21–22; v2 with the
nonvanishing of `K` explicit). Every parameter in the cut plane is `λ` of a point of `ℍ`,
where the period is the θ-null and the period ratio is the modulus. The single bridge
between the curve's elliptic integrals and the repo's modular `λ`/`θ` layer.
(NOT VERIFIED in Lean; vetted numerically at 40 digits and by adversarial review.) -/
axiom AX_elliptic_inversion (m : ℂ) (hm : m ∈ EllipticParamDomain) :
    ellipticKm m ≠ 0 ∧
    ∃ τ : UpperHalfPlane, modularLambdaFn (τ : ℂ) = m ∧
      ellipticKm m = (Real.pi / 2 : ℂ) * theta3 (τ : ℂ) ^ 2 ∧
      (τ : ℂ) = Complex.I * ellipticKm (1 - m) / ellipticKm m

-- (C2, the Legendre relation, was an axiom `AX_legendre_relation` here until 2026-07-04;
-- it is now the THEOREM `legendre_relation` at the end of this file, proved from the two
-- Legendre ODEs + constancy on the star-shaped domain + the cusp limit, consuming only
-- C3's single logarithmic clause.)

/-! ## C3 discharge staging (real ray)

Along the positive-real approach everything is real: `K(1−x)` is the real integral
`∫₀^{π/2} (sin²φ + x cos²φ)^{−1/2} dφ` (reflection `φ = π/2 − θ`, which moves the
`x → 0` singularity to the endpoint `φ = 0`), and its log divergence is carried
*exactly* by the elementary model `∫₀^{π/2} (φ² + x)^{−1/2} dφ
= log(π/2 + √(π²/4 + x)) − log √x` (honest FTC — for `x > 0` the antiderivative
`log(φ + √(φ² + x))` is smooth on the whole interval). The remaining steps of the
discharge: the difference of the two integrands is *uniformly bounded* in `x`, so
dominated convergence sends it to `∫₀^{π/2} (1/sin φ − 1/φ) dφ = log(4/π)`, and
`log(4/π) + log π = 2 log 2`. -/

/-- Positivity of the reflected integrand's base on the whole line:
`sin²φ + x·cos²φ ≥ x > 0` for `0 < x ≤ 1`. -/
theorem sin_sq_add_mul_cos_sq_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (φ : ℝ) :
    0 < Real.sin φ ^ 2 + x * Real.cos φ ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq φ,
    mul_nonneg (sub_nonneg.mpr hx1) (sq_nonneg (Real.sin φ))]

/-- **Realization of `K′` on the real ray:** for `0 < x < 1`, the complex `K(1−x)` is
the coerced *real* integral of `(sin²φ + x cos²φ)^{−1/2}` — the base is positive, the
principal `cpow` is the real `rpow`, and the reflection `φ = π/2 − θ` moves the cusp
singularity to `φ = 0` where the model comparison lives. -/
theorem ellipticKm_one_sub_ofReal {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ellipticKm (1 - (x : ℂ))
      = ((∫ φ in (0:ℝ)..(Real.pi/2),
          (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) := by
  have hpos : ∀ θ : ℝ, 0 < Real.cos θ ^ 2 + x * Real.sin θ ^ 2 := by
    intro θ
    nlinarith [Real.sin_sq_add_cos_sq θ,
      mul_nonneg (sub_nonneg.mpr hx1.le) (sq_nonneg (Real.cos θ))]
  have hKint : ellipticKm (1 - (x:ℂ))
      = ∫ θ in (0:ℝ)..(Real.pi/2),
          (((Real.cos θ ^ 2 + x * Real.sin θ ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) := by
    simp only [ellipticKm]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    have hpy : ((Real.sin θ : ℂ)) ^ 2 + ((Real.cos θ : ℂ)) ^ 2 = 1 := by
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (Real.sin_sq_add_cos_sq θ)
    have hbase : (1 : ℂ) - (1 - (x:ℂ)) * (Real.sin θ : ℂ) ^ 2
        = ((Real.cos θ ^ 2 + x * Real.sin θ ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
      linear_combination -hpy
    rw [hbase, show (-(1/2) : ℂ) = ((-(1/2) : ℝ) : ℂ) from by norm_num]
    exact (Complex.ofReal_cpow (hpos θ).le _).symm
  rw [hKint, intervalIntegral.integral_ofReal]
  congr 1
  have h := intervalIntegral.integral_comp_sub_left
    (a := (0:ℝ)) (b := Real.pi/2)
    (fun φ : ℝ => (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ)) (Real.pi/2)
  simp only [sub_self, sub_zero] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

/-- **The model integral** carrying the cusp's log divergence exactly: for `x > 0`,
`∫₀^{π/2} (φ² + x)^{−1/2} dφ = log(π/2 + √(π²/4 + x)) − log √x` — FTC with the
everywhere-smooth antiderivative `log(φ + √(φ² + x))`. -/
theorem integral_rpow_neg_half_sq_add {x : ℝ} (hx : 0 < x) :
    ∫ φ in (0:ℝ)..(Real.pi/2), (φ ^ 2 + x) ^ (-(1/2) : ℝ)
      = Real.log (Real.pi/2 + Real.sqrt ((Real.pi/2) ^ 2 + x))
        - Real.log (Real.sqrt x) := by
  have hF : ∀ φ : ℝ, HasDerivAt (fun t : ℝ => Real.log (t + Real.sqrt (t ^ 2 + x)))
      ((φ ^ 2 + x) ^ (-(1/2) : ℝ)) φ := by
    intro φ
    have hbase : 0 < φ ^ 2 + x := by positivity
    have hs : 0 < Real.sqrt (φ ^ 2 + x) := Real.sqrt_pos.mpr hbase
    have harg : 0 < φ + Real.sqrt (φ ^ 2 + x) := by
      have habs : |φ| < Real.sqrt (φ ^ 2 + x) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_lt_sqrt (sq_nonneg φ) (by linarith)
      cases abs_lt.mp habs with
      | intro h1 h2 => linarith
    have hq : HasDerivAt (fun t : ℝ => t ^ 2 + x) (2 * φ) φ := by
      have h := (hasDerivAt_pow 2 φ).add_const x
      simpa using h
    have hsq : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + x))
        (1 / (2 * Real.sqrt (φ ^ 2 + x)) * (2 * φ)) φ :=
      (Real.hasDerivAt_sqrt hbase.ne').comp φ hq
    have hsum : HasDerivAt (fun t : ℝ => t + Real.sqrt (t ^ 2 + x))
        (1 + 1 / (2 * Real.sqrt (φ ^ 2 + x)) * (2 * φ)) φ :=
      (hasDerivAt_id φ).add hsq
    have hlog := (Real.hasDerivAt_log harg.ne').comp φ hsum
    have hval : (φ + Real.sqrt (φ ^ 2 + x))⁻¹
        * (1 + 1 / (2 * Real.sqrt (φ ^ 2 + x)) * (2 * φ))
        = (φ ^ 2 + x) ^ (-(1/2) : ℝ) := by
      rw [Real.rpow_neg hbase.le, ← Real.sqrt_eq_rpow]
      have hsq2 : Real.sqrt (φ ^ 2 + x) ^ 2 = φ ^ 2 + x := Real.sq_sqrt hbase.le
      field_simp
      ring
    have h := hlog
    rw [Function.comp_def] at h
    convert h using 1
    rw [← hval]
  have hcont : Continuous (fun φ : ℝ => (φ ^ 2 + x) ^ (-(1/2) : ℝ)) := by
    apply Continuous.rpow_const ((continuous_pow 2).add continuous_const)
    intro φ
    dsimp only
    exact Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg φ) hx).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
    (hcont.intervalIntegrable _ _)]
  norm_num

/-- Cancellation helper: from the division-free core `B² − A² ≤ C·A²·B` (with
`0 < A ≤ B`, `0 ≤ C`), conclude `A⁻¹ − B⁻¹ ≤ C`. -/
theorem inv_sub_inv_le_of_sq {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B)
    (hC : 0 ≤ C) (h : B ^ 2 - A ^ 2 ≤ C * (A ^ 2 * B)) : A⁻¹ - B⁻¹ ≤ C := by
  have hABpos : 0 < A + B := by linarith
  have h1 : (B - A) * (A + B) ≤ (C * (A * B)) * (A + B) := by
    have hexp : (B - A) * (A + B) = B ^ 2 - A ^ 2 := by ring
    have hnn : 0 ≤ C * (A * B ^ 2) :=
      mul_nonneg hC (mul_nonneg hA.le (sq_nonneg B))
    nlinarith [hnn, h, hexp]
  have h2 : B - A ≤ C * (A * B) := le_of_mul_le_mul_right h1 hABpos
  rw [inv_sub_inv hA.ne' hB.ne', div_le_iff₀ (mul_pos hA hB)]
  linarith

/-- Standalone certificate for the quantitative regime: `φ² − s² ≤ φ⁴/2` from the
cubic lower bound `φ − φ³/4 ≤ s` and `0 ≤ s ≤ φ` (kept context-free so `nlinarith`
stays fast). -/
theorem cusp_aux_sq_diff {φ s : ℝ} (hs0 : 0 ≤ s) (hsle : s ≤ φ)
    (hcube : φ - φ ^ 3 / 4 ≤ s) : φ ^ 2 - s ^ 2 ≤ φ ^ 4 / 2 := by
  nlinarith [mul_nonneg hs0 hs0]

/-- The division-free core of the C3 comparison bound, with the two square roots
abstracted to opaque `A, B` (only their squares and lower bounds enter):
`B² − A² ≤ π²·A²·B`. Quantitative regime `φ ≤ 1`: cubic bound + Jordan + `B ≥ √x`;
coarse regime `φ ≥ 1`: `B² ≤ π²/4 + 1 ≤ 4 ≤ 4φ³ ≤ π²A²B`. -/
theorem cusp_star_abstract {x φ A B : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hφ0 : 0 ≤ φ) (hφp : φ ≤ Real.pi / 2)
    (hAsq : A ^ 2 = Real.sin φ ^ 2 + x * Real.cos φ ^ 2) (hBsq : B ^ 2 = φ ^ 2 + x)
    (hBφ : φ ≤ B) (hBsx : Real.sqrt x ≤ B) (hA_lb : 2 / Real.pi * φ ≤ A)
    (hs0 : 0 ≤ Real.sin φ) (hsin_le : Real.sin φ ≤ φ) :
    B ^ 2 - A ^ 2 ≤ Real.pi ^ 2 * (A ^ 2 * B) := by
  have hπ := Real.pi_pos
  have hπ2 : (0:ℝ) < Real.pi ^ 2 := by positivity
  have hpy : Real.sin φ ^ 2 + Real.cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  have hA_lb0 : 0 ≤ 2 / Real.pi * φ := by positivity
  have hA2ge : (2 / Real.pi * φ) ^ 2 ≤ A ^ 2 := by
    have := mul_le_mul hA_lb hA_lb hA_lb0 (hA_lb0.trans hA_lb)
    calc (2 / Real.pi * φ) ^ 2 = (2 / Real.pi * φ) * (2 / Real.pi * φ) := pow_two _
      _ ≤ A * A := this
      _ = A ^ 2 := (pow_two A).symm
  have hd1 : (2 / Real.pi * φ) ^ 2 * φ ≤ A ^ 2 * B :=
    mul_le_mul hA2ge hBφ hφ0 (sq_nonneg A)
  have h3 : 4 * φ ^ 3 ≤ Real.pi ^ 2 * (A ^ 2 * B) := by
    have h := mul_le_mul_of_nonneg_left hd1 hπ2.le
    have hcalc : Real.pi ^ 2 * ((2 / Real.pi * φ) ^ 2 * φ) = 4 * φ ^ 3 := by
      field_simp
      ring
    linarith only [h, hcalc.le, hcalc.ge]
  rcases le_total φ 1 with hc | hc
  · -- quantitative regime
    have hcube : φ - φ ^ 3 / 4 ≤ Real.sin φ := by
      rcases hφ0.eq_or_lt with h | h
      · simp [← h]
      · exact (Real.sin_gt_sub_cube h hc).le
    have hk1 : φ ^ 2 - Real.sin φ ^ 2 ≤ φ ^ 4 / 2 := cusp_aux_sq_diff hs0 hsin_le hcube
    have hs2 : Real.sin φ ^ 2 ≤ φ ^ 2 := by
      have := mul_le_mul hsin_le hsin_le hs0 hφ0
      calc Real.sin φ ^ 2 = Real.sin φ * Real.sin φ := pow_two _
        _ ≤ φ * φ := this
        _ = φ ^ 2 := (pow_two φ).symm
    have hk2 : x * Real.sin φ ^ 2 ≤ x * φ ^ 2 := mul_le_mul_of_nonneg_left hs2 hx0.le
    have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have hsx1 : Real.sqrt x ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hx1
    have hsx0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hd2 : (2 / Real.pi * φ) ^ 2 * Real.sqrt x ≤ A ^ 2 * B :=
      mul_le_mul hA2ge hBsx hsx0 (sq_nonneg A)
    have h4 : 4 * φ ^ 2 * Real.sqrt x ≤ Real.pi ^ 2 * (A ^ 2 * B) := by
      have h := mul_le_mul_of_nonneg_left hd2 hπ2.le
      have hcalc : Real.pi ^ 2 * ((2 / Real.pi * φ) ^ 2 * Real.sqrt x)
          = 4 * φ ^ 2 * Real.sqrt x := by
        field_simp
        ring
      linarith only [h, hcalc.le, hcalc.ge]
    have hnum : B ^ 2 - A ^ 2 = (φ ^ 2 - Real.sin φ ^ 2) + x * Real.sin φ ^ 2 := by
      rw [hAsq, hBsq]
      linear_combination (-x) * hpy
    have hp43 : φ ^ 4 ≤ φ ^ 3 := pow_le_pow_of_le_one hφ0 hc (by norm_num)
    have h5 : φ ^ 4 / 2 ≤ 2 * φ ^ 3 := by
      have h30 : 0 ≤ φ ^ 3 := pow_nonneg hφ0 3
      linarith only [hp43, h30]
    have h8 : Real.sqrt x * Real.sqrt x ≤ 1 * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hsx1 hsx0
    have h9 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hx2sx : x ≤ 2 * Real.sqrt x := by linarith only [h8, h9.le, h9.ge, hsx0]
    have h7 : x * φ ^ 2 ≤ 2 * Real.sqrt x * φ ^ 2 :=
      mul_le_mul_of_nonneg_right hx2sx (sq_nonneg φ)
    linarith only [hnum.le, hnum.ge, hk1, hk2, h3, h4, h5, h7]
  · -- coarse regime
    have hφ2 : φ ^ 2 ≤ (Real.pi / 2) ^ 2 := by
      have := mul_le_mul hφp hφp hφ0 (by positivity)
      calc φ ^ 2 = φ * φ := pow_two _
        _ ≤ Real.pi / 2 * (Real.pi / 2) := this
        _ = (Real.pi / 2) ^ 2 := (pow_two _).symm
    have hB2le : B ^ 2 ≤ Real.pi ^ 2 / 4 + 1 := by
      rw [hBsq]
      have hexp : (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 := by ring
      linarith only [hφ2, hx1, hexp.le, hexp.ge]
    have hpil : Real.pi * Real.pi ≤ 3.15 * 3.15 :=
      mul_le_mul Real.pi_lt_d2.le Real.pi_lt_d2.le Real.pi_pos.le (by norm_num)
    have h44 : Real.pi ^ 2 / 4 + 1 ≤ 4 := by
      have hexp : Real.pi ^ 2 = Real.pi * Real.pi := pow_two Real.pi
      nlinarith [hpil, hexp]
    have hφ31 : (1:ℝ) ≤ φ ^ 3 := one_le_pow₀ hc
    linarith only [hB2le, h44, hφ31, h3, sq_nonneg A]

/-- **Uniform bound for the C3 comparison** (the dominating function is a *constant*):
for `0 < x ≤ 1` and `φ ∈ [0, π/2]`, the difference of the reflected `K′` integrand and
the model integrand satisfies
`0 ≤ (sin²φ + x cos²φ)^{−1/2} − (φ² + x)^{−1/2} ≤ π²`, uniformly in `x` — the two log
divergences kill each other pointwise. Core: `cusp_star_abstract` + the cancellation
`inv_sub_inv_le_of_sq`. -/
theorem cusp_diff_integrand_bound {x φ : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hφ0 : 0 ≤ φ) (hφp : φ ≤ Real.pi / 2) :
    0 ≤ (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ)
        - (φ ^ 2 + x) ^ (-(1/2) : ℝ)
    ∧ (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ)
        - (φ ^ 2 + x) ^ (-(1/2) : ℝ) ≤ Real.pi ^ 2 := by
  have hA2 : 0 < Real.sin φ ^ 2 + x * Real.cos φ ^ 2 :=
    sin_sq_add_mul_cos_sq_pos hx0 hx1 φ
  have hB2 : 0 < φ ^ 2 + x := add_pos_of_nonneg_of_pos (sq_nonneg φ) hx0
  have hs0 : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (hφp.trans (by linarith [Real.pi_pos]))
  have hsin_le : Real.sin φ ≤ φ := by
    rcases hφ0.eq_or_lt with h | h
    · simp [← h]
    · exact (Real.sin_lt h).le
  have hs2 : Real.sin φ ^ 2 ≤ φ ^ 2 := by
    have := mul_le_mul hsin_le hsin_le hs0 (hs0.trans hsin_le)
    calc Real.sin φ ^ 2 = Real.sin φ * Real.sin φ := pow_two _
      _ ≤ φ * φ := this
      _ = φ ^ 2 := (pow_two φ).symm
  have hxc : x * Real.cos φ ^ 2 ≤ x :=
    (mul_le_mul_of_nonneg_left (Real.cos_sq_le_one φ) hx0.le).trans_eq (mul_one x)
  have hle : Real.sin φ ^ 2 + x * Real.cos φ ^ 2 ≤ φ ^ 2 + x := by
    linarith only [hs2, hxc]
  have hrwA : (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ)
      = (Real.sqrt (Real.sin φ ^ 2 + x * Real.cos φ ^ 2))⁻¹ := by
    rw [Real.rpow_neg hA2.le, ← Real.sqrt_eq_rpow]
  have hrwB : (φ ^ 2 + x) ^ (-(1/2) : ℝ) = (Real.sqrt (φ ^ 2 + x))⁻¹ := by
    rw [Real.rpow_neg hB2.le, ← Real.sqrt_eq_rpow]
  have hA : 0 < Real.sqrt (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) := Real.sqrt_pos.mpr hA2
  have hB : 0 < Real.sqrt (φ ^ 2 + x) := Real.sqrt_pos.mpr hB2
  have hABle : Real.sqrt (Real.sin φ ^ 2 + x * Real.cos φ ^ 2)
      ≤ Real.sqrt (φ ^ 2 + x) := Real.sqrt_le_sqrt hle
  rw [hrwA, hrwB]
  constructor
  · have h : (Real.sqrt (φ ^ 2 + x))⁻¹
        ≤ (Real.sqrt (Real.sin φ ^ 2 + x * Real.cos φ ^ 2))⁻¹ := by gcongr
    linarith only [h]
  · refine inv_sub_inv_le_of_sq hA hB hABle (sq_nonneg Real.pi) ?_
    refine cusp_star_abstract hx0 hx1 hφ0 hφp (Real.sq_sqrt hA2.le) (Real.sq_sqrt hB2.le)
      ?_ (Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg φ))) ?_ hs0 hsin_le
    · have h := Real.sqrt_le_sqrt (le_add_of_nonneg_right hx0.le : φ ^ 2 ≤ φ ^ 2 + x)
      rwa [Real.sqrt_sq hφ0] at h
    · have hAs : Real.sin φ ≤ Real.sqrt (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) := by
        have h := Real.sqrt_le_sqrt (le_add_of_nonneg_right
          (mul_nonneg hx0.le (sq_nonneg (Real.cos φ))) : Real.sin φ ^ 2
            ≤ Real.sin φ ^ 2 + x * Real.cos φ ^ 2)
        rwa [Real.sqrt_sq hs0] at h
      exact (Real.mul_le_sin hφ0 hφp).trans hAs

/-- **The C3 comparison integral converges** (dominated convergence, constant `π²`
dominator from `cusp_diff_integrand_bound`): as `x ↓ 0`,
`∫₀^{π/2} [(sin²φ + x cos²φ)^{−1/2} − (φ²+x)^{−1/2}] dφ → ∫₀^{π/2} (1/sinφ − 1/φ) dφ`.
The remaining log divergence lives entirely in the (elementarily evaluated) model. -/
theorem cusp_diff_integral_tendsto :
    Tendsto (fun x : ℝ => ∫ φ in (0:ℝ)..(Real.pi/2),
        ((Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ)
          - (φ ^ 2 + x) ^ (-(1/2) : ℝ)))
      (𝓝[>] (0:ℝ))
      (𝓝 (∫ φ in (0:ℝ)..(Real.pi/2), ((Real.sin φ)⁻¹ - φ⁻¹))) := by
  have key := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := Real.pi / 2)
    (l := 𝓝[>] (0:ℝ))
    (F := fun (x : ℝ) (φ : ℝ) => (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ)
      - (φ ^ 2 + x) ^ (-(1/2) : ℝ))
    (f := fun φ : ℝ => (Real.sin φ)⁻¹ - φ⁻¹)
    (bound := fun _ => Real.pi ^ 2)
    ?_ ?_ ?_ ?_
  · exact key
  · have hev : ∀ᶠ x in 𝓝[>] (0:ℝ), x ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hev] with x hx
    have hcont : Continuous fun φ : ℝ =>
        (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ)
          - (φ ^ 2 + x) ^ (-(1/2) : ℝ) := by
      apply Continuous.sub
      · apply Continuous.rpow_const ((Real.continuous_sin.pow 2).add
          (continuous_const.mul (Real.continuous_cos.pow 2)))
        intro φ
        exact Or.inl (sin_sq_add_mul_cos_sq_pos hx.1 hx.2.le φ).ne'
      · apply Continuous.rpow_const ((continuous_pow 2).add continuous_const)
        intro φ
        exact Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg φ) hx.1).ne'
    exact hcont.aestronglyMeasurable
  · have hev : ∀ᶠ x in 𝓝[>] (0:ℝ), x ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hev] with x hx
    refine MeasureTheory.ae_of_all _ fun φ hφmem => ?_
    have hφIoc : φ ∈ Set.Ioc (0:ℝ) (Real.pi / 2) := by
      rwa [Set.uIoc_of_le (by positivity)] at hφmem
    obtain ⟨h0, h1⟩ := cusp_diff_integrand_bound hx.1 hx.2.le hφIoc.1.le hφIoc.2
    rw [Real.norm_of_nonneg h0]
    exact h1
  · exact intervalIntegral.intervalIntegrable_const
  · refine MeasureTheory.ae_of_all _ fun φ hφmem => ?_
    have hφIoc : φ ∈ Set.Ioc (0:ℝ) (Real.pi / 2) := by
      rwa [Set.uIoc_of_le (by positivity)] at hφmem
    have hφ0 : 0 < φ := hφIoc.1
    have hsin : 0 < Real.sin φ :=
      Real.sin_pos_of_pos_of_lt_pi hφ0
        (lt_of_le_of_lt hφIoc.2 (by linarith [Real.pi_pos]))
    have hb1 : Tendsto (fun x : ℝ => Real.sin φ ^ 2 + x * Real.cos φ ^ 2)
        (𝓝[>] (0:ℝ)) (𝓝 (Real.sin φ ^ 2)) := by
      have hcont : Continuous (fun x : ℝ => Real.sin φ ^ 2 + x * Real.cos φ ^ 2) :=
        continuous_const.add (continuous_id.mul continuous_const)
      have h := hcont.tendsto (0:ℝ)
      simp only [zero_mul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have ht1 : Tendsto (fun x : ℝ =>
        (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ))
        (𝓝[>] (0:ℝ)) (𝓝 ((Real.sin φ ^ 2) ^ (-(1/2) : ℝ))) :=
      hb1.rpow_const (Or.inl (pow_ne_zero 2 hsin.ne'))
    have hb2 : Tendsto (fun x : ℝ => φ ^ 2 + x) (𝓝[>] (0:ℝ)) (𝓝 (φ ^ 2)) := by
      have hcont : Continuous (fun x : ℝ => φ ^ 2 + x) :=
        continuous_const.add continuous_id
      have h := hcont.tendsto (0:ℝ)
      simp only [add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have ht2 : Tendsto (fun x : ℝ => (φ ^ 2 + x) ^ (-(1/2) : ℝ))
        (𝓝[>] (0:ℝ)) (𝓝 ((φ ^ 2) ^ (-(1/2) : ℝ))) :=
      hb2.rpow_const (Or.inl (pow_ne_zero 2 hφ0.ne'))
    have hv1 : (Real.sin φ ^ 2) ^ (-(1/2) : ℝ) = (Real.sin φ)⁻¹ := by
      rw [Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq hsin.le]
    have hv2 : (φ ^ 2) ^ (-(1/2) : ℝ) = φ⁻¹ := by
      rw [Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq hφ0.le]
    have h := ht1.sub ht2
    rw [hv1, hv2] at h
    exact h

/-- Pointwise bound for the limit integrand: `0 ≤ 1/sin φ − 1/φ ≤ π²` on `(0, π/2]`
(the `x → 0` shadow of `cusp_diff_integrand_bound`, proved directly: Jordan + the
cubic bound below `1`, the coarse `1/sin ≤ π/2` above `1`). -/
theorem cusp_limit_integrand_bound {φ : ℝ} (hφ0 : 0 < φ) (hφp : φ ≤ Real.pi / 2) :
    0 ≤ (Real.sin φ)⁻¹ - φ⁻¹ ∧ (Real.sin φ)⁻¹ - φ⁻¹ ≤ Real.pi ^ 2 := by
  have hπ := Real.pi_pos
  have hsin : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ0 (lt_of_le_of_lt hφp (by linarith))
  have hsle : Real.sin φ ≤ φ := (Real.sin_lt hφ0).le
  have hJ : 2 / Real.pi * φ ≤ Real.sin φ := Real.mul_le_sin hφ0.le hφp
  constructor
  · have h : φ⁻¹ ≤ (Real.sin φ)⁻¹ := by gcongr
    linarith only [h]
  · rcases le_total φ 1 with hc | hc
    · have hcube : φ - φ ^ 3 / 4 ≤ Real.sin φ := (Real.sin_gt_sub_cube hφ0 hc).le
      have h1 : φ - Real.sin φ ≤ φ ^ 3 / 4 := by linarith only [hcube]
      have h2 : 2 / Real.pi * φ * φ ≤ Real.sin φ * φ :=
        mul_le_mul_of_nonneg_right hJ hφ0.le
      have h3 : Real.pi ^ 2 * (2 / Real.pi * φ * φ) ≤ Real.pi ^ 2 * (Real.sin φ * φ) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      have h4 : Real.pi ^ 2 * (2 / Real.pi * φ * φ) = 2 * Real.pi * φ ^ 2 := by
        field_simp
      have h5 : φ ^ 3 ≤ φ ^ 2 := pow_le_pow_of_le_one hφ0.le hc (by norm_num)
      have hπ3 : 3 < Real.pi := Real.pi_gt_three
      have h6 : 6 * φ ^ 2 ≤ 2 * Real.pi * φ ^ 2 := by nlinarith [sq_nonneg φ, hπ3]
      rw [inv_sub_inv hsin.ne' hφ0.ne', div_le_iff₀ (mul_pos hsin hφ0)]
      linarith only [h1, h3, h4.le, h4.ge, h5, h6, sq_nonneg φ]
    · have hJpos : 0 < 2 / Real.pi * φ := by positivity
      have h1 : (Real.sin φ)⁻¹ ≤ (2 / Real.pi * φ)⁻¹ := by gcongr
      have h2 : (2 / Real.pi * φ)⁻¹ = Real.pi / (2 * φ) := by
        field_simp
      have h3 : Real.pi / (2 * φ) ≤ Real.pi / 2 := by
        apply div_le_div_of_nonneg_left hπ.le (by linarith) (by linarith)
      have h4 : (0:ℝ) < φ⁻¹ := inv_pos.mpr hφ0
      have h5 : Real.pi / 2 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      linarith only [h1, h2.le, h2.ge, h3, h4, h5]

/-- The limit integrand is interval-integrable on `[0, π/2]` (bounded measurable;
Lean's junk value at `φ = 0` is `0`, inside the bound). -/
theorem cusp_limit_integrand_intervalIntegrable :
    IntervalIntegrable (fun φ : ℝ => (Real.sin φ)⁻¹ - φ⁻¹)
      MeasureTheory.volume 0 (Real.pi / 2) := by
  rw [intervalIntegrable_iff]
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) (Real.pi/2))) := by
    constructor
    rw [MeasureTheory.Measure.restrict_apply_univ, Set.uIoc_of_le (by positivity),
      Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  refine ⟨((Real.measurable_sin.inv).sub measurable_inv).aestronglyMeasurable, ?_⟩
  apply MeasureTheory.HasFiniteIntegral.of_bounded (C := Real.pi ^ 2)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  refine MeasureTheory.ae_of_all _ fun φ hφ => ?_
  rw [Set.uIoc_of_le (by positivity)] at hφ
  obtain ⟨h0, h1⟩ := cusp_limit_integrand_bound hφ.1 hφ.2
  rw [Real.norm_of_nonneg h0]
  exact h1

/-- **FTC on `[ε, π/2]`** for the limit integrand, with the classical antiderivative
`log(tan(φ/2)) − log φ` (its derivative is `1/sin φ − 1/φ` via
`sin φ = 2 sin(φ/2) cos(φ/2)`): the integral from `ε` is
`−log(π/2) − (log tan(ε/2) − log ε)`. -/
theorem cusp_eps_integral {ε : ℝ} (hε0 : 0 < ε) (hεp : ε ≤ Real.pi / 2) :
    ∫ φ in ε..(Real.pi/2), ((Real.sin φ)⁻¹ - φ⁻¹)
      = -Real.log (Real.pi / 2) - (Real.log (Real.tan (ε / 2)) - Real.log ε) := by
  have hπ := Real.pi_pos
  have hF : ∀ t ∈ Set.uIcc ε (Real.pi/2),
      HasDerivAt (fun φ : ℝ => Real.log (Real.tan (φ / 2)) - Real.log φ)
        ((Real.sin t)⁻¹ - t⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le hεp] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hε0 ht.1
    have htp : t ≤ Real.pi / 2 := ht.2
    have hh0 : 0 < t / 2 := by linarith
    have hhp : t / 2 < Real.pi / 2 := by linarith
    have hcos : 0 < Real.cos (t / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hhp⟩
    have hsinh : 0 < Real.sin (t / 2) :=
      Real.sin_pos_of_pos_of_lt_pi hh0 (by linarith)
    have hsint : 0 < Real.sin t :=
      Real.sin_pos_of_pos_of_lt_pi ht0 (lt_of_le_of_lt htp (by linarith))
    have htan : 0 < Real.tan (t / 2) := by
      rw [Real.tan_eq_sin_div_cos]
      positivity
    have hhalf : HasDerivAt (fun φ : ℝ => φ / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const 2
    have htand : HasDerivAt Real.tan (1 / Real.cos (t / 2) ^ 2) (t / 2) :=
      Real.hasDerivAt_tan hcos.ne'
    have hcomp := HasDerivAt.comp t htand hhalf
    have hlog1 := (Real.hasDerivAt_log htan.ne').comp t hcomp
    rw [Function.comp_def] at hlog1
    have hlog2 := Real.hasDerivAt_log ht0.ne'
    have h := hlog1.sub hlog2
    convert h using 1
    have hsin2 : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
      have h2 := Real.sin_two_mul (t / 2)
      rw [show 2 * (t / 2) = t from by ring] at h2
      linarith only [h2]
    rw [Real.tan_eq_sin_div_cos, hsin2]
    field_simp
  have hint : IntervalIntegrable (fun φ : ℝ => (Real.sin φ)⁻¹ - φ⁻¹)
      MeasureTheory.volume ε (Real.pi/2) := by
    apply cusp_limit_integrand_intervalIntegrable.mono_set
    rw [Set.uIcc_of_le hεp, Set.uIcc_of_le (by positivity)]
    exact Set.Icc_subset_Icc hε0.le le_rfl
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  rw [show Real.pi / 2 / 2 = Real.pi / 4 from by ring, Real.tan_pi_div_four,
    Real.log_one]
  ring

/-- **The limit integral evaluated:** `∫₀^{π/2} (1/sin φ − 1/φ) dφ = log 2 − log(π/2)`
(i.e. `log(4/π)`). ε-endpoint limit of the FTC formula: the tail `∫₀^ε` is `O(ε)` by
the constant bound, and `log tan(ε/2) − log ε → −log 2` via the slope of `tan` at `0`. -/
theorem cusp_limit_integral_eval :
    ∫ φ in (0:ℝ)..(Real.pi/2), ((Real.sin φ)⁻¹ - φ⁻¹)
      = Real.log 2 - Real.log (Real.pi / 2) := by
  have hπ := Real.pi_pos
  have hπ2 : (0:ℝ) < Real.pi / 2 := by linarith
  -- (a) the ε-integrals tend to the full integral: the tail is O(ε)
  have ha : Tendsto (fun ε : ℝ => ∫ φ in ε..(Real.pi/2), ((Real.sin φ)⁻¹ - φ⁻¹))
      (𝓝[>] (0:ℝ))
      (𝓝 (∫ φ in (0:ℝ)..(Real.pi/2), ((Real.sin φ)⁻¹ - φ⁻¹))) := by
    have htail : Tendsto (fun ε : ℝ => ∫ φ in (0:ℝ)..ε, ((Real.sin φ)⁻¹ - φ⁻¹))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hb1 : ∀ᶠ ε in 𝓝[>] (0:ℝ),
          ‖∫ φ in (0:ℝ)..ε, ((Real.sin φ)⁻¹ - φ⁻¹)‖ ≤ Real.pi ^ 2 * |ε| := by
        filter_upwards [Ioo_mem_nhdsGT hπ2] with ε hε
        have hbnd : ∀ y ∈ Set.uIoc (0:ℝ) ε, ‖(Real.sin y)⁻¹ - y⁻¹‖ ≤ Real.pi ^ 2 := by
          intro y hy
          rw [Set.uIoc_of_le hε.1.le] at hy
          obtain ⟨h0, h1⟩ := cusp_limit_integrand_bound hy.1 (hy.2.trans hε.2.le)
          rw [Real.norm_of_nonneg h0]
          exact h1
        have h := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
        simpa using h
      have hb2 : Tendsto (fun ε : ℝ => Real.pi ^ 2 * |ε|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have hcont : Continuous (fun ε : ℝ => Real.pi ^ 2 * |ε|) :=
          continuous_const.mul continuous_abs
        have h := hcont.tendsto (0:ℝ)
        simp only [abs_zero, mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact squeeze_zero_norm' hb1 hb2
    have hsplit : ∀ᶠ ε in 𝓝[>] (0:ℝ),
        (∫ φ in (0:ℝ)..(Real.pi/2), ((Real.sin φ)⁻¹ - φ⁻¹))
          - (∫ φ in (0:ℝ)..ε, ((Real.sin φ)⁻¹ - φ⁻¹))
        = ∫ φ in ε..(Real.pi/2), ((Real.sin φ)⁻¹ - φ⁻¹) := by
      filter_upwards [Ioo_mem_nhdsGT hπ2] with ε hε
      have h1 : IntervalIntegrable (fun φ : ℝ => (Real.sin φ)⁻¹ - φ⁻¹)
          MeasureTheory.volume 0 ε := by
        apply cusp_limit_integrand_intervalIntegrable.mono_set
        rw [Set.uIcc_of_le hε.1.le, Set.uIcc_of_le hπ2.le]
        exact Set.Icc_subset_Icc le_rfl hε.2.le
      have h2 : IntervalIntegrable (fun φ : ℝ => (Real.sin φ)⁻¹ - φ⁻¹)
          MeasureTheory.volume ε (Real.pi/2) := by
        apply cusp_limit_integrand_intervalIntegrable.mono_set
        rw [Set.uIcc_of_le hε.2.le, Set.uIcc_of_le hπ2.le]
        exact Set.Icc_subset_Icc hε.1.le le_rfl
      have h := intervalIntegral.integral_add_adjacent_intervals h1 h2
      linarith only [h]
    have hbase := tendsto_const_nhds
      (x := ∫ φ in (0:ℝ)..(Real.pi/2), ((Real.sin φ)⁻¹ - φ⁻¹))
      (f := 𝓝[>] (0:ℝ)) |>.sub htail
    rw [sub_zero] at hbase
    exact Filter.Tendsto.congr' hsplit hbase
  -- (b) the FTC closed forms tend to log 2 − log(π/2)
  have hb : Tendsto (fun ε : ℝ =>
        -Real.log (Real.pi/2) - (Real.log (Real.tan (ε/2)) - Real.log ε))
      (𝓝[>] (0:ℝ)) (𝓝 (Real.log 2 - Real.log (Real.pi/2))) := by
    have hd : HasDerivAt Real.tan 1 0 := by
      have h := Real.hasDerivAt_tan (by simp : Real.cos 0 ≠ 0)
      simpa using h
    have hslope := hasDerivAt_iff_tendsto_slope.mp hd
    have hhalf : Tendsto (fun ε : ℝ => ε/2) (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hcont : Continuous (fun ε : ℝ => ε/2) := continuous_id.div_const 2
        have h := hcont.tendsto (0:ℝ)
        simp only [zero_div] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact div_ne_zero (ne_of_gt hε) two_ne_zero
    have hs2 : Tendsto (fun ε : ℝ => Real.tan (ε/2) / (ε/2))
        (𝓝[>] (0:ℝ)) (𝓝 1) := by
      have h := hslope.comp hhalf
      apply h.congr
      intro ε
      simp [slope_def_field, Real.tan_zero]
    have hlog0 : Tendsto (fun ε : ℝ => Real.log (Real.tan (ε/2) / (ε/2)))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hcont : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
      have h := hcont.tendsto.comp hs2
      simpa [Function.comp_def, Real.log_one] using h
    have heq : ∀ᶠ ε in 𝓝[>] (0:ℝ),
        Real.log (Real.tan (ε/2) / (ε/2)) - Real.log 2
          = Real.log (Real.tan (ε/2)) - Real.log ε := by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 2 from by norm_num)] with ε hε
      have hε0 : 0 < ε := hε.1
      have h2 : 0 < ε/2 := by linarith
      have hlt : ε/2 < Real.pi/2 := by linarith [Real.pi_gt_three, hε.2]
      have htanpos : 0 < Real.tan (ε/2) :=
        Real.tan_pos_of_pos_of_lt_pi_div_two h2 hlt
      rw [Real.log_div htanpos.ne' (by positivity : (ε/2:ℝ) ≠ 0),
        Real.log_div hε0.ne' two_ne_zero]
      ring
    have hcomb : Tendsto (fun ε : ℝ => Real.log (Real.tan (ε/2)) - Real.log ε)
        (𝓝[>] (0:ℝ)) (𝓝 (-Real.log 2)) := by
      have h := hlog0.sub_const (Real.log 2)
      rw [zero_sub] at h
      exact Filter.Tendsto.congr' heq h
    have h := (tendsto_const_nhds (x := -Real.log (Real.pi/2))
      (f := 𝓝[>] (0:ℝ))).sub hcomb
    have hval : -Real.log (Real.pi/2) - -Real.log 2
        = Real.log 2 - Real.log (Real.pi/2) := by ring
    rwa [hval] at h
  -- (c) both limits along the same nontrivial filter: uniqueness
  have hformula : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      (∫ φ in ε..(Real.pi/2), ((Real.sin φ)⁻¹ - φ⁻¹))
        = -Real.log (Real.pi/2) - (Real.log (Real.tan (ε/2)) - Real.log ε) := by
    filter_upwards [Ioo_mem_nhdsGT hπ2] with ε hε
    exact cusp_eps_integral hε.1 hε.2.le
  have ha' := Filter.Tendsto.congr' hformula ha
  exact tendsto_nhds_unique ha' hb

/-- **The real cusp asymptotic, assembled:** `∫₀^{π/2}(sin²φ + x cos²φ)^{−1/2}dφ
+ ½ log x → 2 log 2` as `x ↓ 0` — the reflected `K(1−x)` integral plus half-log. The
split into comparison + model cancels `−log√x` against `½ log x` exactly, the
comparison tends to `log(4/π)` and the model constant to `log π`; `log(4/π) + log π
= 2 log 2`. -/
theorem cusp_asymptotic_real :
    Tendsto (fun x : ℝ =>
        (∫ φ in (0:ℝ)..(Real.pi/2),
          (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ))
        + 1/2 * Real.log x)
      (𝓝[>] (0:ℝ)) (𝓝 (2 * Real.log 2)) := by
  have hπ := Real.pi_pos
  have hlog : Tendsto
      (fun x : ℝ => Real.log (Real.pi/2 + Real.sqrt ((Real.pi/2) ^ 2 + x)))
      (𝓝[>] (0:ℝ)) (𝓝 (Real.log Real.pi)) := by
    have h1 : ContinuousAt (fun x : ℝ => (Real.pi/2) ^ 2 + x) 0 :=
      continuousAt_const.add continuousAt_id
    have h3 : ContinuousAt (fun x : ℝ => Real.sqrt ((Real.pi/2) ^ 2 + x)) 0 :=
      Real.continuous_sqrt.continuousAt.comp h1
    have h4 : ContinuousAt
        (fun x : ℝ => Real.pi/2 + Real.sqrt ((Real.pi/2) ^ 2 + x)) 0 :=
      continuousAt_const.add h3
    have hsq : Real.sqrt ((Real.pi/2) ^ 2 + 0) = Real.pi/2 := by
      rw [add_zero, Real.sqrt_sq (by positivity : (0:ℝ) ≤ Real.pi/2)]
    have h5 : Real.pi/2 + Real.sqrt ((Real.pi/2) ^ 2 + 0) ≠ 0 := by
      rw [hsq]
      linarith
    have h := (h4.log h5).tendsto
    have hval : Real.log (Real.pi/2 + Real.sqrt ((Real.pi/2) ^ 2 + 0))
        = Real.log Real.pi := by
      rw [hsq, show Real.pi/2 + Real.pi/2 = Real.pi from by ring]
    rw [hval] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hD := cusp_diff_integral_tendsto
  rw [cusp_limit_integral_eval] at hD
  have hsum := hD.add hlog
  have hval : Real.log 2 - Real.log (Real.pi/2) + Real.log Real.pi
      = 2 * Real.log 2 := by
    rw [Real.log_div (by positivity : Real.pi ≠ 0) two_ne_zero]
    ring
  rw [hval] at hsum
  apply Filter.Tendsto.congr' ?_ hsum
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  have hFcont : Continuous fun φ : ℝ =>
      (Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ) := by
    apply Continuous.rpow_const ((Real.continuous_sin.pow 2).add
      (continuous_const.mul (Real.continuous_cos.pow 2)))
    intro φ
    exact Or.inl (sin_sq_add_mul_cos_sq_pos hx.1 hx.2.le φ).ne'
  have hGcont : Continuous fun φ : ℝ => (φ ^ 2 + x) ^ (-(1/2) : ℝ) := by
    apply Continuous.rpow_const ((continuous_pow 2).add continuous_const)
    intro φ
    exact Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg φ) hx.1).ne'
  have hsub := intervalIntegral.integral_sub
    (hFcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (Real.pi/2))
    (hGcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (Real.pi/2))
  show (∫ φ in (0:ℝ)..(Real.pi/2),
      ((Real.sin φ ^ 2 + x * Real.cos φ ^ 2) ^ (-(1/2) : ℝ)
        - (φ ^ 2 + x) ^ (-(1/2) : ℝ)))
      + Real.log (Real.pi/2 + Real.sqrt ((Real.pi/2) ^ 2 + x)) = _
  rw [hsub, integral_rpow_neg_half_sq_add hx.1, Real.log_sqrt hx.1.le]
  ring

/-- **The positive-real approach to the cusp `m = 0`**: the pushforward of `𝓝[>] 0` on
`ℝ` along the real embedding. This is the filter on which the one remaining C3 clause
is stated — the constancy of the Legendre combination on the whole cut plane (proved,
`legendreL_eq_half`) means the cusp constant only needs to be pinned along *one*
nontrivial approach, and the positive-real ray is the classical (Whittaker–Watson)
regime where every quantity is real. -/
def realCuspApproach : Filter ℂ := Filter.map (fun x : ℝ => (x : ℂ)) (𝓝[>] (0:ℝ))

/-- The real approach stays inside the cut plane and converges to `0`: it refines the
domain filter, so every limit already proved at `𝓝[EllipticParamDomain] 0` transfers. -/
theorem realCuspApproach_le : realCuspApproach ≤ 𝓝[EllipticParamDomain] (0:ℂ) := by
  rw [realCuspApproach, Filter.map_le_iff_le_comap, ← Filter.tendsto_iff_comap]
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  · have hIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) :=
      Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hIoo] with x hx
    simp only [EllipticParamDomain, Set.mem_setOf_eq, not_and, not_or,
      Complex.ofReal_re, Complex.ofReal_im]
    intro _
    constructor
    · rw [not_le]; exact hx.1
    · rw [not_le]; exact hx.2

instance : realCuspApproach.NeBot := Filter.map_neBot

-- (C3, the K′ logarithmic cusp asymptotic, was an axiom `AX_elliptic_cusp_limits`
-- here until 2026-07-05 — v6, already weakened to the positive-real ray. It is now
-- the THEOREM `elliptic_cusp_limit` below, proved by the model-comparison route:
-- realization of K(1−x) as a real integral, the elementary arcsinh model carrying
-- the whole log divergence, a constant-dominated comparison, and the ε-endpoint
-- evaluation ∫(1/sin − 1/φ) = log(4/π). The C-route now has NO cusp axiom.)

/-- **C3 DISCHARGED (formerly axiom `AX_elliptic_cusp_limits`):** the `K′`
logarithmic cusp asymptotic `K(1−m) + ½ log m → 2 log 2` along the positive-real
approach — now a theorem (Whittaker–Watson §22.7 made kernel-checked). The complex
statement reduces through the real embedding to `cusp_asymptotic_real`. -/
theorem elliptic_cusp_limit :
    Tendsto (fun m : ℂ => ellipticKm (1 - m) + (1/2 : ℂ) * Complex.log m)
      realCuspApproach (𝓝 ((2 * Real.log 2 : ℝ) : ℂ)) := by
  rw [realCuspApproach, Filter.tendsto_map'_iff]
  have hco := (Complex.continuous_ofReal.tendsto (2 * Real.log 2)).comp
    cusp_asymptotic_real
  apply Filter.Tendsto.congr' ?_ hco
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  simp only [Function.comp_def]
  rw [ellipticKm_one_sub_ofReal hx.1 hx.2, ← Complex.ofReal_log hx.1.le]
  push_cast
  ring

-- (C4, the cusp labeling, was an axiom `AX_tau_cusp_zero` here until 2026-07-05.
-- The golden trace showed it was consumed by NO theorem — an unconsumed axiom is
-- pure trusted-base pollution — so it is demoted to the named, *unasserted*
-- statement below. A future consumer (H3's explicit monopole/dyon monodromies)
-- must either prove it or reintroduce it as an explicitly tracked axiom.)

/-- **C4 as a named statement (demoted from the axiom `AX_tau_cusp_zero`):** near
`m = 0` the period ratio is `−(i/π)·log(m/16)` plus a function analytic at `0`;
hence the loop about `m = 0` shifts `τ` by exactly `+2` — the `Γ(2)` generator `T²`.
This is the cusp label the covering axiom alone cannot supply, required for H3's
explicit monopole/dyon monodromies. **Not asserted** — it is the target spec for
the cusp-labeling milestone (both cusp jumps checked numerically,
`audit/numerical/validate_elliptic.py` C4 blocks). -/
def TauCuspLabelZero : Prop :=
  ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ ∀ᶠ m in 𝓝[EllipticParamDomain] 0,
    Complex.I * ellipticKm (1 - m) / ellipticKm m
      = -(Complex.I / (Real.pi : ℂ)) * Complex.log (m / 16) + h m

/-- The candidate developing map `m ↦ i·K(1−m)/K(m)` is **holomorphic** on the cut plane —
the reviewer's proposed `AX_tau_holomorphic`, obtained as a theorem from C1h and C1's
nonvanishing clause (footprint: standard-3 + `AX_elliptic_inversion`), per the plan's
disposition that holomorphy is provable, not axiomatic. -/
theorem tau_ratio_differentiableOn :
    DifferentiableOn ℂ
      (fun m => Complex.I * ellipticKm (1 - m) / ellipticKm m) EllipticParamDomain := by
  have hnum : DifferentiableOn ℂ (fun m : ℂ => ellipticKm (1 - m)) EllipticParamDomain :=
    ellipticKm_differentiableOn.comp
      (((differentiable_const (1:ℂ)).sub differentiable_id).differentiableOn)
      (fun m hm => one_sub_mem_ellipticParamDomain hm)
  exact ((differentiableOn_const Complex.I).mul hnum).div ellipticKm_differentiableOn
    fun m hm => (AX_elliptic_inversion m hm).1

/-! ## The SW modulus map `swCrossRatio` (pinned numerically, 2026-07-04)

Which Möbius map `u ↦ m` identifies the SU(2) Coulomb branch with the elliptic parameter
plane was **determined by computation, not chosen**: direct branch-tracked contour
quadrature of the curve periods of `y² = (x²−u)² − Λ⁴`, with `λ(τ_curve(u))` compared
against all six anharmonic candidates (`audit/numerical/validate_swcrossratio.py`,
16/16 PASS; unique winner at every sample, residuals `≲ 1e-31`; cycle normalization
pinned by the `τ(u=3, Λ=1) = i` self-dual anchor, which caught a factor-2 error in the
first attempt). The three singular points map `u = Λ² ↦ 1` (monopole), `u = −Λ² ↦ ∞`
(dyon), `u = ∞ ↦ 0` (weak coupling) — so the `m` cut plane is a *chart*: it pulls back
to the `u`-plane slit along the locus where `m` is real `≤ 0` or `≥ 1`, matching the
simply-connected-chart carrier (H0). -/

/-- **The SW modulus** `m(u) = 2Λ²/(u + Λ²)`: the elliptic parameter of the SU(2) curve
`y² = (x²−u)² − Λ⁴`, pinned by the period computation above. -/
noncomputable def swCrossRatio (Λ u : ℂ) : ℂ := 2 * Λ ^ 2 / (u + Λ ^ 2)

/-- At the monopole point `u = Λ²` the modulus is exactly the cusp value `m = 1`. -/
theorem swCrossRatio_monopole {Λ : ℂ} (hΛ : Λ ≠ 0) : swCrossRatio Λ (Λ ^ 2) = 1 := by
  simp only [swCrossRatio]
  rw [show Λ ^ 2 + Λ ^ 2 = 2 * Λ ^ 2 from by ring]
  exact div_self (mul_ne_zero two_ne_zero (pow_ne_zero 2 hΛ))

/-- Scale covariance: the modulus depends only on `u/Λ²` (the dimensionless Coulomb
coordinate), as the physics requires. -/
theorem swCrossRatio_scale {Λ : ℂ} (u : ℂ) (hΛ : Λ ≠ 0) :
    swCrossRatio Λ u = swCrossRatio 1 (u / Λ ^ 2) := by
  simp only [swCrossRatio, one_pow, mul_one]
  rw [show u / Λ ^ 2 + 1 = (u + Λ ^ 2) / Λ ^ 2 from by field_simp, div_div_eq_mul_div]

/-- **The pinned developing property** (chart-level): on a chart `D` of the Coulomb
branch, a candidate coupling `f` develops the SW geometry iff its `λ`-image is the
curve's modulus. Anchoring to the geometry (rather than comparing two maps to each
other) avoids the conjugacy ambiguity the review flagged; `SameSWMonodromy` will be
*derived* as `DevelopsSWCrossRatio Λ D f ∧ DevelopsSWCrossRatio Λ D g` when the
uninterpreted axiom is retired (next milestone). -/
def DevelopsSWCrossRatio (Λ : ℂ) (D : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ u ∈ D, modularLambdaFn (f u) = swCrossRatio Λ u

/-- The cusp `0` is an honest limit point of the cut plane (real approach `m = ε`). -/
theorem nhdsWithin_zero_neBot : (𝓝[EllipticParamDomain] (0:ℂ)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  refine ⟨((min (ε/2) (1/2) : ℝ) : ℂ), ?_, ?_⟩
  · have hpos : 0 < min (ε/2) (1/2) := lt_min (by linarith) (by norm_num)
    have hlt : min (ε/2) (1/2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    simp only [EllipticParamDomain, Set.mem_setOf_eq, not_and, not_or,
      Complex.ofReal_re, Complex.ofReal_im]
    intro _
    constructor
    · rw [not_le]; exact hpos
    · rw [not_le]; exact hlt
  · rw [dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_min (by linarith) (by norm_num))]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-- **The Legendre combination tends to `π/2` at the cusp** (along the positive-real
approach, where C3 v6 lives; all other ingredients transfer from the domain filter by
`realCuspApproach_le`) — the toolkit assembled: `(E−K)·(K′+½log m) → 0·2log2`,
`½(E−K)·log m → 0` by the quantitative rate against `m·log m → 0`, and `E′·K → 1·π/2`
from the proved limits; only the C3 log clause is consumed. -/
theorem legendreL_tendsto :
    Tendsto legendreL realCuspApproach (𝓝 ((Real.pi / 2 : ℝ) : ℂ)) := by
  have hK : Tendsto ellipticKm realCuspApproach
      (𝓝 ((Real.pi / 2 : ℝ) : ℂ)) := ellipticKm_tendsto_zero.mono_left
    (realCuspApproach_le.trans nhdsWithin_le_nhds)
  have hE : Tendsto ellipticEm realCuspApproach
      (𝓝 ((Real.pi / 2 : ℝ) : ℂ)) := ellipticEm_tendsto_zero.mono_left
    (realCuspApproach_le.trans nhdsWithin_le_nhds)
  have hE1 := ellipticEm_one_sub_tendsto.mono_left realCuspApproach_le
  have hC3 := elliptic_cusp_limit
  have hEK0 : Tendsto (fun m => ellipticEm m - ellipticKm m)
      realCuspApproach (𝓝 0) := by
    have h := hE.sub hK
    simpa using h
  have hterm1 : Tendsto (fun m : ℂ => (ellipticEm m - ellipticKm m)
      * (ellipticKm (1 - m) + (1/2 : ℂ) * Complex.log m))
      realCuspApproach (𝓝 0) := by
    have h := hEK0.mul hC3
    simpa using h
  have hterm2 : Tendsto (fun m : ℂ => (ellipticEm m - ellipticKm m) * Complex.log m)
      realCuspApproach (𝓝 0) := by
    have hev : ∀ᶠ m in realCuspApproach, ‖m‖ ≤ 1/2 ∧
        m ∈ EllipticParamDomain := by
      have h1 : ∀ᶠ m in 𝓝 (0:ℂ), ‖m‖ ≤ 1/2 := by
        filter_upwards [Metric.closedBall_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1/2)]
          with x hx
        simpa using mem_closedBall_zero_iff.mp hx
      filter_upwards [(h1.filter_mono nhdsWithin_le_nhds).filter_mono realCuspApproach_le,
        realCuspApproach_le self_mem_nhdsWithin]
        with x hx1 hx2
      exact ⟨hx1, hx2⟩
    have hbnd : ∀ᶠ m in realCuspApproach,
        ‖(ellipticEm m - ellipticKm m) * Complex.log m‖
          ≤ (Real.sqrt 2 * (Real.pi / 2)) * ‖m * Complex.log m‖ := by
      filter_upwards [hev] with x hx
      obtain ⟨hx2, hxd⟩ := hx
      rw [norm_mul, norm_mul]
      calc ‖ellipticEm x - ellipticKm x‖ * ‖Complex.log x‖
          ≤ (‖x‖ * (Real.sqrt 2 * (Real.pi / 2))) * ‖Complex.log x‖ :=
            mul_le_mul_of_nonneg_right
              (norm_ellipticEm_sub_ellipticKm_le hxd hx2) (norm_nonneg _)
        _ = (Real.sqrt 2 * (Real.pi / 2)) * (‖x‖ * ‖Complex.log x‖) := by ring
    have hml : Tendsto (fun m : ℂ => (Real.sqrt 2 * (Real.pi / 2))
        * ‖m * Complex.log m‖) realCuspApproach (𝓝 0) := by
      have h := (tendsto_mul_log_zero.mono_left realCuspApproach_le).norm
      rw [norm_zero] at h
      have h2 := h.const_mul (Real.sqrt 2 * (Real.pi / 2))
      simpa using h2
    exact squeeze_zero_norm' hbnd hml
  have hsplit : legendreL = fun m : ℂ =>
      (ellipticEm m - ellipticKm m) * (ellipticKm (1 - m) + (1/2 : ℂ) * Complex.log m)
      - (1/2 : ℂ) * ((ellipticEm m - ellipticKm m) * Complex.log m)
      + ellipticEm (1 - m) * ellipticKm m := by
    funext x
    simp only [legendreL]
    ring
  rw [hsplit]
  have hfinal := (hterm1.sub (hterm2.const_mul ((1:ℂ)/2))).add (hE1.mul hK)
  simpa using hfinal

/-- **The Legendre constant is `π/2` (proved):** constancy + the cusp limit, with the
filter nontrivial because the positive-real ray accumulates at `0`. -/
theorem legendreL_half : legendreL (1/2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by
  have hconst : Tendsto legendreL realCuspApproach
      (𝓝 (legendreL (1/2 : ℂ))) := by
    have hmem : ∀ᶠ m in realCuspApproach, m ∈ EllipticParamDomain :=
      realCuspApproach_le self_mem_nhdsWithin
    have hev : ∀ᶠ m in realCuspApproach,
        legendreL (1/2 : ℂ) = legendreL m :=
      hmem.mono fun m hm => (legendreL_eq_half hm).symm
    exact Filter.Tendsto.congr' hev tendsto_const_nhds
  exact tendsto_nhds_unique hconst legendreL_tendsto

/-- **The Legendre relation, DISCHARGED (formerly axiom C2 = `AX_legendre_relation`):**
`E·K′ + E′·K − K·K′ = π/2` on the cut plane — now a theorem of **standard-3 alone**
(2026-07-05: its last input, the C3 cusp clause, was itself discharged). -/
theorem legendre_relation (m : ℂ) (hm : m ∈ EllipticParamDomain) :
    ellipticEm m * ellipticKm (1 - m) + ellipticEm (1 - m) * ellipticKm m
      - ellipticKm m * ellipticKm (1 - m) = (Real.pi / 2 : ℂ) := by
  have h := (legendreL_eq_half hm).trans legendreL_half
  rw [show ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi / 2 : ℂ) from by push_cast; ring] at h
  exact h


/-- **The Wronskian formula for the period ratio (the Legendre relation's payoff):**
`d/dm [i·K(1−m)/K(m)] = −iπ / (4·m·(1−m)·K(m)²)` on the cut plane — quotient rule
through the two proved Legendre ODEs, the numerator collapsed by `legendre_relation`.
This is the classical statement that the modular parameter is an (orientation-fixed)
local biholomorphism wherever `K ≠ 0`, and the derivative input for the faithful
weak-coupling (one-loop) asymptotic of the SU(2) coupling. Footprint: standard-3 +
`AX_elliptic_inversion` (only its `K ≠ 0` clause). -/
theorem tau_ratio_hasDerivAt {m : ℂ} (hm : m ∈ EllipticParamDomain) :
    HasDerivAt (fun m : ℂ => Complex.I * ellipticKm (1 - m) / ellipticKm m)
      (-(Complex.I * (Real.pi : ℂ)) / (4 * m * (1 - m) * ellipticKm m ^ 2)) m := by
  have hs : (1 - m) ∈ EllipticParamDomain := one_sub_mem_ellipticParamDomain hm
  have hm0 : m ≠ 0 := ne_zero_of_mem_ellipticParamDomain hm
  have hm1 : (1 : ℂ) - m ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (ne_one_of_mem_ellipticParamDomain hm))
  have hK0 : ellipticKm m ≠ 0 := (AX_elliptic_inversion m hm).1
  have hinner : HasDerivAt (fun m : ℂ => 1 - m) (-1) m := by
    simpa using (hasDerivAt_id m).const_sub 1
  have hK1 : HasDerivAt (fun m : ℂ => ellipticKm (1 - m))
      (-((ellipticEm (1 - m) - m * ellipticKm (1 - m))
        / (2 * (1 - m) * m))) m := by
    have h := HasDerivAt.comp m (ellipticKm_hasDerivAt hs) hinner
    simpa only [Function.comp_def, mul_neg_one, sub_sub_cancel] using h
  have hK := ellipticKm_hasDerivAt hm
  have hq := (hK1.const_mul Complex.I).div hK hK0
  have hleg := legendre_relation m hm
  have hkey : Complex.I * -((ellipticEm (1 - m) - m * ellipticKm (1 - m))
        / (2 * (1 - m) * m)) * ellipticKm m
      - Complex.I * ellipticKm (1 - m)
        * ((ellipticEm m - (1 - m) * ellipticKm m) / (2 * m * (1 - m)))
      = -(Complex.I * (Real.pi : ℂ)) / (4 * m * (1 - m)) := by
    field_simp
    linear_combination (-4 : ℂ) * hleg
  convert hq using 1
  rw [hkey, div_div]

end SeibergWitten.Physics
