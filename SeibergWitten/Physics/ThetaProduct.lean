/-
# The Jacobi triple product — staging (milestone T0: the product side exists)

Discharge target for the θ pair (`AX_jacobi_quartic`, `AX_theta3_ne_zero` in
`ThetaLambda.lean`): the triple product

  `θ(w, q) = ∏_{n≥0} (1 − q^{2(n+1)}) (1 + q^{2n+1} w) (1 + q^{2n+1} w⁻¹)`

equals `jacobiTheta₂ z τ` at `q = e^{πiτ}`, `w = e^{2πiz}` — from which the quartic
identity and `θ₃ ≠ 0` follow as corollaries (each factor is visibly nonzero for
`‖q‖ < 1`, `w` on the unit circle).

This file is **T0**: the product-side object and its convergence — the nome bound
`‖q‖ < 1` on `ℍ`, geometric summability of each factor family, and `Multipliable`
for the full term (via `Complex.multipliable_one_add_of_summable`). No identity is
claimed yet; the equality with the series is the (Mathlib-scale) sequel, staged in
`audit/GENUS1_PERIODS_PLAN.md`.
-/
import Mathlib
import SeibergWitten.Physics.ThetaLambda

namespace SeibergWitten.Physics

open Complex

/-- The nome `q = e^{πiτ}` of the θ conventions used throughout
(`theta3 τ = jacobiTheta₂ 0 τ = ∑ q^{n²}`). -/
noncomputable def thetaNome (τ : ℂ) : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * τ)

/-- On the upper half-plane the nome is strictly inside the unit disc. -/
theorem norm_thetaNome_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖thetaNome τ‖ < 1 := by
  rw [thetaNome, Complex.norm_exp]
  have hre : ((Real.pi : ℂ) * Complex.I * τ).re = -(Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

/-- The `n`-th factor of the Jacobi triple product:
`(1 − q^{2(n+1)}) · (1 + q^{2n+1}·w) · (1 + q^{2n+1}·w⁻¹)`. -/
noncomputable def tripleProductTerm (q w : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (2 * (n + 1))) * (1 + q ^ (2 * n + 1) * w) * (1 + q ^ (2 * n + 1) * w⁻¹)

/-- The Jacobi triple product (as a `tprod`; junk `1` off the convergence region,
per `tprod` conventions). -/
noncomputable def jacobiTripleProduct (q w : ℂ) : ℂ := ∏' n : ℕ, tripleProductTerm q w n

/-- Geometric summability of the even-power family `q^{2(n+1)}` for `‖q‖ < 1`. -/
theorem summable_q_even {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => q ^ (2 * (n + 1))) := by
  have hsq : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hgeo : Summable (fun n : ℕ => (q ^ 2) ^ n) := summable_geometric_of_norm_lt_one hsq
  apply (hgeo.mul_left (q ^ 2)).congr
  intro n
  rw [← pow_succ', ← pow_mul]

/-- Geometric summability of the odd-power family `q^{2n+1}·c` for `‖q‖ < 1`. -/
theorem summable_q_odd_mul {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) :
    Summable (fun n : ℕ => q ^ (2 * n + 1) * c) := by
  have hsq : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hgeo : Summable (fun n : ℕ => (q ^ 2) ^ n) := summable_geometric_of_norm_lt_one hsq
  apply ((hgeo.mul_left q).mul_right c).congr
  intro n
  rw [pow_add, pow_mul, pow_one]
  ring

/-- **T0 — the triple product converges** on `‖q‖ < 1` (any `w`; the `w⁻¹` factor is
junk-tolerant at `w = 0`): each of the three factor families is `1 + (summable)`,
and `Multipliable` is closed under products. -/
theorem multipliable_tripleProductTerm {q : ℂ} (hq : ‖q‖ < 1) (w : ℂ) :
    Multipliable (tripleProductTerm q w) := by
  have h1 : Multipliable (fun n : ℕ => 1 - q ^ (2 * (n + 1))) := by
    have := Complex.multipliable_one_add_of_summable (summable_q_even hq).neg
    apply this.congr
    intro n
    ring
  have h2 : Multipliable (fun n : ℕ => 1 + q ^ (2 * n + 1) * w) :=
    Complex.multipliable_one_add_of_summable (summable_q_odd_mul hq w)
  have h3 : Multipliable (fun n : ℕ => 1 + q ^ (2 * n + 1) * w⁻¹) :=
    Complex.multipliable_one_add_of_summable (summable_q_odd_mul hq w⁻¹)
  exact (h1.mul h2).mul h3

/-- The convergence instance at the θ-null arguments: `q = e^{πiτ}`, `w = 1`, for
`τ ∈ ℍ` — the case whose value the θ₃ product formula will compute. -/
theorem multipliable_tripleProductTerm_theta3 {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (tripleProductTerm (thetaNome τ) 1) :=
  multipliable_tripleProductTerm (norm_thetaNome_lt_one hτ) 1


/-- The three factor families, named for the shift bookkeeping. -/
private noncomputable def tpA (q : ℂ) (n : ℕ) : ℂ := 1 - q ^ (2 * (n + 1))
private noncomputable def tpB (q w : ℂ) (n : ℕ) : ℂ := 1 + q ^ (2 * n + 1) * w

theorem multipliable_tpA {q : ℂ} (hq : ‖q‖ < 1) : Multipliable (tpA q) := by
  have := Complex.multipliable_one_add_of_summable (summable_q_even hq).neg
  apply this.congr
  intro n
  simp only [tpA]
  ring

theorem multipliable_tpB {q : ℂ} (hq : ‖q‖ < 1) (w : ℂ) : Multipliable (tpB q w) :=
  Complex.multipliable_one_add_of_summable (summable_q_odd_mul hq w)

/-- The triple product splits as the product of the three family products. -/
theorem jacobiTripleProduct_eq_mul {q : ℂ} (hq : ‖q‖ < 1) (w : ℂ) :
    jacobiTripleProduct q w
      = (∏' n, tpA q n) * (∏' n, tpB q w n) * (∏' n, tpB q w⁻¹ n) := by
  have hMA := multipliable_tpA hq
  have hMB := multipliable_tpB hq w
  have hMC := multipliable_tpB hq w⁻¹
  rw [jacobiTripleProduct]
  rw [show tripleProductTerm q w = fun n => (tpA q n * tpB q w n) * tpB q w⁻¹ n from
    funext fun n => by simp only [tripleProductTerm, tpA, tpB]]
  rw [(hMA.mul hMB).tprod_mul hMC, hMA.tprod_mul hMB]

/-- **T1 — quasi-periodicity of the product side:** for `q ≠ 0`, `w ≠ 0` with
`1 + qw ≠ 0` (off the zero set), `qw · P(q, q²w) = P(q, w)` — the `w`-family shifts
down (losing its `n = 0` factor `1 + qw`), the `w⁻¹`-family shifts up (gaining
`1 + q⁻¹w⁻¹`), and `qw·(1 + q⁻¹w⁻¹) = 1 + qw`. This is the same functional equation
as `jacobiTheta₂` under `z ↦ z + τ`, the engine of the T2 ratio argument. -/
theorem tripleProduct_quasi_periodic {q w : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (hw0 : w ≠ 0) (hqw : 1 + q * w ≠ 0) :
    (q * w) * jacobiTripleProduct q (q ^ 2 * w) = jacobiTripleProduct q w := by
  have hq2w : q ^ 2 * w ≠ 0 := mul_ne_zero (pow_ne_zero 2 hq0) hw0
  have hMB' := multipliable_tpB hq (q ^ 2 * w)
  have hMC' := multipliable_tpB hq (q ^ 2 * w)⁻¹
  have hMB := multipliable_tpB hq w
  have hMC := multipliable_tpB hq w⁻¹
  -- the shifted-w family is the tail of the w family
  have hBshift : (∏' n, tpB q (q ^ 2 * w) n) * (1 + q * w) = ∏' n, tpB q w n := by
    have hcongr : tpB q (q ^ 2 * w) = fun n => tpB q w (n + 1) := by
      funext n
      simp only [tpB]
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by ring, pow_add]
      ring
    have hshift : Multipliable (fun n => tpB q w (n + 1)) := hcongr ▸ hMB'
    rw [hcongr, tprod_eq_zero_mul' hshift]
    have h0 : tpB q w 0 = 1 + q * w := by
      simp [tpB]
    rw [h0]
    ring
  -- the shifted-w⁻¹ family gains the head factor `1 + q·(q²w)⁻¹`
  have hCshift : ∏' n, tpB q (q ^ 2 * w)⁻¹ n
      = (1 + q * (q ^ 2 * w)⁻¹) * ∏' n, tpB q w⁻¹ n := by
    have hcongr : (fun n => tpB q (q ^ 2 * w)⁻¹ (n + 1)) = tpB q w⁻¹ := by
      funext n
      simp only [tpB]
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by ring, pow_add]
      field_simp
    have hshift : Multipliable (fun n => tpB q (q ^ 2 * w)⁻¹ (n + 1)) :=
      hMC.congr fun n => (congrFun hcongr n).symm
    rw [tprod_eq_zero_mul' hshift]
    have h0 : tpB q (q ^ 2 * w)⁻¹ 0 = 1 + q * (q ^ 2 * w)⁻¹ := by
      simp [tpB]
    rw [h0, hcongr]
  -- assemble, cancelling `1 + qw`
  have hhead : (q * w) * (1 + q * (q ^ 2 * w)⁻¹) = 1 + q * w := by
    field_simp
    ring
  have hA := jacobiTripleProduct_eq_mul hq (q ^ 2 * w)
  have hB := jacobiTripleProduct_eq_mul hq w
  apply mul_left_cancel₀ hqw
  calc (1 + q * w) * ((q * w) * jacobiTripleProduct q (q ^ 2 * w))
      = (∏' n, tpA q n) * ((∏' n, tpB q (q ^ 2 * w) n) * (1 + q * w))
        * ((q * w) * (1 + q * (q ^ 2 * w)⁻¹)) * (∏' n, tpB q w⁻¹ n) := by
        rw [hA, hCshift]
        ring
    _ = (∏' n, tpA q n) * (∏' n, tpB q w n) * (1 + q * w) * (∏' n, tpB q w⁻¹ n) := by
        rw [hBshift, hhead]
    _ = (1 + q * w) * jacobiTripleProduct q w := by
        rw [hB]
        ring


/-- `1 + x ≠ 0` for `‖x‖ < 1` — each triple-product factor is visibly nonzero. -/
theorem one_add_ne_zero_of_norm_lt_one {x : ℂ} (hx : ‖x‖ < 1) : 1 + x ≠ 0 := by
  intro h
  have hx1 : x = -1 := by linear_combination h
  rw [hx1] at hx
  simp at hx

/-- A `1 + summable` family with all factors nonzero has nonzero `tprod`: it is the
exponential of the summed logs (`Complex.cexp_tsum_eq_tprod`). -/
theorem tprod_one_add_ne_zero {f : ℕ → ℂ} (hf : Summable f)
    (hfn : ∀ n, ‖f n‖ < 1) : (∏' n, (1 + f n)) ≠ 0 := by
  have hne : ∀ n, 1 + f n ≠ 0 := fun n => one_add_ne_zero_of_norm_lt_one (hfn n)
  have hlog : Summable fun n => Complex.log (1 + f n) :=
    Complex.summable_log_one_add_of_summable hf
  rw [← Complex.cexp_tsum_eq_tprod hne hlog]
  exact Complex.exp_ne_zero _

/-- **T3a — the triple product is nonvanishing on the open annulus**
`‖q‖ < ‖w‖ < ‖q‖⁻¹` (where all theta zeros `w = −q^{2k+1}, k ∈ ℤ` are excluded):
every factor is `1 + (norm < 1)`, and each family product is an exponential. -/
theorem jacobiTripleProduct_ne_zero {q w : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (hlo : ‖q‖ < ‖w‖) (hhi : ‖w‖ * ‖q‖ < 1) :
    jacobiTripleProduct q w ≠ 0 := by
  have hqn : (0:ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hwn : (0:ℝ) < ‖w‖ := lt_trans hqn hlo
  have hqle : ∀ n : ℕ, ‖q‖ ^ (2 * n) ≤ 1 :=
    fun n => pow_le_one₀ (norm_nonneg q) hq.le
  have hA : ∀ n : ℕ, ‖-(q ^ (2 * (n + 1)))‖ < 1 := by
    intro n
    rw [norm_neg, norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hB : ∀ n : ℕ, ‖q ^ (2 * n + 1) * w‖ < 1 := by
    intro n
    rw [norm_mul, norm_pow, pow_add, pow_one]
    calc ‖q‖ ^ (2 * n) * ‖q‖ * ‖w‖ = ‖q‖ ^ (2 * n) * (‖w‖ * ‖q‖) := by ring
      _ ≤ 1 * (‖w‖ * ‖q‖) :=
          mul_le_mul_of_nonneg_right (hqle n) (by positivity)
      _ < 1 := by rw [one_mul]; exact hhi
  have hC : ∀ n : ℕ, ‖q ^ (2 * n + 1) * w⁻¹‖ < 1 := by
    intro n
    rw [norm_mul, norm_pow, norm_inv, pow_add, pow_one]
    have hqw : ‖q‖ * ‖w‖⁻¹ < 1 := by
      rw [mul_inv_lt_iff₀ hwn, one_mul]
      exact hlo
    calc ‖q‖ ^ (2 * n) * ‖q‖ * ‖w‖⁻¹ = ‖q‖ ^ (2 * n) * (‖q‖ * ‖w‖⁻¹) := by ring
      _ ≤ 1 * (‖q‖ * ‖w‖⁻¹) :=
          mul_le_mul_of_nonneg_right (hqle n) (by positivity)
      _ < 1 := by rw [one_mul]; exact hqw
  rw [jacobiTripleProduct_eq_mul hq]
  have hAne : (∏' n, tpA q n) ≠ 0 := by
    have h := tprod_one_add_ne_zero (f := fun n => -(q ^ (2 * (n + 1))))
      (summable_q_even hq).neg hA
    apply ne_of_eq_of_ne ?_ h
    apply tprod_congr
    intro n
    simp only [tpA]
    ring
  have hBne : (∏' n, tpB q w n) ≠ 0 :=
    tprod_one_add_ne_zero (summable_q_odd_mul hq w) hB
  have hCne : (∏' n, tpB q w⁻¹ n) ≠ 0 :=
    tprod_one_add_ne_zero (summable_q_odd_mul hq w⁻¹) hC
  exact mul_ne_zero (mul_ne_zero hAne hBne) hCne

/-- The θ-null instance: the product at `q = e^{πiτ}`, `w = 1` is nonzero on `ℍ` —
exactly what `θ₃ ≠ 0` (`AX_theta3_ne_zero`) becomes once T2's product identity
lands. -/
theorem jacobiTripleProduct_theta3_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTripleProduct (thetaNome τ) 1 ≠ 0 := by
  have hq := norm_thetaNome_lt_one hτ
  have hq0 : thetaNome τ ≠ 0 := Complex.exp_ne_zero _
  apply jacobiTripleProduct_ne_zero hq hq0
  · simpa using hq
  · simpa using hq


/-- **T2 brick — entire dependence on the multiplier:** for `‖q‖ < 1` and any entire
`g`, the family product `z ↦ ∏' n, (1 + q^{2n+1}·g z)` is entire — locally uniform
convergence (`hasProdLocallyUniformlyOn_nat_one_add` with the geometric dominator
scaled by a compact bound on `g`) plus the locally-uniform-limit-of-holomorphic
theorem. -/
theorem differentiable_tprod_one_add_qpow_mul {q : ℂ} (hq : ‖q‖ < 1) {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun z => ∏' n : ℕ, (1 + q ^ (2 * n + 1) * g z)) := by
  intro z₀
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
    (hg.continuous.continuousOn)
  have hM0 : (0:ℝ) ≤ max M 0 := le_max_right M 0
  have hsq : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hu : Summable (fun n : ℕ => ‖q‖ ^ (2 * n + 1) * max M 0) := by
    apply Summable.mul_right
    have hgeo : Summable (fun n : ℕ => ‖q ^ 2‖ ^ n) :=
      summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])
    apply (hgeo.mul_left ‖q‖).congr
    intro n
    rw [norm_pow, ← pow_mul, pow_add, pow_one]
    ring
  have hbound : ∀ᶠ n in Filter.atTop, ∀ z ∈ Metric.ball z₀ 1,
      ‖q ^ (2 * n + 1) * g z‖ ≤ ‖q‖ ^ (2 * n + 1) * max M 0 := by
    refine Filter.Eventually.of_forall fun n z hz => ?_
    rw [norm_mul, norm_pow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg q) _)
    exact le_trans (hM z (Metric.ball_subset_closedBall hz)) (le_max_left M 0)
  have hcts : ∀ n : ℕ, ContinuousOn (fun z => q ^ (2 * n + 1) * g z) (Metric.ball z₀ 1) :=
    fun n => (continuous_const.mul hg.continuous).continuousOn
  have hprod := Summable.hasProdLocallyUniformlyOn_nat_one_add
    (f := fun n z => q ^ (2 * n + 1) * g z) Metric.isOpen_ball hu hbound hcts
  have htend := hprod.tendstoLocallyUniformlyOn_finsetRange
  have hdiff : DifferentiableOn ℂ (fun z => ∏' n : ℕ, (1 + q ^ (2 * n + 1) * g z))
      (Metric.ball z₀ 1) := by
    apply htend.differentiableOn ?_ Metric.isOpen_ball
    refine Filter.Eventually.of_forall fun N => ?_
    dsimp only
    have hfun : (fun b : ℂ => ∏ i ∈ Finset.range N, (1 + q ^ (2 * i + 1) * g b))
        = ∏ i ∈ Finset.range N, fun z : ℂ => 1 + q ^ (2 * i + 1) * g z := by
      funext b
      simp [Finset.prod_apply]
    rw [hfun]
    exact DifferentiableOn.finset_prod fun i _ =>
      ((differentiable_const _).add ((differentiable_const _).mul hg)).differentiableOn
  exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self one_pos))


/-- **T2 brick — the product side is entire in `z`:** for fixed `‖q‖ < 1`,
`z ↦ P(q, e^{2πiz})` is entire — the `A`-family is constant in `z`, and both
exponential families are entire by `differentiable_tprod_one_add_qpow_mul`. With T1
this gives the product side all the analytic structure the Liouville step of T2
consumes. -/
theorem differentiable_jacobiTripleProduct_exp {q : ℂ} (hq : ‖q‖ < 1) :
    Differentiable ℂ
      (fun z => jacobiTripleProduct q (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))) := by
  have hgB : Differentiable ℂ (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)) :=
    Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id)
  have hgC : Differentiable ℂ
      (fun z : ℂ => Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * z))) :=
    Complex.differentiable_exp.comp (((differentiable_const _).mul differentiable_id).neg)
  have hfun : (fun z => jacobiTripleProduct q (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)))
      = fun z => (∏' n, tpA q n)
        * (∏' n, (1 + q ^ (2 * n + 1) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)))
        * (∏' n, (1 + q ^ (2 * n + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * z)))) := by
    funext z
    rw [jacobiTripleProduct_eq_mul hq]
    congr 1
    apply tprod_congr
    intro n
    simp only [tpB]
    rw [← Complex.exp_neg]
  rw [hfun]
  exact ((differentiable_const _).mul
    (differentiable_tprod_one_add_qpow_mul hq hgB)).mul
    (differentiable_tprod_one_add_qpow_mul hq hgC)

end SeibergWitten.Physics
