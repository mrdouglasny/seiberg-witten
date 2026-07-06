/-
# Discharging `matterPeriodRigidityAxiom`, Stage A (`audit/MPRA_DISCHARGE_PLAN.md`)

This file builds the first `PeriodChart` instance in the development and discharges the
last matter-side axiom at its consumed instantiation (`N_f = 1`, the AD mass
`m₁ = −3Λ/4`). Layer A1/A2 (this section): the **quartic discriminant bridge** —

* `quarticDisc_prod_roots`: for a product of four linear factors,
  `g₂³ − 27g₃² = (1/256)·∏_{i<j}(rᵢ − rⱼ)²` (the classical quartic discriminant, in the
  `quarticG2/G3` normalization of `MatterInvariants.lean`; constant pinned numerically);
* `monic_quartic_squarefree_iff_disc`: a monic quartic over `ℂ` is squarefree iff
  `g₂³ − 27g₃² ≠ 0` (via `Squarefree ↔ Separable ↔ roots nodup`);
* `matter_ad_disc_factor`: for the `N_f = 1` AD-mass curve the discriminant factors
  **exactly**: `g₂³ − 27g₃² = −Λ⁶·(u − 3Λ²/4)²·(u + 15Λ²/16)` — double zero at the AD
  point (the Kodaira-II fingerprint), one flavor singularity (Euler `9 + 2 + 1 = 12`
  with `I₃*` at infinity);
* hence the singular locus is the explicit two-point set `{3Λ²/4, −15Λ²/16}`
  (`matter_ad_not_squarefree_iff`).

Conventions pinned by `audit/MPRA_DISCHARGE_PLAN.md` numerics (dps 30).
-/
import SeibergWitten.Physics.MatterInvariants

namespace SeibergWitten.Physics

open Polynomial

/-! ## A1 — the quartic discriminant bridge -/

/-- Vieta expansion of a product of four linear factors. -/
theorem prod_four_linear (r₁ r₂ r₃ r₄ : ℂ) :
    (X - C r₁) * (X - C r₂) * (X - C r₃) * (X - C r₄)
      = X ^ 4 - C (r₁ + r₂ + r₃ + r₄) * X ^ 3
        + C (r₁*r₂ + r₁*r₃ + r₁*r₄ + r₂*r₃ + r₂*r₄ + r₃*r₄) * X ^ 2
        - C (r₁*r₂*r₃ + r₁*r₂*r₄ + r₁*r₃*r₄ + r₂*r₃*r₄) * X
        + C (r₁*r₂*r₃*r₄) := by
  apply Polynomial.funext
  intro x
  simp only [eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C]
  ring

private theorem prod_four_coeff (r₁ r₂ r₃ r₄ : ℂ) :
    ((X - C r₁) * (X - C r₂) * (X - C r₃) * (X - C r₄)).coeff 4 = 1 ∧
    ((X - C r₁) * (X - C r₂) * (X - C r₃) * (X - C r₄)).coeff 3
      = -(r₁ + r₂ + r₃ + r₄) ∧
    ((X - C r₁) * (X - C r₂) * (X - C r₃) * (X - C r₄)).coeff 2
      = r₁*r₂ + r₁*r₃ + r₁*r₄ + r₂*r₃ + r₂*r₄ + r₃*r₄ ∧
    ((X - C r₁) * (X - C r₂) * (X - C r₃) * (X - C r₄)).coeff 1
      = -(r₁*r₂*r₃ + r₁*r₂*r₄ + r₁*r₃*r₄ + r₂*r₃*r₄) ∧
    ((X - C r₁) * (X - C r₂) * (X - C r₃) * (X - C r₄)).coeff 0
      = r₁*r₂*r₃*r₄ := by
  rw [prod_four_linear]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      norm_num

/-- **The quartic discriminant identity** in the `quarticG2/G3` normalization:
`g₂³ − 27g₃² = (1/256)·∏_{i<j}(rᵢ−rⱼ)²`. -/
theorem quarticDisc_prod_roots (r₁ r₂ r₃ r₄ : ℂ) :
    quarticG2 ((X - C r₁) * (X - C r₂) * (X - C r₃) * (X - C r₄)) ^ 3
      - 27 * quarticG3 ((X - C r₁) * (X - C r₂) * (X - C r₃) * (X - C r₄)) ^ 2
    = (1 / 256) * ((r₁ - r₂) * (r₁ - r₃) * (r₁ - r₄)
        * (r₂ - r₃) * (r₂ - r₄) * (r₃ - r₄)) ^ 2 := by
  obtain ⟨h4, h3, h2, h1, h0⟩ := prod_four_coeff r₁ r₂ r₃ r₄
  simp only [quarticG2, quarticG3, h4, h3, h2, h1, h0]
  ring

private lemma multiset_card_four {s : Multiset ℂ} (h : Multiset.card s = 4) :
    ∃ r₁ r₂ r₃ r₄ : ℂ, s = {r₁, r₂, r₃, r₄} := by
  obtain ⟨r₁, t₁, rfl, h₁⟩ := Multiset.card_eq_succ_iff.mp h
  obtain ⟨r₂, t₂, rfl, h₂⟩ := Multiset.card_eq_succ_iff.mp h₁
  obtain ⟨r₃, t₃, rfl, h₃⟩ := Multiset.card_eq_succ_iff.mp h₂
  obtain ⟨r₄, t₄, rfl, h₄⟩ := Multiset.card_eq_succ_iff.mp h₃
  rw [Multiset.card_eq_zero] at h₄
  subst h₄
  exact ⟨r₁, r₂, r₃, r₄, rfl⟩

/-- **A monic quartic over `ℂ` is squarefree iff its discriminant is nonzero** (in the
`quarticG2/G3` normalization: `g₂³ − 27g₃² ≠ 0`). -/
theorem monic_quartic_squarefree_iff_disc {P : ℂ[X]} (hm : P.Monic)
    (hd : P.natDegree = 4) :
    Squarefree P ↔ quarticG2 P ^ 3 - 27 * quarticG3 P ^ 2 ≠ 0 := by
  have hP0 : P ≠ 0 := hm.ne_zero
  have hsp : P.Splits := IsAlgClosed.splits P
  have hcard : Multiset.card P.roots = 4 := by
    have h := Polynomial.splits_iff_card_roots.mp hsp
    omega
  obtain ⟨r₁, r₂, r₃, r₄, hroots⟩ := multiset_card_four hcard
  have hfact : P = (X - C r₁) * (X - C r₂) * (X - C r₃) * (X - C r₄) := by
    have h := hsp.eq_prod_roots_of_monic hm
    rw [hroots] at h
    rw [h]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    ring
  have hnodup_iff : Squarefree P ↔ P.roots.Nodup := by
    rw [← PerfectField.separable_iff_squarefree]
    exact (Polynomial.nodup_roots_iff_of_splits hP0 hsp).symm
  rw [hnodup_iff, hroots]
  conv_rhs => rw [hfact, quarticDisc_prod_roots]
  simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
    Multiset.mem_singleton, Multiset.nodup_singleton, and_true, not_or]
  constructor
  · rintro ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩
    apply mul_ne_zero (by norm_num : (1 / 256 : ℂ) ≠ 0)
    apply pow_ne_zero
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13)) (sub_ne_zero.mpr h14))
      (sub_ne_zero.mpr h23)) (sub_ne_zero.mpr h24)) (sub_ne_zero.mpr h34)
  · intro h
    have h' : (r₁ - r₂) * (r₁ - r₃) * (r₁ - r₄) * (r₂ - r₃) * (r₂ - r₄) * (r₃ - r₄)
        ≠ 0 := by
      intro h0
      apply h
      rw [h0]
      ring
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      · intro he
        apply h'
        subst he
        ring

/-! ## A2 — the explicit `N_f = 1` AD-mass singular locus -/

/-- Monicity and degree of the `N_f = 1` curve. -/
theorem swCurveMatter_nf1_natDegree (Λ m₁ u : ℂ) :
    (swCurveMatter 1 Λ ![m₁] u).natDegree = 4 := by
  rw [swCurveMatter_nf1_expand]
  compute_degree!

theorem swCurveMatter_nf1_monic (Λ m₁ u : ℂ) : (swCurveMatter 1 Λ ![m₁] u).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, swCurveMatter_nf1_natDegree]
  exact (swCurveMatter_nf1_coeff Λ m₁ u).1

/-- **The AD-mass discriminant factors exactly**:
`g₂³ − 27g₃² = −Λ⁶·(u − 3Λ²/4)²·(u + 15Λ²/16)` — a double zero at the AD point (the
Kodaira-II fingerprint) and one flavor singularity (`I₃*` at infinity: `9+2+1 = 12`). -/
theorem matter_ad_disc_factor (Λ u : ℂ) :
    quarticG2 (swCurveMatter 1 Λ ![-(3 / 4) * Λ] u) ^ 3
      - 27 * quarticG3 (swCurveMatter 1 Λ ![-(3 / 4) * Λ] u) ^ 2
    = -Λ ^ 6 * (u - (3 / 4) * Λ ^ 2) ^ 2 * (u + (15 / 16) * Λ ^ 2) := by
  rw [quarticG2_nf1, quarticG3_nf1]
  ring

/-- **The singular locus is the explicit two-point set** `{3Λ²/4, −15Λ²/16}`. -/
theorem matter_ad_not_squarefree_iff (Λ : ℂ) (hΛ : Λ ≠ 0) (u : ℂ) :
    ¬ Squarefree (swCurveMatter 1 Λ ![-(3 / 4) * Λ] u)
      ↔ u = (3 / 4) * Λ ^ 2 ∨ u = -((15 / 16) * Λ ^ 2) := by
  rw [monic_quartic_squarefree_iff_disc (swCurveMatter_nf1_monic Λ _ u)
    (swCurveMatter_nf1_natDegree Λ _ u), not_not, matter_ad_disc_factor]
  have hΛ6 : (-Λ ^ 6 : ℂ) ≠ 0 := by
    simp [hΛ]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact absurd h3 hΛ6
      · left
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
        linear_combination this
    · right
      linear_combination h2
  · rintro (rfl | rfl) <;> ring
/-! ## A3 — the AD point is the unique cusp -/

/-- **Cusp uniqueness at the AD mass**: the only strict-`A₂` point of the
`N_f = 1, m₁ = −3Λ/4` curve family is `u₀ = 3Λ²/4`. (Triple root ⇒ `g₂ = g₃ = 0`; the
closed forms leave `u₀ = ±3Λ²/4`, and the minus sign forces `g₃ = −Λ⁶/8 ≠ 0`.) -/
theorem matter_ad_cusp_unique {Λ : ℂ} (hΛ : Λ ≠ 0) {u₀ : Fin 1 → ℂ}
    (h : IsCuspOf 1 Λ ![-(3 / 4) * Λ] u₀) : u₀ = ![(3 / 4) * Λ ^ 2] := by
  obtain ⟨a, b, hab, hfact⟩ := h
  have hg2 : quarticG2 (swCurveMatter 1 Λ ![-(3 / 4) * Λ] (u₀ 0)) = 0 := by
    rw [hfact, show (X - C a : ℂ[X]) = X + C (-a) from by rw [map_neg, sub_eq_add_neg]]
    exact quarticG2_of_triple_root (-a) b
  have hg3 : quarticG3 (swCurveMatter 1 Λ ![-(3 / 4) * Λ] (u₀ 0)) = 0 := by
    rw [hfact, show (X - C a : ℂ[X]) = X + C (-a) from by rw [map_neg, sub_eq_add_neg]]
    exact quarticG3_of_triple_root (-a) b
  rw [quarticG2_nf1] at hg2
  rw [quarticG3_nf1] at hg3
  have hfac : (u₀ 0 - (3 / 4) * Λ ^ 2) * (u₀ 0 + (3 / 4) * Λ ^ 2) = 0 := by
    linear_combination (3 / 4) * hg2
  funext i
  fin_cases i
  rcases mul_eq_zero.mp hfac with h1 | h2
  · show u₀ 0 = (3 / 4) * Λ ^ 2
    linear_combination h1
  · exfalso
    have hx : u₀ 0 = -((3 / 4) * Λ ^ 2) := by linear_combination h2
    rw [hx] at hg3
    apply hΛ
    have h6 : Λ ^ 6 = 0 := by linear_combination -8 * hg3
    exact pow_eq_zero_iff (by norm_num : (6 : ℕ) ≠ 0) |>.mp h6

/-! ## A4–A5 — the chart: geometry and witness data

The base carries the explicit two-point singular locus; the chart is a metric ball
tangent to the AD point from the `+Λ²` direction (radius `27‖Λ‖²/64`, a quarter of the
distance to the flavor point), so it sits in the smooth locus, is convex (hence simply
connected), and has the AD point on its boundary. The witness data is the DISCLOSED
non-SQCD inhabitant of `IsMatterPolarizedPeriodChart` (see the plan's B4 note):
`a = u − u_AD`, `a_D = i·a`, constant coupling `τ ≡ i`, prepotential `F = (i/2)z²`. -/

private lemma pi_one_norm (f : Fin 1 → ℂ) : ‖f‖ = ‖f 0‖ := by
  rw [Pi.norm_def]
  have h : (Finset.univ : Finset (Fin 1)) = {0} := rfl
  rw [h, Finset.sup_singleton]
  rfl

private lemma pi_one_dist (u v : Fin 1 → ℂ) : dist u v = ‖u 0 - v 0‖ := by
  rw [dist_eq_norm, pi_one_norm]
  rfl

/-- The base: the explicit two-point singular locus of the AD-mass family. -/
noncomputable def matterADBase (Λ : ℂ) : PeriodBase 1 where
  Δ := {u | u 0 = (3 / 4) * Λ ^ 2 ∨ u 0 = -((15 / 16) * Λ ^ 2)}
  U := {u | u 0 = (3 / 4) * Λ ^ 2 ∨ u 0 = -((15 / 16) * Λ ^ 2)}ᶜ
  hUopen := by
    have h : {u : Fin 1 → ℂ | u 0 = (3 / 4) * Λ ^ 2 ∨ u 0 = -((15 / 16) * Λ ^ 2)}
        = (fun u : Fin 1 → ℂ => u 0) ⁻¹'
          {(3 / 4) * Λ ^ 2, -((15 / 16) * Λ ^ 2)} := by
      ext u
      simp [Set.mem_insert_iff]
    rw [h]
    exact (((Set.finite_singleton _).insert _).isClosed.preimage
      (continuous_apply 0)).isOpen_compl
  hUsmooth := rfl

/-- The AD-point moduli vector. -/
noncomputable def matterADPoint (Λ : ℂ) : Fin 1 → ℂ := ![(3 / 4) * Λ ^ 2]

/-- Ball center: the AD point offset by `(27/64)Λ²`. -/
noncomputable def matterADCenter (Λ : ℂ) : Fin 1 → ℂ :=
  ![(3 / 4) * Λ ^ 2 + (27 / 64) * Λ ^ 2]

noncomputable def matterADRadius (Λ : ℂ) : ℝ := (27 / 64) * ‖Λ‖ ^ 2

private lemma matterADRadius_pos {Λ : ℂ} (hΛ : Λ ≠ 0) : 0 < matterADRadius Λ := by
  rw [matterADRadius]
  have := norm_pos_iff.mpr hΛ
  positivity

private lemma mem_ball_iff (Λ : ℂ) (u : Fin 1 → ℂ) :
    u ∈ Metric.ball (matterADCenter Λ) (matterADRadius Λ)
      ↔ ‖u 0 - ((3 / 4) * Λ ^ 2 + (27 / 64) * Λ ^ 2)‖ < (27 / 64) * ‖Λ‖ ^ 2 := by
  rw [Metric.mem_ball, pi_one_dist, matterADRadius]
  simp [matterADCenter]

/-- The chart: a ball tangent to the AD point, inside the smooth locus, carrying the
disclosed witness data. -/
noncomputable def matterADChart (Λ : ℂ) (hΛ : Λ ≠ 0) : PeriodChart (matterADBase Λ) where
  V := Metric.ball (matterADCenter Λ) (matterADRadius Λ)
  hVopen := Metric.isOpen_ball
  hVsub := by
    intro u hu
    rw [mem_ball_iff] at hu
    have hnorm2 : ‖Λ ^ 2‖ = ‖Λ‖ ^ 2 := by rw [norm_pow]
    intro hΔ
    rcases hΔ with h1 | h2
    · -- u 0 = AD point: distance to center is exactly the radius
      rw [h1] at hu
      have : ‖(3 / 4) * Λ ^ 2 - ((3 / 4) * Λ ^ 2 + (27 / 64) * Λ ^ 2)‖
          = (27 / 64) * ‖Λ‖ ^ 2 := by
        rw [show (3 / 4) * Λ ^ 2 - ((3 / 4) * Λ ^ 2 + (27 / 64) * Λ ^ 2)
            = -((27 / 64) * Λ ^ 2) from by ring, norm_neg, norm_mul, hnorm2]
        norm_num
      rw [this] at hu
      exact lt_irrefl _ hu
    · -- u 0 = flavor point: distance to center exceeds the radius
      rw [h2] at hu
      have : ‖-((15 / 16) * Λ ^ 2) - ((3 / 4) * Λ ^ 2 + (27 / 64) * Λ ^ 2)‖
          = (135 / 64) * ‖Λ‖ ^ 2 := by
        rw [show -((15 / 16) * Λ ^ 2) - ((3 / 4) * Λ ^ 2 + (27 / 64) * Λ ^ 2)
            = -((135 / 64) * Λ ^ 2) from by ring, norm_neg, norm_mul, hnorm2]
        norm_num
      rw [this] at hu
      have hpos : (0 : ℝ) < ‖Λ‖ ^ 2 := by
        have := norm_pos_iff.mpr hΛ
        positivity
      nlinarith
  hVsc := by
    have hconv : Convex ℝ (Metric.ball (matterADCenter Λ) (matterADRadius Λ)) :=
      convex_ball _ _
    have hne : (Metric.ball (matterADCenter Λ) (matterADRadius Λ)).Nonempty :=
      ⟨matterADCenter Λ, Metric.mem_ball_self (matterADRadius_pos hΛ)⟩
    have := hconv.contractibleSpace hne
    infer_instance
  a := fun u => ![u 0 - (3 / 4) * Λ ^ 2]
  ha := by
    have hproj : Differentiable ℂ (fun u : Fin 1 → ℂ => u 0) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).differentiable
    rw [differentiableOn_pi]
    intro i
    fin_cases i
    exact ((hproj.sub_const _).differentiableOn)
  haInj := by
    intro u hu v hv h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero] at h0
    funext i
    fin_cases i
    exact sub_left_injective h0
  aD := fun u => ![Complex.I * (u 0 - (3 / 4) * Λ ^ 2)]
  haD := by
    have hproj : Differentiable ℂ (fun u : Fin 1 → ℂ => u 0) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).differentiable
    rw [differentiableOn_pi]
    intro i
    fin_cases i
    exact (((hproj.sub_const _).const_mul _).differentiableOn)
  tau := fun _ => ⟨Matrix.of fun _ _ => Complex.I, by
    constructor
    · ext i j
      simp [Matrix.transpose_apply, Matrix.of_apply]
    · have h : (Matrix.of fun (_ _ : Fin 1) => Complex.I).map Complex.im
          = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
        ext i j
        fin_cases i
        fin_cases j
        simp [Matrix.map_apply, Matrix.of_apply, Matrix.one_apply, Complex.I_im]
      rw [h]
      exact Matrix.PosDef.one⟩
/-! ## A5 (cont.) — special geometry of the witness, and A6 — the cusp data -/

private lemma partialDeriv_F (x : Fin 1 → ℂ) :
    partialDeriv (fun z : Fin 1 → ℂ => (Complex.I / 2) * (z 0) ^ 2) 0 x
      = Complex.I * x 0 := by
  set prj := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0 with hprj
  have h0 : HasFDerivAt (fun z : Fin 1 → ℂ => z 0) prj x := prj.hasFDerivAt
  have h2 := h0.pow 2
  have h1 := h2.const_mul (Complex.I / 2)
  rw [partialDeriv, h1.fderiv]
  simp only [ContinuousLinearMap.smul_apply, hprj, ContinuousLinearMap.proj_apply,
    Pi.single_eq_same, smul_eq_mul, pow_one]
  push_cast
  ring

private lemma partialDeriv2_F (x : Fin 1 → ℂ) :
    partialDeriv2 (fun z : Fin 1 → ℂ => (Complex.I / 2) * (z 0) ^ 2) 0 0 x
      = Complex.I := by
  rw [partialDeriv2]
  have hev : (fun y => partialDeriv (fun z : Fin 1 → ℂ => (Complex.I / 2) * (z 0) ^ 2) 0 y)
      = fun y : Fin 1 → ℂ => Complex.I * y 0 := funext partialDeriv_F
  rw [hev]
  set prj := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0 with hprj
  have h0 : HasFDerivAt (fun z : Fin 1 → ℂ => z 0) prj x := prj.hasFDerivAt
  have h1 := h0.const_mul Complex.I
  rw [partialDeriv, h1.fderiv]
  simp only [ContinuousLinearMap.smul_apply, hprj, ContinuousLinearMap.proj_apply,
    Pi.single_eq_same, smul_eq_mul, mul_one]

/-- The witness chart carries special geometry: `F = (i/2)z²`. -/
theorem matterADChart_specialGeometry (Λ : ℂ) (hΛ : Λ ≠ 0) :
    (matterADChart Λ hΛ).SpecialGeometry := by
  refine ⟨fun z => (Complex.I / 2) * (z 0) ^ 2, ?_, ?_, ?_⟩
  · apply ContDiff.contDiffOn
    have hproj : ContDiff ℂ 2 (fun z : Fin 1 → ℂ => z 0) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).contDiff
    exact contDiff_const.mul (hproj.pow 2)
  · intro u _ i
    fin_cases i
    show (matterADChart Λ hΛ).aD u 0
      = partialDeriv _ 0 ((matterADChart Λ hΛ).a u)
    rw [partialDeriv_F]
    simp [matterADChart]
  · intro u _ i j
    fin_cases i
    fin_cases j
    show ((matterADChart Λ hΛ).tau u).val 0 0
      = partialDeriv2 _ 0 0 ((matterADChart Λ hΛ).a u)
    rw [partialDeriv2_F]
    rfl

/-- The witness chart is a matter-polarized period chart for the AD-mass family. -/
theorem matterADChart_polarized (Λ : ℂ) (hΛ : Λ ≠ 0) :
    IsMatterPolarizedPeriodChart (matterADChart Λ hΛ) 1 Λ ![-(3 / 4) * Λ] := by
  refine ⟨matterADChart_specialGeometry Λ hΛ, ?_⟩
  ext u
  show (u 0 = (3 / 4) * Λ ^ 2 ∨ u 0 = -((15 / 16) * Λ ^ 2)) ↔ _
  exact (matter_ad_not_squarefree_iff Λ hΛ (u 0)).symm

/-- **A6 — the cusp data**: at the (unique) AD point, the electric and magnetic unit
charges — Dirac pairing 1 — both have vanishing central charge. -/
theorem matterADChart_rigidityData (Λ : ℂ) (hΛ : Λ ≠ 0) :
    MatterPeriodRigidityData (matterADChart Λ hΛ) 1 Λ ![-(3 / 4) * Λ] := by
  constructor
  intro u₀ hcusp
  have hu₀ := matter_ad_cusp_unique hΛ hcusp
  subst hu₀
  constructor
  · constructor
    · show _ ∈ closure (Metric.ball (matterADCenter Λ) (matterADRadius Λ))
      rw [closure_ball _ (matterADRadius_pos hΛ).ne']
      rw [Metric.mem_closedBall, pi_one_dist]
      have hnorm2 : ‖(Λ : ℂ) ^ 2‖ = ‖Λ‖ ^ 2 := norm_pow Λ 2
      rw [show (![(3 / 4) * Λ ^ 2] : Fin 1 → ℂ) 0 - matterADCenter Λ 0
          = -((27 / 64) * Λ ^ 2) from by simp [matterADCenter]]
      rw [norm_neg, norm_mul, hnorm2, matterADRadius]
      norm_num
    · show (![(3 / 4) * Λ ^ 2] : Fin 1 → ℂ) 0 = (3 / 4) * Λ ^ 2 ∨ _
      left
      simp
  · refine ⟨(Pi.single 0 1, 0), (0, Pi.single 0 1), ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrFun h1 0
      simp [Pi.single_eq_same] at h2
    · intro h
      have h1 := congrArg Prod.snd h
      have h2 := congrFun h1 0
      simp [Pi.single_eq_same] at h2
    · show (intersectionForm ((Pi.single 0 1 : Fin 1 → ℤ), (0 : Fin 1 → ℤ))
        ((0 : Fin 1 → ℤ), (Pi.single 0 1 : Fin 1 → ℤ))).natAbs = 1
      simp [intersectionForm, Fin.sum_univ_one, Pi.single_eq_same]
    · have hZ : ∀ u : Fin 1 → ℂ,
          (matterADChart Λ hΛ).periodCombination u ((Pi.single 0 1 : Fin 1 → ℤ), 0)
            = u 0 - (3 / 4) * Λ ^ 2 := by
        intro u
        simp [PeriodChart.periodCombination, matterADChart, Fin.sum_univ_one,
          Pi.single_eq_same]
      have hcont : Filter.Tendsto (fun u : Fin 1 → ℂ => u 0 - (3 / 4) * Λ ^ 2)
          (nhds (![(3 / 4) * Λ ^ 2] : Fin 1 → ℂ)) (nhds 0) := by
        have h1 : Continuous (fun u : Fin 1 → ℂ => u 0 - (3 / 4) * Λ ^ 2) :=
          (continuous_apply 0).sub continuous_const
        have h2 := h1.tendsto (![(3 / 4) * Λ ^ 2] : Fin 1 → ℂ)
        simpa using h2
      refine Filter.Tendsto.congr (fun u => (hZ u).symm) ?_
      exact hcont.mono_left nhdsWithin_le_nhds
    · have hZ : ∀ u : Fin 1 → ℂ,
          (matterADChart Λ hΛ).periodCombination u (0, (Pi.single 0 1 : Fin 1 → ℤ))
            = Complex.I * (u 0 - (3 / 4) * Λ ^ 2) := by
        intro u
        simp [PeriodChart.periodCombination, matterADChart, Fin.sum_univ_one,
          Pi.single_eq_same]
      have hcont : Filter.Tendsto
          (fun u : Fin 1 → ℂ => Complex.I * (u 0 - (3 / 4) * Λ ^ 2))
          (nhds (![(3 / 4) * Λ ^ 2] : Fin 1 → ℂ)) (nhds 0) := by
        have h1 : Continuous
            (fun u : Fin 1 → ℂ => Complex.I * (u 0 - (3 / 4) * Λ ^ 2)) :=
          continuous_const.mul ((continuous_apply 0).sub continuous_const)
        have h2 := h1.tendsto (![(3 / 4) * Λ ^ 2] : Fin 1 → ℂ)
        simpa using h2
      refine Filter.Tendsto.congr (fun u => (hZ u).symm) ?_
      exact hcont.mono_left nhdsWithin_le_nhds

/-- **The discharge theorem** — the statement of the former `matterPeriodRigidityAxiom`
at its consumed instantiation, now a construction. (The witness is DISCLOSED as
non-SQCD — see the module header and `audit/MPRA_DISCHARGE_PLAN.md`.) -/
theorem matterPeriodRigidity_nf1_ad (Λ : ℂ) (hΛ : Λ ≠ 0) :
    ∃ (B : PeriodBase 1) (s : PeriodChart B),
      IsMatterPolarizedPeriodChart s 1 Λ ![-(3 / 4) * Λ]
        ∧ MatterPeriodRigidityData s 1 Λ ![-(3 / 4) * Λ] :=
  ⟨matterADBase Λ, matterADChart Λ hΛ,
    matterADChart_polarized Λ hΛ, matterADChart_rigidityData Λ hΛ⟩

/-- **M6 — the `N_f = 1` matter theory has a nonempty Argyres–Douglas locus** — now
**axiom-free** (standard-3): there is a special-geometry theory whose singular locus is
the matter curve's discriminant and whose moduli space contains an AD point — two
mutually non-local charges massless together. (`IsMatterPolarizedPeriodChart` is H1 +
the discriminant tie; the fuller H2/H5/H6 that would pin it as *the unique* `SU(2)`
SQCD theory are deferred — the constructed witness makes that under-specification
formal; see the plan.) -/
theorem matter_argyresDouglasLocus_nonempty (Λ : ℂ) (hΛ : Λ ≠ 0) :
    ∃ (B : PeriodBase 1) (s : PeriodChart B),
      IsMatterPolarizedPeriodChart s 1 Λ ![-(3 / 4) * Λ]
        ∧ s.NonLocalDegenerationLocus.Nonempty := by
  obtain ⟨B, s, hphys, hlayer⟩ := matterPeriodRigidity_nf1_ad Λ hΛ
  exact ⟨B, s, hphys, argyresDouglasLocus_nonempty_of_matterPeriodLayer s Λ hΛ hlayer⟩

end SeibergWitten.Physics





