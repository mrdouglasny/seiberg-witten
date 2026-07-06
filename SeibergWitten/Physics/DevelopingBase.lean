/-
# Deriving the developing base: the monodromy clause demoted to a theorem

`audit/DEVELOPING_BASE_PLAN.md`. The rank-1 developing condition
`λ(τ(u)) = 2Λ²/(u+Λ²)` looked like a strong postulate — a pinned exact formula. This
file **derives** it from purely qualitative data (`SWModulusData`): the modulus
observable `J = λ∘τ` — single-valued on the full punctured u-plane because the SW
monodromies lie in `Γ(2)·{±1}` (the H3+H4 group-theory residue) — is analytic there,
omits `{0,1}` (automatic from `Im τ > 0`), and has three qualitative cusp limits
recording which BPS state is light where (H2): `J → 1` at the monopole point,
`|J| → ∞` at the dyon point, `J → 0` at weak coupling. Then `J = 2Λ²/(u+Λ²)` EXACTLY —
degree, rates, and the normalization `2Λ²` are all **derived**:

* Riemann removability makes `K = J⁻¹` entire (`analyticAt_of_differentiable_on_
  punctured_nhds_of_continuousAt`);
* `K` vanishes only at the dyon point, to finite positive order `p` (identity theorem);
* factoring off the zero and a **polynomial-growth Liouville** theorem
  (`entire_polynomial_of_growth`, dslope induction on the exponent) give
  `J = c₀/(u+Λ²)^p`;
* the omit-1 clause plus distinctness of `p`-th roots force `p = 1`, and the single
  solution of `u + Λ² = c₀` being the monopole point forces `c₀ = 2Λ²`.

No Picard, no Riemann–Hurwitz. Footprint: **standard-3 — no axioms at all**, not even
the covering pair. The chain to the headline: `λ∘f = J` on the chart plus
`SWModulusData` gives `IsSWDevelopingMap` (`isSWDevelopingMap_of_modulusData`), and the
existing rigidity applies (`sw_su2_unique_of_modulusData`).

Non-vacuity both ways (`audit/numerical/validate_devbase.py`, 13/13): the cross-ratio
itself satisfies the data (`swModulusData_swCrossRatio`); the `p = 2` candidate
`4Λ⁴/(u+Λ²)²` passes every cusp clause but hits `J = 1` at the smooth point `u = −3Λ²`
— the omit-1 clause that kills it is physics (an extra would-be singularity), not
bookkeeping.
-/
import SeibergWitten.Physics.SU2Rigidity

namespace SeibergWitten.Physics
namespace SU2

open Complex Filter Set Polynomial
open scoped Topology

/-! ## A polynomial-growth Liouville theorem -/

/-- **Polynomial-growth Liouville.** An entire function bounded by `C‖z‖^n` outside a
ball is the evaluation of a polynomial. Induction on `n` via `dslope`; the base case is
Liouville's theorem. -/
theorem entire_polynomial_of_growth (n : ℕ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (C R : ℝ) (hb : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n) :
    ∃ P : Polynomial ℂ, ∀ z, f z = P.eval z := by
  induction n generalizing f C R with
  | zero =>
    have hbdd : Bornology.IsBounded (Set.range f) := by
      rw [isBounded_iff_forall_norm_le]
      obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) |R|).exists_bound_of_continuousOn
        hf.continuous.continuousOn
      refine ⟨max M C, ?_⟩
      rintro - ⟨z, rfl⟩
      rcases le_or_gt ‖z‖ |R| with hz | hz
      · exact le_max_of_le_left (hM z (by simpa [Metric.mem_closedBall, dist_eq_norm]))
      · have h1 := hb z ((le_abs_self R).trans hz.le)
        simpa using le_max_of_le_right (by simpa using h1)
    obtain ⟨c, hc⟩ := hf.exists_const_forall_eq_of_bounded hbdd
    exact ⟨Polynomial.C c, fun z => by simp [hc z]⟩
  | succ n ih =>
    have hgd : Differentiable ℂ (dslope f 0) := by
      rw [← differentiableOn_univ] at hf ⊢
      exact (Complex.differentiableOn_dslope univ_mem).mpr hf
    have hgb : ∀ z : ℂ, max R 1 ≤ ‖z‖ →
        ‖dslope f 0 z‖ ≤ (C + ‖f 0‖) * ‖z‖ ^ n := by
      intro z hz
      have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (le_max_right _ _) hz
      have hzR : R ≤ ‖z‖ := le_trans (le_max_left _ _) hz
      have hz0 : z ≠ 0 := by
        intro h; rw [h, norm_zero] at hz1; linarith
      rw [dslope_of_ne f hz0, slope_def_field, sub_zero, norm_div]
      have hzpos : (0 : ℝ) < ‖z‖ := by linarith
      rw [div_le_iff₀ hzpos]
      have h2 : ‖f z - f 0‖ ≤ C * ‖z‖ ^ (n + 1) + ‖f 0‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact hb z hzR)
      have hpow1 : (1 : ℝ) ≤ ‖z‖ ^ (n + 1) := one_le_pow₀ hz1
      have hexp : (C + ‖f 0‖) * ‖z‖ ^ n * ‖z‖
          = C * ‖z‖ ^ (n + 1) + ‖f 0‖ * ‖z‖ ^ (n + 1) := by ring
      rw [hexp]
      nlinarith [norm_nonneg (f 0)]
    obtain ⟨Q, hQ⟩ := ih (dslope f 0) hgd (C + ‖f 0‖) (max R 1) hgb
    refine ⟨Polynomial.C (f 0) + Polynomial.X * Q, fun z => ?_⟩
    have h1 := sub_smul_dslope f 0 z
    simp only [sub_zero, smul_eq_mul] at h1
    have hfz : f z = f 0 + z * dslope f 0 z := by rw [h1]; ring
    simp [hfz, hQ z]

/-! ## The qualitative modulus data -/

/-- **The qualitative SW modulus data** — what remains of the "monodromy postulate" after
the derivation. `J` is the modulus observable `λ∘τ`, single-valued on the full punctured
u-plane precisely because the SW monodromies lie in `Γ(2)·{±1}` (the H3+H4 group-theory
residue); it omits `{0,1}` (automatic from `Im τ > 0`: `λ` maps `ℍ` into `ℂ∖{0,1}`); and
it has three **qualitative** cusp limits — which BPS state is light where (H2): value `1`
at the monopole point, a pole at the dyon point, `0` at weak coupling. No rates, no
normalization, no pinned formula: those are derived (`swModulusData_eq_crossRatio`). The
two-puncture domain is the singularity count of `SingularityCount.lean`. -/
structure SWModulusData (Λ : ℂ) (J : ℂ → ℂ) : Prop where
  diff : ∀ u : ℂ, u ≠ Λ ^ 2 → u ≠ -Λ ^ 2 → DifferentiableAt ℂ J u
  ne_zero : ∀ u : ℂ, u ≠ Λ ^ 2 → u ≠ -Λ ^ 2 → J u ≠ 0
  ne_one : ∀ u : ℂ, u ≠ Λ ^ 2 → u ≠ -Λ ^ 2 → J u ≠ 1
  monopole : Tendsto J (𝓝[≠] (Λ ^ 2)) (𝓝 1)
  dyon : Tendsto (fun u => (J u)⁻¹) (𝓝[≠] (-Λ ^ 2)) (𝓝 0)
  weak : Tendsto J (cocompact ℂ) (𝓝 0)

section Derivation

variable {Λ : ℂ} {J : ℂ → ℂ}

private lemma sq_ne_neg_sq' (hΛ : Λ ≠ 0) : Λ ^ 2 ≠ -Λ ^ 2 := by
  intro h
  apply hΛ
  have h2 : (2 : ℂ) * Λ ^ 2 = 0 := by linear_combination h
  have h3 := mul_eq_zero.mp h2
  simpa [pow_eq_zero_iff] using h3.resolve_left (by norm_num)

private lemma denom_pow_ne_zero {v : ℂ} (h2 : v ≠ -Λ ^ 2) (p : ℕ) :
    (v + Λ ^ 2) ^ p ≠ 0 := by
  apply pow_ne_zero
  intro h0
  exact h2 (by linear_combination h0)

/-- The analysis core: the modulus data forces `J = c₀/(u+Λ²)^p` on the punctured plane,
for some `c₀ ≠ 0` and `p ≥ 1`. Removability → entire reciprocal → order factorization →
polynomial-growth Liouville → a nonvanishing polynomial is constant. -/
private lemma exists_pow_form (hΛ : Λ ≠ 0) (h : SWModulusData Λ J) :
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∃ p : ℕ, 1 ≤ p ∧
      ∀ u : ℂ, u ≠ Λ ^ 2 → u ≠ -Λ ^ 2 → J u = c₀ / (u + Λ ^ 2) ^ p := by
  classical
  have hne : Λ ^ 2 ≠ -Λ ^ 2 := sq_ne_neg_sq' hΛ
  -- the extended reciprocal
  set K : ℂ → ℂ := fun v => if v = Λ ^ 2 then 1 else if v = -Λ ^ 2 then 0 else (J v)⁻¹
    with hKdef
  have hKoff : ∀ v : ℂ, v ≠ Λ ^ 2 → v ≠ -Λ ^ 2 → K v = (J v)⁻¹ := by
    intro v h1 h2; simp [hKdef, h1, h2]
  have hKmono : K (Λ ^ 2) = 1 := by simp [hKdef]
  have hKdyon : K (-Λ ^ 2) = 0 := by simp [hKdef, Ne.symm hne]
  -- differentiability of K away from the two points
  have hKdiff_off : ∀ v : ℂ, v ≠ Λ ^ 2 → v ≠ -Λ ^ 2 → DifferentiableAt ℂ K v := by
    intro v h1 h2
    have hev : K =ᶠ[𝓝 v] fun w => (J w)⁻¹ := by
      have hmem : {w : ℂ | w ≠ Λ ^ 2} ∩ {w : ℂ | w ≠ -Λ ^ 2} ∈ 𝓝 v :=
        (isOpen_compl_singleton.inter isOpen_compl_singleton).mem_nhds ⟨h1, h2⟩
      filter_upwards [hmem] with w hw
      exact hKoff w hw.1 hw.2
    exact ((h.diff v h1 h2).inv (h.ne_zero v h1 h2)).congr_of_eventuallyEq hev
  -- eventual identification on punctured neighborhoods of the two special points
  have hKev_mono : K =ᶠ[𝓝[≠] (Λ ^ 2)] fun w => (J w)⁻¹ := by
    have hmem : {w : ℂ | w ≠ -Λ ^ 2} ∈ 𝓝[≠] (Λ ^ 2) :=
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hne)
    filter_upwards [hmem, self_mem_nhdsWithin] with w hw2 hw1
    exact hKoff w hw1 hw2
  have hKev_dyon : K =ᶠ[𝓝[≠] (-Λ ^ 2)] fun w => (J w)⁻¹ := by
    have hmem : {w : ℂ | w ≠ Λ ^ 2} ∈ 𝓝[≠] (-Λ ^ 2) :=
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    filter_upwards [hmem, self_mem_nhdsWithin] with w hw1 hw2
    exact hKoff w hw1 hw2
  -- removability at the two points
  have hK_mono_an : AnalyticAt ℂ K (Λ ^ 2) := by
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · have hmem : {w : ℂ | w ≠ -Λ ^ 2} ∈ 𝓝[≠] (Λ ^ 2) :=
        nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hne)
      filter_upwards [hmem, self_mem_nhdsWithin] with w hw2 hw1
      exact hKdiff_off w hw1 hw2
    · rw [ContinuousAt, ← nhdsNE_sup_pure, hKmono]
      refine Tendsto.sup ?_ ?_
      · have h1 : Tendsto (fun w => (J w)⁻¹) (𝓝[≠] (Λ ^ 2)) (𝓝 1) := by
          simpa using h.monopole.inv₀ one_ne_zero
        exact h1.congr' hKev_mono.symm
      · have hpure := tendsto_pure_nhds K (Λ ^ 2)
        rwa [hKmono] at hpure
  have hK_dyon_an : AnalyticAt ℂ K (-Λ ^ 2) := by
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · have hmem : {w : ℂ | w ≠ Λ ^ 2} ∈ 𝓝[≠] (-Λ ^ 2) :=
        nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
      filter_upwards [hmem, self_mem_nhdsWithin] with w hw1 hw2
      exact hKdiff_off w hw1 hw2
    · rw [ContinuousAt, ← nhdsNE_sup_pure, hKdyon]
      refine Tendsto.sup (h.dyon.congr' hKev_dyon.symm) ?_
      have hpure := tendsto_pure_nhds K (-Λ ^ 2)
      rwa [hKdyon] at hpure
  -- K is entire
  have hK : Differentiable ℂ K := by
    intro v
    rcases eq_or_ne v (Λ ^ 2) with rfl | h1
    · exact hK_mono_an.differentiableAt
    rcases eq_or_ne v (-Λ ^ 2) with rfl | h2
    · exact hK_dyon_an.differentiableAt
    exact hKdiff_off v h1 h2
  -- K vanishes only at the dyon point
  have hKne : ∀ v : ℂ, v ≠ -Λ ^ 2 → K v ≠ 0 := by
    intro v h2
    rcases eq_or_ne v (Λ ^ 2) with rfl | h1
    · rw [hKmono]; exact one_ne_zero
    · rw [hKoff v h1 h2]
      exact inv_ne_zero (h.ne_zero v h1 h2)
  -- finite positive vanishing order at the dyon point
  have hord_ne_top : analyticOrderAt K (-Λ ^ 2) ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hKan : AnalyticOnNhd ℂ K Set.univ := fun v _ => hK.analyticAt v
    have hzero : Set.EqOn K 0 Set.univ :=
      hKan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ (-Λ ^ 2)) htop
    have h1 := hzero (Set.mem_univ (Λ ^ 2))
    rw [hKmono] at h1
    exact one_ne_zero h1
  obtain ⟨p, hp⟩ : ∃ p : ℕ, analyticOrderAt K (-Λ ^ 2) = (p : ℕ∞) := by
    obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp hord_ne_top
    exact ⟨p, hp.symm⟩
  have hp1 : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with rfl | h1
    · exfalso
      have h0 : analyticOrderAt K (-Λ ^ 2) ≠ 0 :=
        analyticOrderAt_ne_zero.mpr ⟨hK_dyon_an, hKdyon⟩
      exact h0 (by exact_mod_cast hp)
    · exact h1
  obtain ⟨g, hg_an, hg0, hfac⟩ := (hK_dyon_an.analyticOrderAt_eq_natCast).mp hp
  -- globalize the factorization: H entire, nonvanishing, K = (·+Λ²)^p · H
  set H : ℂ → ℂ := fun v => if v = -Λ ^ 2 then g (-Λ ^ 2) else K v / (v + Λ ^ 2) ^ p
    with hHdef
  have hHoff : ∀ v : ℂ, v ≠ -Λ ^ 2 → H v = K v / (v + Λ ^ 2) ^ p := by
    intro v h2; simp [hHdef, h2]
  have hHev : H =ᶠ[𝓝 (-Λ ^ 2)] g := by
    filter_upwards [hfac] with v hv
    rcases eq_or_ne v (-Λ ^ 2) with rfl | h2
    · simp [hHdef]
    · have hpow := denom_pow_ne_zero (Λ := Λ) h2 p
      have hKv : K v = (v + Λ ^ 2) ^ p * g v := by
        rw [hv, smul_eq_mul]
        ring
      rw [hHoff v h2, hKv, mul_div_cancel_left₀ _ hpow]
  have hH_an_dyon : AnalyticAt ℂ H (-Λ ^ 2) := hg_an.congr hHev.symm
  have hHdiff : Differentiable ℂ H := by
    intro v
    rcases eq_or_ne v (-Λ ^ 2) with rfl | h2
    · exact hH_an_dyon.differentiableAt
    · have hev : H =ᶠ[𝓝 v] fun w => K w / (w + Λ ^ 2) ^ p := by
        have hmem : {w : ℂ | w ≠ -Λ ^ 2} ∈ 𝓝 v := isOpen_compl_singleton.mem_nhds h2
        filter_upwards [hmem] with w hw
        exact hHoff w hw
      have hpow := denom_pow_ne_zero (Λ := Λ) h2 p
      exact ((hK v).div (((differentiableAt_fun_id).add_const _).pow p) hpow
        ).congr_of_eventuallyEq hev
  have hHne : ∀ v : ℂ, H v ≠ 0 := by
    intro v
    rcases eq_or_ne v (-Λ ^ 2) with rfl | h2
    · simpa [hHdef] using hg0
    · rw [hHoff v h2]
      exact div_ne_zero (hKne v h2) (denom_pow_ne_zero h2 p)
  have hKH : ∀ v : ℂ, v ≠ -Λ ^ 2 → K v = (v + Λ ^ 2) ^ p * H v := by
    intro v h2
    rw [hHoff v h2, mul_comm, div_mul_cancel₀ _ (denom_pow_ne_zero h2 p)]
  -- G = 1/H is entire with polynomial growth, hence a nonvanishing polynomial: constant
  have hGdiff : Differentiable ℂ (fun v => (H v)⁻¹) := fun v => (hHdiff v).inv (hHne v)
  -- outside a large ball, ‖K‖ ≥ 1, so ‖G‖ ≤ ‖v+Λ²‖^p ≤ 2^p ‖v‖^p
  have hKbig : ∀ᶠ v in cocompact ℂ, 1 ≤ ‖K v‖ := by
    have hJsmall : ∀ᶠ v in cocompact ℂ, ‖J v‖ < 1 := by
      have hw := h.weak
      rw [Metric.tendsto_nhds] at hw
      simpa [dist_eq_norm] using hw 1 one_pos
    have h1 : ∀ᶠ v in cocompact ℂ, v ≠ Λ ^ 2 := by
      have := (isCompact_singleton : IsCompact {(Λ ^ 2 : ℂ)}).compl_mem_cocompact
      filter_upwards [this] with v hv
      simpa using hv
    have h2 : ∀ᶠ v in cocompact ℂ, v ≠ -Λ ^ 2 := by
      have := (isCompact_singleton : IsCompact {(-Λ ^ 2 : ℂ)}).compl_mem_cocompact
      filter_upwards [this] with v hv
      simpa using hv
    filter_upwards [hJsmall, h1, h2] with v hv hv1 hv2
    rw [hKoff v hv1 hv2, norm_inv]
    have h0 : (0 : ℝ) < ‖J v‖ :=
      norm_pos_iff.mpr (h.ne_zero v hv1 hv2)
    exact one_le_inv_iff₀.mpr ⟨h0, hv.le⟩
  obtain ⟨s, hs_comp, hs⟩ := mem_cocompact.mp hKbig
  obtain ⟨R₀, hR₀⟩ := hs_comp.isBounded.subset_closedBall (0 : ℂ)
  set R₁ : ℝ := max (R₀ + 1) (max (‖(Λ : ℂ) ^ 2‖ + 1) 1) with hR₁def
  have hGgrow : ∀ v : ℂ, R₁ ≤ ‖v‖ → ‖(H v)⁻¹‖ ≤ 2 ^ p * ‖v‖ ^ p := by
    intro v hv
    have hvR₀ : R₀ < ‖v‖ := by
      have := le_trans (le_max_left _ _) hv; linarith
    have hvΛ : ‖(Λ : ℂ) ^ 2‖ < ‖v‖ := by
      have := le_trans (le_max_of_le_right (le_max_left _ _)) hv; linarith
    have hv1 : (1 : ℝ) ≤ ‖v‖ :=
      le_trans (le_max_of_le_right (le_max_right _ _)) hv
    have hv2 : v ≠ -Λ ^ 2 := by
      intro h0
      rw [h0, norm_neg] at hvΛ
      exact lt_irrefl _ hvΛ
    have hvK : 1 ≤ ‖K v‖ := by
      apply hs
      intro hmem
      exact absurd (Metric.mem_closedBall.mp (hR₀ hmem)) (by
        rw [dist_zero_right]; exact not_le.mpr hvR₀)
    rw [hHoff v hv2, inv_div, norm_div, norm_pow]
    have hK0 : ‖K v‖ ≠ 0 := by positivity
    calc ‖v + Λ ^ 2‖ ^ p / ‖K v‖ ≤ ‖v + Λ ^ 2‖ ^ p / 1 := by
          gcongr
      _ = ‖v + Λ ^ 2‖ ^ p := by rw [div_one]
      _ ≤ (2 * ‖v‖) ^ p := by
          gcongr
          calc ‖v + Λ ^ 2‖ ≤ ‖v‖ + ‖(Λ : ℂ) ^ 2‖ := norm_add_le _ _
            _ ≤ 2 * ‖v‖ := by linarith
      _ = 2 ^ p * ‖v‖ ^ p := by rw [mul_pow]
  obtain ⟨P, hP⟩ := entire_polynomial_of_growth p _ hGdiff (2 ^ p) R₁ hGgrow
  -- G is nonvanishing, so P has no roots, so P is a nonzero constant
  have hPne : ∀ z, P.eval z ≠ 0 := fun z => (hP z) ▸ inv_ne_zero (hHne z)
  have hPconst : P = Polynomial.C (P.coeff 0) := by
    rcases le_or_gt P.degree 0 with hd | hd
    · exact Polynomial.eq_C_of_degree_le_zero hd
    · obtain ⟨z, hz⟩ := Complex.exists_root hd
      exact absurd hz (hPne z)
  have hc₁ : P.coeff 0 ≠ 0 := by
    have h0 := hPne 0
    rwa [hPconst, Polynomial.eval_C] at h0
  have hHconst : ∀ v : ℂ, H v = (P.coeff 0)⁻¹ := by
    intro v
    have h1 := hP v
    rw [hPconst, Polynomial.eval_C] at h1
    rw [← h1, inv_inv]
  -- assemble
  refine ⟨P.coeff 0, hc₁, p, hp1, fun u h1 h2 => ?_⟩
  have hKu : (J u)⁻¹ = (u + Λ ^ 2) ^ p * (P.coeff 0)⁻¹ := by
    rw [← hKoff u h1 h2, hKH u h2, hHconst u]
  have hJu := h.ne_zero u h1 h2
  have hpow := denom_pow_ne_zero (Λ := Λ) h2 p
  rw [eq_div_iff hpow]
  have hmul : J u * (J u)⁻¹ = 1 := mul_inv_cancel₀ hJu
  rw [hKu] at hmul
  field_simp [hc₁] at hmul
  linear_combination hmul

end Derivation

/-! ## The derived developing base and the decomposed uniqueness headline -/

/-- **The derived developing base.** Qualitative modulus data forces the exact SW
cross-ratio: degree, rates, and the normalization `2Λ²` all come out. The former
"monodromy postulate" `λ(τ(u)) = 2Λ²/(u+Λ²)` is a THEOREM given `SWModulusData`. -/
theorem swModulusData_eq_crossRatio {Λ : ℂ} (hΛ : Λ ≠ 0) {J : ℂ → ℂ}
    (h : SWModulusData Λ J) :
    ∀ u : ℂ, u ≠ Λ ^ 2 → u ≠ -Λ ^ 2 → J u = swCrossRatio Λ u := by
  obtain ⟨c₀, hc₀, p, hp1, hJ⟩ := exists_pow_form hΛ h
  have hp0 : p ≠ 0 := by omega
  -- every solution of (w+Λ²)^p = c₀ must be the monopole point
  have hsol : ∀ w : ℂ, (w + Λ ^ 2) ^ p = c₀ → w = Λ ^ 2 := by
    intro w hw
    have hw2 : w ≠ -Λ ^ 2 := by
      intro h2
      rw [h2] at hw
      rw [show (-Λ ^ 2 + Λ ^ 2 : ℂ) = 0 by ring, zero_pow hp0] at hw
      exact hc₀ hw.symm
    by_contra hw1
    have hne1 := h.ne_one w hw1 hw2
    rw [hJ w hw1 hw2, hw, div_self hc₀] at hne1
    exact hne1 rfl
  -- p = 1 via two distinct p-th roots of c₀
  have hp_eq : p = 1 := by
    by_contra hp2
    have hp2' : 2 ≤ p := by omega
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq c₀ (by omega : 0 < p)
    have hwne : w ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp0] at hw
      exact hc₀ hw.symm
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * 1 / p) with hζdef
    have hζp : ζ ^ p = 1 := by
      rw [hζdef, ← Complex.exp_nat_mul]
      rw [show (p : ℂ) * (2 * Real.pi * Complex.I * 1 / p)
            = 2 * Real.pi * Complex.I by
          rw [mul_comm, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hp0), mul_one]]
      exact Complex.exp_two_pi_mul_I
    have hζ1 : ζ ≠ 1 := by
      rw [hζdef]
      intro h1
      have h1' : Complex.exp (2 * Real.pi * Complex.I * ((1 : ℕ) : ℂ) / ((p : ℕ) : ℂ)) = 1 := by
        push_cast
        exact h1
      have h2 := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := 1) (N := p) hp0).mp h1'
      have h3 := Nat.le_of_dvd one_pos h2
      omega
    have h1 := hsol (w - Λ ^ 2) (by rw [sub_add_cancel]; exact hw)
    have h2 := hsol (ζ * w - Λ ^ 2)
      (by rw [sub_add_cancel, mul_pow, hζp, one_mul]; exact hw)
    have hw2Λ : w = 2 * Λ ^ 2 := by linear_combination h1
    have hζw2Λ : ζ * w = 2 * Λ ^ 2 := by linear_combination h2
    rw [hw2Λ] at hζw2Λ
    have h2Λ : (2 : ℂ) * Λ ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ hΛ)
    exact hζ1 (mul_right_cancel₀ h2Λ (by rw [hζw2Λ, one_mul]))
  -- p = 1: the single solution pins c₀ = 2Λ²
  subst hp_eq
  have hc₀val : c₀ = 2 * Λ ^ 2 := by
    have := hsol (c₀ - Λ ^ 2) (by rw [pow_one]; ring)
    linear_combination this
  intro u h1 h2
  rw [hJ u h1 h2, hc₀val, pow_one]
  rfl

/-- **Non-vacuity**: the SW cross-ratio itself carries the qualitative modulus data. -/
theorem swModulusData_swCrossRatio {Λ : ℂ} (hΛ : Λ ≠ 0) :
    SWModulusData Λ (swCrossRatio Λ) := by
  have h2Λ : (2 : ℂ) * Λ ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ hΛ)
  have hdenom : ∀ u : ℂ, u ≠ -Λ ^ 2 → u + Λ ^ 2 ≠ 0 := by
    intro u h2 h0
    exact h2 (by linear_combination h0)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u _ h2
    have : DifferentiableAt ℂ (fun v : ℂ => 2 * Λ ^ 2 / (v + Λ ^ 2)) u :=
      (differentiableAt_const _).div ((differentiableAt_fun_id).add_const _)
        (hdenom u h2)
    exact this
  · intro u _ h2
    show 2 * Λ ^ 2 / (u + Λ ^ 2) ≠ 0
    exact div_ne_zero h2Λ (hdenom u h2)
  · intro u h1 h2 hone
    rw [show swCrossRatio Λ u = 2 * Λ ^ 2 / (u + Λ ^ 2) from rfl,
      div_eq_one_iff_eq (hdenom u h2)] at hone
    exact h1 (by linear_combination -hone)
  · have heq : swCrossRatio Λ = fun u : ℂ => 2 * Λ ^ 2 / (u + Λ ^ 2) := rfl
    have hd0 : (Λ : ℂ) ^ 2 + Λ ^ 2 ≠ 0 := by
      intro h0; exact h2Λ (by linear_combination h0)
    have hcont : ContinuousAt (swCrossRatio Λ) (Λ ^ 2) := by
      rw [heq]
      exact ContinuousAt.div continuousAt_const
        (continuousAt_id.add continuousAt_const) hd0
    have hval : swCrossRatio Λ (Λ ^ 2) = 1 := by
      rw [heq, div_eq_one_iff_eq hd0]; ring
    have h1 := hcont.tendsto
    rw [hval] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  · have hrw : ∀ u : ℂ, (swCrossRatio Λ u)⁻¹ = (u + Λ ^ 2) / (2 * Λ ^ 2) := by
      intro u
      rw [swCrossRatio, inv_div]
    have hcont : ContinuousAt (fun u : ℂ => (u + Λ ^ 2) / (2 * Λ ^ 2)) (-Λ ^ 2) := by
      simp only [div_eq_mul_inv]
      exact (continuousAt_id.add continuousAt_const).mul continuousAt_const
    have hval : ((-Λ ^ 2 : ℂ) + Λ ^ 2) / (2 * Λ ^ 2) = 0 := by
      rw [show ((-Λ ^ 2 : ℂ) + Λ ^ 2) = 0 by ring, zero_div]
    have h1 : Tendsto (fun u : ℂ => (u + Λ ^ 2) / (2 * Λ ^ 2)) (𝓝[≠] (-Λ ^ 2)) (𝓝 0) := by
      have h2 := hcont.tendsto
      rw [hval] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    exact h1.congr fun u => (hrw u).symm
  · rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_iff, mem_cocompact]
    refine ⟨Metric.closedBall 0 (‖(2 : ℂ) * Λ ^ 2‖ / ε + ‖(Λ : ℂ) ^ 2‖),
      isCompact_closedBall _ _, ?_⟩
    intro u hu
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hu
    simp only [Set.mem_setOf_eq, dist_zero_right]
    rw [show swCrossRatio Λ u = 2 * Λ ^ 2 / (u + Λ ^ 2) from rfl, norm_div]
    have hpos : (0 : ℝ) < ‖(2 : ℂ) * Λ ^ 2‖ / ε + ‖(Λ : ℂ) ^ 2‖ := by
      have := norm_pos_iff.mpr h2Λ
      positivity
    have hd : ‖(2 : ℂ) * Λ ^ 2‖ / ε < ‖u + Λ ^ 2‖ := by
      have h1 : ‖u‖ ≤ ‖u + Λ ^ 2‖ + ‖(Λ : ℂ) ^ 2‖ := by
        calc ‖u‖ = ‖(u + Λ ^ 2) - Λ ^ 2‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖u + Λ ^ 2‖ + ‖(Λ : ℂ) ^ 2‖ := norm_sub_le _ _
      linarith
    have hd0 : (0 : ℝ) < ‖u + Λ ^ 2‖ :=
      lt_of_le_of_lt (by positivity) hd
    rw [div_lt_iff₀ hd0]
    calc ‖(2 : ℂ) * Λ ^ 2‖ = (‖(2 : ℂ) * Λ ^ 2‖ / ε) * ε := by
          field_simp
      _ < ‖u + Λ ^ 2‖ * ε := by
          exact mul_lt_mul_of_pos_right hd hε
      _ = ε * ‖u + Λ ^ 2‖ := by ring

/-- Any coupling whose `λ`-composite agrees on its chart with a global modulus observable
carrying the qualitative cusp data is an SW developing map: the pinned formula is
derived, not postulated. -/
theorem isSWDevelopingMap_of_modulusData {Λ : ℂ} (hΛ : Λ ≠ 0) {J : ℂ → ℂ}
    (hJ : SWModulusData Λ J) {D : Set ℂ}
    (hD : ∀ u ∈ D, u ≠ Λ ^ 2 ∧ u ≠ -Λ ^ 2)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) (hfH : ∀ u ∈ D, 0 < (f u).im)
    (hdev : ∀ u ∈ D, modularLambdaFn (f u) = J u) :
    IsSWDevelopingMap Λ D f :=
  ⟨hf, hfH, fun u hu => by
    rw [hdev u hu, swModulusData_eq_crossRatio hΛ hJ u (hD u hu).1 (hD u hu).2]⟩

/-- **The decomposed uniqueness headline.** Two candidate couplings that are analytic and
ℍ-valued on a connected chart and develop the SAME global modulus observable with the
qualitative SW cusp data agree up to an explicit `Γ(2)` duality frame. Compared with
`sw_su2_unique`, the pinned developing formula has been replaced by its derivation. -/
theorem sw_su2_unique_of_modulusData {Λ : ℂ} (hΛ : Λ ≠ 0) {J : ℂ → ℂ}
    (hJ : SWModulusData Λ J) {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    {u₀ : ℂ} (hu₀ : u₀ ∈ D) (hD : ∀ u ∈ D, u ≠ Λ ^ 2 ∧ u ≠ -Λ ^ 2)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D) (hfH : ∀ u ∈ D, 0 < (f u).im)
    (hg : AnalyticOnNhd ℂ g D) (hgH : ∀ u ∈ D, 0 < (g u).im)
    (hdevf : ∀ u ∈ D, modularLambdaFn (f u) = J u)
    (hdevg : ∀ u ∈ D, modularLambdaFn (g u) = J u) :
    ∃ γ ∈ Gamma2, Set.EqOn f (fun u => moebiusOn γ (g u)) D :=
  sw_su2_unique hDo hDc hu₀
    ⟨isSWDevelopingMap_of_modulusData hΛ hJ hD hf hfH hdevf,
     isSWDevelopingMap_of_modulusData hΛ hJ hD hg hgH hdevg⟩

end SU2
end SeibergWitten.Physics
