/-
# Cusp-data campaign, step A: the λ-frame SW monodromies (`audit/CUSP_DATA_PLAN.md`)

The three local monodromies of the pure-`SU(2)` theory, in the frame of the modulus
`τ` that `modularLambdaFn` takes (the `Γ(2)`-curve modulus; conventions pinned by
`audit/numerical/validate_cuspdata.py`, 14/14 — including the width-2 check
`λ ≈ 16·e^{iπτ}`):

* `swMWeak = −T⁻² = [[-1,2],[0,-1]]` — weak coupling, `τ ↦ τ−2` with the Weyl `−1`;
* `swMMono = S T² S⁻¹ = [[1,0],[-2,1]]` — the monopole point, `τ ↦ τ/(1−2τ)`,
  parabolic fixing the cusp `0` (λ-value `1`);
* `swMDyon = swMMono⁻¹·swMWeak = [[-1,2],[-2,3]]` — the dyon point,
  `τ ↦ (−τ+2)/(−2τ+3)`, parabolic fixing the cusp `1` (λ-value `∞`); pinned by the
  factorization `swMMono * swMDyon = swMWeak` (proved).

All three are **parabolic** (`|trace| = 2`, `swM*_trace`) — the transcription of "a
single BPS state goes massless" demands it, and the trace check is in the oracle
(§A4: it caught a v1 slip where a hyperbolic Γ(2) element sat in the dyon slot;
det/mod-2/product/λ-invariance all pass for hyperbolic elements too).

Physics provenance (H2+H3): each finite matrix is the Picard–Lefschetz transvection of
the state H2 puts at that point, seen through the Landen doubling (width-2 cusps); the
weak-coupling matrix is the one-loop monodromy. What this file proves — the content
step B consumes for single-valuedness of `J = λ∘τ`:

* all three lie in `Γ(2)` itself (at level 2 the coset bookkeeping trivializes:
  `−I ∈ Γ(2)` since `−1 ≡ 1 (mod 2)`);
* `λ` is invariant under each of their Möbius actions on `ℍ`
  (`modularLambda_swMWeak/Mono/Dyon`), from the proved `T²`- and `ST²S⁻¹`-laws only.

Footprints: memberships and the factorization are standard-3; the invariance laws
consume the θ pair (through `modularLambda_S`), nothing else.
-/
import SeibergWitten.Physics.DevelopingBase

namespace SeibergWitten.Physics
namespace SU2

open Complex

/-- λ-frame weak-coupling monodromy `−T⁻²`: `τ ↦ τ − 2` with the Weyl `−1`. -/
def swMWeak : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![-1, 2; 0, -1], by norm_num [Matrix.det_fin_two_of]⟩

/-- λ-frame monopole monodromy `S T² S⁻¹`: `τ ↦ τ/(1−2τ)`, parabolic fixing `0`. -/
def swMMono : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 0; -2, 1], by norm_num [Matrix.det_fin_two_of]⟩

/-- λ-frame dyon monodromy, pinned by the factorization
`swMMono * swMDyon = swMWeak`: `τ ↦ (−τ+2)/(−2τ+3)`, parabolic fixing `1`. -/
def swMDyon : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![-1, 2; -2, 3], by norm_num [Matrix.det_fin_two_of]⟩

/-- Parabolicity (trace `±2`) — the faithfulness check for "one massless BPS state". -/
theorem swMWeak_trace : swMWeak.1 0 0 + swMWeak.1 1 1 = -2 := by decide

theorem swMMono_trace : swMMono.1 0 0 + swMMono.1 1 1 = 2 := by decide

theorem swMDyon_trace : swMDyon.1 0 0 + swMDyon.1 1 1 = 2 := by decide

/-- The monodromy factorization `M_∞ = M_monopole · M_dyon` (loop composition around
both strong-coupling points is the loop at infinity). -/
theorem swM_factorization : swMMono * swMDyon = swMWeak := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swMMono, swMDyon, swMWeak, Matrix.mul_apply, Fin.sum_univ_succ]

theorem swMWeak_mem_Gamma2 : swMWeak ∈ Gamma2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [swMWeak] <;> decide

theorem swMMono_mem_Gamma2 : swMMono ∈ Gamma2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [swMMono] <;> decide

theorem swMDyon_mem_Gamma2 : swMDyon ∈ Gamma2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [swMDyon] <;> decide

/-! ## The Möbius actions in closed form -/

theorem moebiusOn_swMWeak (τ : ℂ) : moebiusOn swMWeak τ = τ - 2 := by
  simp only [moebiusOn, swMWeak]
  norm_num
  ring

theorem moebiusOn_swMMono (τ : ℂ) : moebiusOn swMMono τ = τ / (1 - 2 * τ) := by
  simp only [moebiusOn, swMMono]
  norm_num
  ring_nf

theorem moebiusOn_swMDyon (τ : ℂ) : moebiusOn swMDyon τ = (-τ + 2) / (-2 * τ + 3) := by
  simp only [moebiusOn, swMDyon]
  norm_num

/-! ## λ-invariance of the three actions -/

private lemma two_mul_add_one_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : 2 * τ + 1 ≠ 0 := by
  intro h0
  have := congrArg Complex.im h0
  simp at this
  linarith

private lemma im_div_two_mul_add_one_pos {τ : ℂ} (hτ : 0 < τ.im) :
    0 < (τ / (2 * τ + 1)).im := by
  have hw := two_mul_add_one_ne_zero hτ
  have hns : 0 < Complex.normSq (2 * τ + 1) := Complex.normSq_pos.mpr hw
  have key : (τ / (2 * τ + 1)).im = τ.im / Complex.normSq (2 * τ + 1) := by
    rw [Complex.div_im]
    have hre : (2 * τ + 1).re = 2 * τ.re + 1 := by simp
    have him : (2 * τ + 1).im = 2 * τ.im := by simp
    rw [hre, him, div_sub_div_same]
    congr 1
    ring
  rw [key]
  positivity

/-- The `ST²S⁻¹`-law in rational form: `λ(σ/(1−2σ)) = λ(σ)` on `ℍ`. -/
theorem modularLambda_ST2S' {σ : ℂ} (hσ : 0 < σ.im) :
    modularLambdaFn (σ / (1 - 2 * σ)) = modularLambdaFn σ := by
  have hσ0 : σ ≠ 0 := by
    intro h0; rw [h0] at hσ; simp at hσ
  have h12 : 1 - 2 * σ ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hρ : -1 / σ + 2 ≠ 0 := by
    intro h0
    field_simp at h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have h := modularLambda_ST2S ⟨σ, hσ⟩
  have hrw : -1 / (-1 / σ + 2) = σ / (1 - 2 * σ) := by
    rw [div_eq_div_iff hρ h12]
    field_simp
    ring
  rw [hrw] at h
  exact h

theorem modularLambda_swMWeak (τ : ℂ) :
    modularLambdaFn (moebiusOn swMWeak τ) = modularLambdaFn τ := by
  rw [moebiusOn_swMWeak]
  have h := modularLambda_add_two (τ - 2)
  rw [show τ - 2 + 2 = τ from by ring] at h
  exact h.symm

theorem modularLambda_swMMono {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaFn (moebiusOn swMMono τ) = modularLambdaFn τ := by
  rw [moebiusOn_swMMono]
  exact modularLambda_ST2S' hτ

/-- The inverse `ST²S⁻¹` law in rational form: `λ(σ/(2σ+1)) = λ(σ)` on `ℍ`. -/
theorem modularLambda_ST2S_inv {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaFn (τ / (2 * τ + 1)) = modularLambdaFn τ := by
  set σ : ℂ := τ / (2 * τ + 1) with hσdef
  have hσim : 0 < σ.im := im_div_two_mul_add_one_pos hτ
  have hw := two_mul_add_one_ne_zero hτ
  have h := modularLambda_ST2S' hσim
  have hback : σ / (1 - 2 * σ) = τ := by
    have h1 : 1 - 2 * σ = 1 / (2 * τ + 1) := by
      rw [hσdef]
      field_simp
      ring
    rw [h1, div_div_eq_mul_div, div_one, hσdef, div_mul_cancel₀ _ hw]
  rw [hback] at h
  exact h.symm

theorem modularLambda_swMDyon {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaFn (moebiusOn swMDyon τ) = modularLambdaFn τ := by
  rw [moebiusOn_swMDyon]
  have hσim : 0 < (τ - 2).im := by
    rw [Complex.sub_im]
    simpa using hτ
  have h := modularLambda_ST2S_inv hσim
  have hden : 2 * (τ - 2) + 1 ≠ 0 := two_mul_add_one_ne_zero hσim
  have hrw : (τ - 2) / (2 * (τ - 2) + 1) = (-τ + 2) / (-2 * τ + 3) := by
    rw [div_eq_div_iff hden (by intro h0; apply hden; linear_combination -h0)]
    ring
  rw [hrw] at h
  rw [h, modularLambda_add_two (τ - 2) |>.symm]
  rw [show τ - 2 + 2 = τ from by ring]

/-! ## Step B: the monodromy group and atlas descent (`audit/CUSP_DATA_PLAN.md`)

The Möbius action infrastructure (positivity, composition — closing the composition
lemma the matter plan left optional), the monodromy group generated by the three
matrices, λ-invariance for the WHOLE group by closure induction, differentiability of
`λ` on `ℍ`, and the descent theorem: an H4-style atlas of local couplings glued by the
monodromy group has one well-defined global modulus observable `J`, analytic and
omitting `{0,1}` on the covered set. With the three cusp limits (steps D/E) this is
`SWModulusData` — the packaging is `swModulusData_of_atlas`, which displays exactly
what remains. Gluing is stated POINTWISE (`∃ γ` per point), weaker than H4's
locally-constant transitions — a weaker hypothesis, hence a stronger theorem. -/

/-- `Im (γ·z) = Im z / |cz+d|² > 0`: the Möbius action preserves `ℍ`. -/
theorem im_moebiusOn_pos (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {z : ℂ}
    (hz : 0 < z.im) : 0 < (moebiusOn γ z).im := by
  have hden := moebius_denom_ne_zero γ hz
  have hns : 0 < Complex.normSq (((γ.1 1 0 : ℤ) : ℂ) * z + ((γ.1 1 1 : ℤ) : ℂ)) :=
    Complex.normSq_pos.mpr hden
  have hdet : ((γ.1 0 0 : ℤ) : ℝ) * ((γ.1 1 1 : ℤ) : ℝ)
      - ((γ.1 0 1 : ℤ) : ℝ) * ((γ.1 1 0 : ℤ) : ℝ) = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    have h2 := congrArg (fun n : ℤ => (n : ℝ)) h
    push_cast at h2
    linarith
  have key : (moebiusOn γ z).im
      = z.im / Complex.normSq (((γ.1 1 0 : ℤ) : ℂ) * z + ((γ.1 1 1 : ℤ) : ℂ)) := by
    rw [moebiusOn, Complex.div_im, div_sub_div_same]
    congr 1
    simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
      Complex.intCast_im, Complex.intCast_re]
    linear_combination z.im * hdet
  rw [key]
  positivity

theorem moebiusOn_one (z : ℂ) : moebiusOn 1 z = z := by
  simp [moebiusOn]

private lemma moebius_comp_algebra {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ z : ℂ}
    (h₂ : c₂ * z + d₂ ≠ 0)
    (h₁ : c₁ * ((a₂ * z + b₂) / (c₂ * z + d₂)) + d₁ ≠ 0) :
    ((a₁ * a₂ + b₁ * c₂) * z + (a₁ * b₂ + b₁ * d₂))
        / ((c₁ * a₂ + d₁ * c₂) * z + (c₁ * b₂ + d₁ * d₂))
      = (a₁ * ((a₂ * z + b₂) / (c₂ * z + d₂)) + b₁)
        / (c₁ * ((a₂ * z + b₂) / (c₂ * z + d₂)) + d₁) := by
  have e1 : a₁ * ((a₂ * z + b₂) / (c₂ * z + d₂)) + b₁
      = (a₁ * (a₂ * z + b₂) + b₁ * (c₂ * z + d₂)) / (c₂ * z + d₂) := by
    rw [mul_div_assoc'] at *
    rw [div_add' _ _ _ h₂]
  have e2 : c₁ * ((a₂ * z + b₂) / (c₂ * z + d₂)) + d₁
      = (c₁ * (a₂ * z + b₂) + d₁ * (c₂ * z + d₂)) / (c₂ * z + d₂) := by
    rw [mul_div_assoc'] at *
    rw [div_add' _ _ _ h₂]
  rw [e1, e2, div_div_div_cancel_right₀ h₂]
  congr 1 <;> ring

/-- Composition of the Möbius action on `ℍ` (the lemma the matter plan left optional). -/
theorem moebiusOn_mul (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {z : ℂ}
    (hz : 0 < z.im) :
    moebiusOn (γ₁ * γ₂) z = moebiusOn γ₁ (moebiusOn γ₂ z) := by
  have h₂ := moebius_denom_ne_zero γ₂ hz
  have h₁ := moebius_denom_ne_zero γ₁ (im_moebiusOn_pos γ₂ hz)
  simp only [moebiusOn] at h₁ h₂ ⊢
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Fin.isValue] at ⊢
  push_cast
  exact moebius_comp_algebra h₂ h₁

/-- The subgroup generated by the three SW monodromies — the image of `π₁` of the
thrice-punctured plane under the H3+H4 monodromy representation. -/
def swMonodromyGroup : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
  Subgroup.closure {swMWeak, swMMono, swMDyon}

theorem swMonodromyGroup_le_Gamma2 : swMonodromyGroup ≤ Gamma2 := by
  rw [swMonodromyGroup, Subgroup.closure_le]
  rintro γ (rfl | rfl | rfl)
  · exact swMWeak_mem_Gamma2
  · exact swMMono_mem_Gamma2
  · exact swMDyon_mem_Gamma2

/-- **λ-invariance under the whole monodromy group**, by closure induction from the
three proved laws — this is the single-valuedness content of step B. -/
theorem modularLambda_swMonodromyGroup {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ swMonodromyGroup) :
    ∀ z : ℂ, 0 < z.im → modularLambdaFn (moebiusOn γ z) = modularLambdaFn z := by
  induction hγ using Subgroup.closure_induction with
  | mem γ hγ =>
    rcases hγ with rfl | rfl | rfl
    · exact fun z _ => modularLambda_swMWeak z
    · exact fun z hz => modularLambda_swMMono hz
    · exact fun z hz => modularLambda_swMDyon hz
  | one => exact fun z _ => by rw [moebiusOn_one]
  | mul a b _ _ ha hb =>
    intro z hz
    rw [moebiusOn_mul a b hz, ha _ (im_moebiusOn_pos b hz), hb z hz]
  | inv a _ ha =>
    intro z hz
    have hw : 0 < (moebiusOn a⁻¹ z).im := im_moebiusOn_pos a⁻¹ hz
    have h1 := ha _ hw
    rw [← moebiusOn_mul a a⁻¹ hz, mul_inv_cancel, moebiusOn_one] at h1
    exact h1.symm

/-- `λ` is differentiable on `ℍ` (upgrades `continuousAt_modularLambdaFn`; from
Mathlib's `hasFDerivAt_jacobiTheta₂`). -/
theorem differentiableAt_modularLambdaFn {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ modularLambdaFn τ := by
  have h3 : DifferentiableAt ℂ theta3 τ := differentiableAt_jacobiTheta₂_snd 0 hτ
  have h2 : DifferentiableAt ℂ theta2 τ := by
    have hj : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (τ / 2, τ) :=
      (hasFDerivAt_jacobiTheta₂ (τ / 2) hτ).differentiableAt
    have hpair : DifferentiableAt ℂ (fun σ : ℂ => (σ / 2, σ)) τ :=
      DifferentiableAt.prodMk (differentiableAt_fun_id.div_const 2) differentiableAt_fun_id
    have hcomp : DifferentiableAt ℂ (fun σ : ℂ => jacobiTheta₂ (σ / 2) σ) τ := by
      have h := DifferentiableAt.comp (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2)
        (f := fun σ : ℂ => (σ / 2, σ)) τ hj hpair
      simpa [Function.comp_def] using h
    exact ((Complex.differentiable_exp.differentiableAt).comp τ
      (by fun_prop : DifferentiableAt ℂ (fun σ : ℂ => (Real.pi : ℂ) * Complex.I * σ / 4) τ)
      ).mul hcomp
  have hne : theta3 τ ^ 4 ≠ 0 := pow_ne_zero 4 (AX_theta3_ne_zero ⟨τ, hτ⟩)
  exact (h2.pow 4).div (h3.pow 4) hne

/-- **H4 at rank 1, transcribed**: an atlas of local couplings — analytic, ℍ-valued,
glued on overlaps by the monodromy group (pointwise, weaker than locally-constant
transitions). -/
structure IsSWCouplingAtlas (S : Set ℂ) {ι : Type*} (chart : ι → Set ℂ)
    (τloc : ι → ℂ → ℂ) : Prop where
  chart_open : ∀ i, IsOpen (chart i)
  covers : S ⊆ ⋃ i, chart i
  analytic : ∀ i, AnalyticOnNhd ℂ (τloc i) (chart i)
  im_pos : ∀ i, ∀ u ∈ chart i, 0 < (τloc i u).im
  glue : ∀ i j, ∀ u ∈ chart i ∩ chart j,
    ∃ γ ∈ swMonodromyGroup, τloc i u = moebiusOn γ (τloc j u)

open Classical in
/-- The global modulus observable of an atlas: `λ` of whichever local coupling is
defined there (well-defined by `atlasModulus_eq`; junk off the atlas). -/
noncomputable def atlasModulus {ι : Type*} (chart : ι → Set ℂ) (τloc : ι → ℂ → ℂ) :
    ℂ → ℂ :=
  fun u => if h : ∃ i, u ∈ chart i then modularLambdaFn (τloc h.choose u) else 0

/-- **Descent (single-valuedness)**: on any chart, `atlasModulus` is `λ` of THAT chart's
coupling — chart-independence is exactly λ-invariance under the monodromy group. -/
theorem atlasModulus_eq {S : Set ℂ} {ι : Type*} {chart : ι → Set ℂ} {τloc : ι → ℂ → ℂ}
    (h : IsSWCouplingAtlas S chart τloc) (i : ι) {u : ℂ} (hu : u ∈ chart i) :
    atlasModulus chart τloc u = modularLambdaFn (τloc i u) := by
  classical
  have hex : ∃ j, u ∈ chart j := ⟨i, hu⟩
  rw [atlasModulus]
  rw [dif_pos hex]
  obtain ⟨γ, hγ, hglue⟩ := h.glue hex.choose i u ⟨hex.choose_spec, hu⟩
  rw [hglue, modularLambda_swMonodromyGroup hγ _ (h.im_pos i u hu)]

theorem atlasModulus_differentiableAt {S : Set ℂ} {ι : Type*} {chart : ι → Set ℂ}
    {τloc : ι → ℂ → ℂ} (h : IsSWCouplingAtlas S chart τloc) {u : ℂ} (hu : u ∈ S) :
    DifferentiableAt ℂ (atlasModulus chart τloc) u := by
  obtain ⟨_, ⟨i, rfl⟩, hui⟩ := h.covers hu
  have hev : atlasModulus chart τloc =ᶠ[nhds u] fun w => modularLambdaFn (τloc i w) := by
    filter_upwards [(h.chart_open i).mem_nhds hui] with w hw
    exact atlasModulus_eq h i hw
  exact ((differentiableAt_modularLambdaFn (h.im_pos i u hui)).comp u
    ((h.analytic i u hui).differentiableAt)).congr_of_eventuallyEq hev

theorem atlasModulus_ne_zero {S : Set ℂ} {ι : Type*} {chart : ι → Set ℂ}
    {τloc : ι → ℂ → ℂ} (h : IsSWCouplingAtlas S chart τloc) {u : ℂ} (hu : u ∈ S) :
    atlasModulus chart τloc u ≠ 0 := by
  obtain ⟨_, ⟨i, rfl⟩, hui⟩ := h.covers hu
  rw [atlasModulus_eq h i hui]
  exact modularLambdaFn_ne_zero ⟨τloc i u, h.im_pos i u hui⟩

theorem atlasModulus_ne_one {S : Set ℂ} {ι : Type*} {chart : ι → Set ℂ}
    {τloc : ι → ℂ → ℂ} (h : IsSWCouplingAtlas S chart τloc) {u : ℂ} (hu : u ∈ S) :
    atlasModulus chart τloc u ≠ 1 := by
  obtain ⟨_, ⟨i, rfl⟩, hui⟩ := h.covers hu
  rw [atlasModulus_eq h i hui]
  exact modularLambdaFn_ne_one ⟨τloc i u, h.im_pos i u hui⟩

/-- **The step-B package**: an atlas covering the punctured u-plane satisfies HALF of
`SWModulusData` outright (analyticity, both omitted values); the three cusp limits are
the surviving hypotheses — exactly what steps D and E are for. -/
theorem swModulusData_of_atlas {Λ : ℂ} {ι : Type*} {chart : ι → Set ℂ}
    {τloc : ι → ℂ → ℂ}
    (h : IsSWCouplingAtlas {u : ℂ | u ≠ Λ ^ 2 ∧ u ≠ -Λ ^ 2} chart τloc)
    (hmono : Filter.Tendsto (atlasModulus chart τloc)
      (nhdsWithin (Λ ^ 2) {Λ ^ 2}ᶜ) (nhds 1))
    (hdyon : Filter.Tendsto (fun u => (atlasModulus chart τloc u)⁻¹)
      (nhdsWithin (-Λ ^ 2) {-Λ ^ 2}ᶜ) (nhds 0))
    (hweak : Filter.Tendsto (atlasModulus chart τloc) (Filter.cocompact ℂ) (nhds 0)) :
    SWModulusData Λ (atlasModulus chart τloc) where
  diff u h1 h2 := atlasModulus_differentiableAt h ⟨h1, h2⟩
  ne_zero u h1 h2 := atlasModulus_ne_zero h ⟨h1, h2⟩
  ne_one u h1 h2 := atlasModulus_ne_one h ⟨h1, h2⟩
  monopole := hmono
  dyon := hdyon
  weak := hweak

/-! ## Step D2 / E ingredient: `λ → 0` uniformly at the cusp `i∞`

The limit is along `comap im atTop` — uniform in `Re τ`, which is what the puncture
limits downstairs require. No `θ₂` estimate is needed: on `ℍ`,
`λ = 1 − θ₄⁴/θ₃⁴` (`oneMinusLambda`) and `θ₄(τ) = θ₃(τ+1)` (the proved shift law), so
everything reduces to Mathlib's `norm_jacobiTheta_sub_one_le` at `τ` and `τ+1`. -/

/-- `θ₃ → 1` uniformly as `Im τ → ∞`. -/
theorem tendsto_theta3_comap_im_atTop :
    Filter.Tendsto theta3 (Filter.comap Complex.im Filter.atTop) (nhds 1) := by
  have him : ∀ᶠ τ : ℂ in Filter.comap Complex.im Filter.atTop, 0 < τ.im :=
    Filter.tendsto_comap.eventually (Filter.eventually_gt_atTop 0)
  suffices hsub : Filter.Tendsto (fun τ : ℂ => theta3 τ - 1)
      (Filter.comap Complex.im Filter.atTop) (nhds 0) by
    have := hsub.add_const 1
    simpa using this
  have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-Real.pi * t))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => Real.pi * t) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop Real.pi_pos Filter.tendsto_id
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    simpa [Function.comp_def, neg_mul] using h2
  have hB : Filter.Tendsto
      (fun t : ℝ => 2 / (1 - Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * t))
      Filter.atTop (nhds 0) := by
    have hcont : Filter.Tendsto (fun x : ℝ => 2 / (1 - x) * x) (nhds 0) (nhds 0) := by
      have : ContinuousAt (fun x : ℝ => 2 / (1 - x) * x) 0 := by
        apply ContinuousAt.mul (ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num))
        exact continuousAt_id
      simpa using this.tendsto
    exact hcont.comp hexp
  have hBim : Filter.Tendsto
      (fun τ : ℂ => 2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im))
      (Filter.comap Complex.im Filter.atTop) (nhds 0) := hB.comp Filter.tendsto_comap
  apply squeeze_zero_norm' _ hBim
  filter_upwards [him] with τ hτ
  have h := norm_jacobiTheta_sub_one_le hτ
  have heq : theta3 τ - 1 = jacobiTheta τ - 1 := by
    rw [theta3, ← jacobiTheta_eq_jacobiTheta₂]
  rw [heq]
  exact h

/-- `θ₄ → 1` uniformly as `Im τ → ∞` (via `θ₄(τ) = θ₃(τ+1)`, same imaginary part). -/
theorem tendsto_theta4_comap_im_atTop :
    Filter.Tendsto theta4 (Filter.comap Complex.im Filter.atTop) (nhds 1) := by
  have hshift : Filter.Tendsto (fun τ : ℂ => τ + 1)
      (Filter.comap Complex.im Filter.atTop) (Filter.comap Complex.im Filter.atTop) := by
    rw [Filter.tendsto_comap_iff]
    have : (Complex.im ∘ fun τ : ℂ => τ + 1) = Complex.im := by
      funext τ; simp [Function.comp_def]
    rw [this]
    exact Filter.tendsto_comap
  have h := tendsto_theta3_comap_im_atTop.comp hshift
  refine h.congr fun τ => ?_
  exact theta3_add_one τ

/-- **`λ → 0` uniformly at the cusp `i∞`** (step D2; also the step-E ingredient). This
is the analytic fact behind the weak-coupling clause of `SWModulusData`. -/
theorem tendsto_modularLambdaFn_comap_im_atTop :
    Filter.Tendsto modularLambdaFn (Filter.comap Complex.im Filter.atTop) (nhds 0) := by
  have him : ∀ᶠ τ : ℂ in Filter.comap Complex.im Filter.atTop, 0 < τ.im :=
    Filter.tendsto_comap.eventually (Filter.eventually_gt_atTop 0)
  have h3 := tendsto_theta3_comap_im_atTop
  have h4 := tendsto_theta4_comap_im_atTop
  have h34 : Filter.Tendsto (fun τ => 1 - theta4 τ ^ 4 / theta3 τ ^ 4)
      (Filter.comap Complex.im Filter.atTop) (nhds 0) := by
    have hdiv : Filter.Tendsto (fun τ => theta4 τ ^ 4 / theta3 τ ^ 4)
        (Filter.comap Complex.im Filter.atTop) (nhds 1) := by
      have := ((h4.pow 4).div (h3.pow 4) (by norm_num : (1 : ℂ) ^ 4 ≠ 0))
      simpa using this
    have := Filter.Tendsto.sub (tendsto_const_nhds (x := (1 : ℂ))) hdiv
    simpa using this
  refine h34.congr' ?_
  filter_upwards [him] with τ hτ
  have h := oneMinusLambda ⟨τ, hτ⟩
  have : modularLambdaFn τ = 1 - theta4 τ ^ 4 / theta3 τ ^ 4 := by
    have hcoe : ((⟨τ, hτ⟩ : UpperHalfPlane) : ℂ) = τ := rfl
    rw [hcoe] at h
    linear_combination -h
  exact this.symm

/-! ## Step D1: the cusp dichotomy

`T` is the universal-cover transcription of a local coupling near a puncture (`w` the
cover coordinate, `q = e^{2πiw}` the punctured-disk coordinate): analytic and ℍ-valued
near `i∞`, with the parabolic equivariance `T(w+1) = T(w) + k` — monodromy `Tᵏ`, `k ≥ 1`
(the H3 input; `k = 2` for the SW points in the λ-frame). Untwisting by
`W = exp((2π/k)·i·T)` — 1-periodic and bounded — and descending through Mathlib's
`Function.Periodic.cuspFunction` (Riemann removability), `W` has a LIMIT `α` at `i∞`,
and the dichotomy is `α = 0` or not. No Picard, no maximum modulus.

Physics reading: either `Im T` stays bounded at the puncture (no genuine singularity —
the branch H2's massless state forbids), or `Im T → ∞` uniformly, and then `λ∘T → 0`
by the step-D2 estimate; the finite-cusp values (`J → 1` at the monopole, the pole at
the dyon) follow by composing with the proved S/T frame laws. -/

/-- **The cusp dichotomy**: bounded `Im T`, or `Im T → ∞` uniformly. -/
theorem cusp_dichotomy {k : ℕ} (hk : 1 ≤ k) {T : ℂ → ℂ}
    (hdiff : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ T w)
    (hH : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, 0 < (T w).im)
    (hper : ∀ w : ℂ, T (w + 1) = T w + k) :
    (∃ M : ℝ, ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, (T w).im ≤ M) ∨
      Filter.Tendsto (fun w => (T w).im) (Filter.comap Complex.im Filter.atTop)
        Filter.atTop := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hπ := Real.pi_pos
  set c : ℂ := 2 * (Real.pi : ℂ) / (k : ℂ) * Complex.I with hcdef
  set W : ℂ → ℂ := fun w => Complex.exp (c * T w) with hWdef
  have hWnorm : ∀ w : ℂ, ‖W w‖ = Real.exp (-(2 * Real.pi / k) * (T w).im) := by
    intro w
    rw [hWdef]
    simp only []
    rw [Complex.norm_exp]
    congr 1
    have hc2 : c = ((2 * Real.pi / k : ℝ) : ℂ) * Complex.I := by
      rw [hcdef]; push_cast; ring
    rw [hc2, mul_assoc, Complex.re_ofReal_mul]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  have hWper : Function.Periodic W 1 := by
    intro w
    rw [hWdef]
    simp only []
    rw [hper w, mul_add, Complex.exp_add]
    rw [show c * (k : ℂ) = 2 * (Real.pi : ℂ) * Complex.I by
      rw [hcdef]; field_simp]
    rw [Complex.exp_two_pi_mul_I, mul_one]
  have hWdiff : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop,
      DifferentiableAt ℂ W w := by
    filter_upwards [hdiff] with w hw
    exact (hw.const_mul c).cexp
  have hWbd : Filter.BoundedAtFilter (Filter.comap Complex.im Filter.atTop) W := by
    have : Asymptotics.IsBigO (Filter.comap Complex.im Filter.atTop) W
        (1 : ℂ → ℝ) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [hH] with w hw
      rw [hWnorm w]
      simp only [Pi.one_apply, norm_one, one_mul]
      apply Real.exp_le_one_iff.mpr
      have : (0 : ℝ) < 2 * Real.pi / k := by positivity
      nlinarith
    exact this
  have htend := hWper.tendsto_at_I_inf one_pos hWdiff hWbd
  rcases eq_or_ne (Function.Periodic.cuspFunction 1 W 0) 0 with h0 | h0
  · right
    rw [h0] at htend
    have hnorm : Filter.Tendsto (fun w => ‖W w‖)
        (Filter.comap Complex.im Filter.atTop) (nhds 0) := by
      simpa using htend.norm
    have hlog : Filter.Tendsto (fun w => Real.log ‖W w‖)
        (Filter.comap Complex.im Filter.atTop) Filter.atBot := by
      apply Real.tendsto_log_nhdsGT_zero.comp
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hnorm, Filter.Eventually.of_forall fun w => ?_⟩
      rw [Set.mem_Ioi, hWnorm w]
      exact Real.exp_pos _
    have heq : ∀ w : ℂ, (T w).im = -((k : ℝ) / (2 * Real.pi)) * Real.log ‖W w‖ := by
      intro w
      rw [hWnorm w, Real.log_exp]
      field_simp
    rw [Filter.tendsto_congr heq]
    have hneg : Filter.Tendsto (fun w => -Real.log ‖W w‖)
        (Filter.comap Complex.im Filter.atTop) Filter.atTop :=
      Filter.tendsto_neg_atBot_atTop.comp hlog
    have := Filter.Tendsto.const_mul_atTop
      (by positivity : (0 : ℝ) < (k : ℝ) / (2 * Real.pi)) hneg
    refine this.congr fun w => ?_
    ring
  · left
    have hnormα : Filter.Tendsto (fun w => ‖W w‖)
        (Filter.comap Complex.im Filter.atTop)
        (nhds ‖Function.Periodic.cuspFunction 1 W 0‖) := htend.norm
    have hαpos : 0 < ‖Function.Periodic.cuspFunction 1 W 0‖ := norm_pos_iff.mpr h0
    have hev : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop,
        ‖Function.Periodic.cuspFunction 1 W 0‖ / 2 < ‖W w‖ :=
      hnormα.eventually (eventually_gt_nhds (by linarith))
    refine ⟨(k : ℝ) / (2 * Real.pi)
      * (-Real.log (‖Function.Periodic.cuspFunction 1 W 0‖ / 2)), ?_⟩
    filter_upwards [hev] with w hw
    have h1 : Real.log (‖Function.Periodic.cuspFunction 1 W 0‖ / 2)
        < -(2 * Real.pi / k) * (T w).im := by
      have h2 := Real.log_lt_log (by positivity) hw
      rwa [hWnorm w, Real.log_exp] at h2
    have h3 : (2 * Real.pi / k) * (T w).im
        < -Real.log (‖Function.Periodic.cuspFunction 1 W 0‖ / 2) := by linarith
    calc (T w).im = ((k : ℝ) / (2 * Real.pi)) * ((2 * Real.pi / k) * (T w).im) := by
          field_simp
      _ ≤ (k : ℝ) / (2 * Real.pi)
          * (-Real.log (‖Function.Periodic.cuspFunction 1 W 0‖ / 2)) := by
          exact mul_le_mul_of_nonneg_left h3.le (by positivity)

/-- **The cusp branch delivers the λ-limit**: if the singularity is genuine (`Im T`
unbounded — H2's massless state), then `λ∘T → 0` uniformly, by D2. The finite-cusp
assignments follow by composing with the proved frame laws. -/
theorem cusp_dichotomy_lambda {k : ℕ} (hk : 1 ≤ k) {T : ℂ → ℂ}
    (hdiff : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ T w)
    (hH : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, 0 < (T w).im)
    (hper : ∀ w : ℂ, T (w + 1) = T w + k) :
    (∃ M : ℝ, ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, (T w).im ≤ M) ∨
      Filter.Tendsto (fun w => modularLambdaFn (T w))
        (Filter.comap Complex.im Filter.atTop) (nhds 0) := by
  rcases cusp_dichotomy hk hdiff hH hper with h | h
  · exact Or.inl h
  · right
    have hT : Filter.Tendsto T (Filter.comap Complex.im Filter.atTop)
        (Filter.comap Complex.im Filter.atTop) := by
      rw [Filter.tendsto_comap_iff]
      exact h
    exact tendsto_modularLambdaFn_comap_im_atTop.comp hT

/-! ## The endgame: `SWModulusData` from an atlas plus three genuine cusp lifts

Transport: the cover maps `w ↦ u₀ + 𝕢(w)` (finite punctures) and `w ↦ 𝕢(w)⁻¹` (weak
coupling) send `I∞ = comap im atTop` ONTO `𝓝[≠] u₀` and `cocompact ℂ` respectively, so
upstairs limits descend. `IsGenuineCuspLift` packages the per-puncture physical input:
a universal-cover lift with parabolic equivariance (H3's `Tᵏ`), genuinely singular
(non-extension — H2 at the finite points, qualitative H6 at `∞`). The frame laws fix
the clause shapes: `λ` at `∞` (cusp `i∞`), `1 − λ` at the monopole (the `S`-frame,
cusp `0`), `(λ−1)/λ` at the dyon (cusp `1`). -/

private lemma nhdsNE_le_map_qParam (u₀ : ℂ) :
    nhdsWithin u₀ {u₀}ᶜ ≤ Filter.map (fun w => u₀ + Function.Periodic.qParam 1 w)
      (Filter.comap Complex.im Filter.atTop) := by
  have hπ := Real.pi_pos
  refine Filter.le_map fun s hs => ?_
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.mp hs
  obtain ⟨A, hA⟩ := Filter.mem_atTop_sets.mp ht
  have hsub : {u : ℂ | u ≠ u₀ ∧ dist u u₀ < Real.exp (-2 * Real.pi * A)}
      ⊆ (fun w => u₀ + Function.Periodic.qParam 1 w) '' s := by
    rintro u ⟨hne, hdist⟩
    have hq0 : u - u₀ ≠ 0 := sub_ne_zero.mpr hne
    refine ⟨Function.Periodic.invQParam 1 (u - u₀), hts ?_, ?_⟩
    · apply hA
      rw [ge_iff_le, Function.Periodic.im_invQParam]
      have hlog : Real.log ‖u - u₀‖ < -2 * Real.pi * A := by
        have h1 : ‖u - u₀‖ < Real.exp (-2 * Real.pi * A) := by
          rwa [← dist_eq_norm]
        have h2 := Real.log_lt_log (norm_pos_iff.mpr hq0) h1
        rwa [Real.log_exp] at h2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
      nlinarith
    · show u₀ + Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 (u - u₀)) = u
      rw [Function.Periodic.qParam_right_inv one_ne_zero hq0]
      ring
  refine Filter.mem_of_superset ?_ hsub
  rw [Metric.mem_nhdsWithin_iff]
  refine ⟨Real.exp (-2 * Real.pi * A), Real.exp_pos _, ?_⟩
  rintro u ⟨hball, hne⟩
  exact ⟨hne, Metric.mem_ball.mp hball⟩

private lemma cocompact_le_map_inv_qParam :
    Filter.cocompact ℂ ≤ Filter.map (fun w => (Function.Periodic.qParam 1 w)⁻¹)
      (Filter.comap Complex.im Filter.atTop) := by
  have hπ := Real.pi_pos
  refine Filter.le_map fun s hs => ?_
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.mp hs
  obtain ⟨A, hA⟩ := Filter.mem_atTop_sets.mp ht
  rw [Filter.mem_cocompact]
  refine ⟨Metric.closedBall 0 (Real.exp (2 * Real.pi * A)),
    isCompact_closedBall _ _, ?_⟩
  intro u hu
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hu
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact absurd hu (not_lt.mpr (Real.exp_pos _).le)
  refine ⟨Function.Periodic.invQParam 1 u⁻¹, hts ?_, ?_⟩
  · apply hA
    rw [ge_iff_le, Function.Periodic.im_invQParam]
    have hlog : Real.log ‖u⁻¹‖ < -2 * Real.pi * A := by
      rw [norm_inv, Real.log_inv]
      have h1 : Real.exp (2 * Real.pi * A) < ‖u‖ := hu
      have h2 := Real.log_lt_log (Real.exp_pos _) h1
      rw [Real.log_exp] at h2
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
    nlinarith
  · show (Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 u⁻¹))⁻¹ = u
    rw [Function.Periodic.qParam_right_inv one_ne_zero (inv_ne_zero hu0), inv_inv]

/-- **The per-puncture physical input**: a universal-cover lift of the local coupling,
analytic and ℍ-valued near the puncture, with parabolic equivariance `T(w+1) = T(w)+k`
(H3's monodromy `Tᵏ`), and genuinely singular — `Im T` unbounded, the non-extension
clause that H2 (massless BPS state) supplies at the finite punctures and qualitative
H6 (asymptotic freedom) supplies at `∞`. -/
structure IsGenuineCuspLift (k : ℕ) (T : ℂ → ℂ) : Prop where
  one_le : 1 ≤ k
  diff : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ T w
  im_pos : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, 0 < (T w).im
  equivariant : ∀ w : ℂ, T (w + 1) = T w + k
  genuine : ¬ ∃ M : ℝ, ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, (T w).im ≤ M

/-- A genuine cusp lift runs to the standard cusp: `λ∘T → 0` (dichotomy + D2). -/
theorem IsGenuineCuspLift.lambda_tendsto {k : ℕ} {T : ℂ → ℂ}
    (h : IsGenuineCuspLift k T) :
    Filter.Tendsto (fun w => modularLambdaFn (T w))
      (Filter.comap Complex.im Filter.atTop) (nhds 0) := by
  rcases cusp_dichotomy_lambda h.one_le h.diff h.im_pos h.equivariant with hb | ht
  · exact absurd hb h.genuine
  · exact ht

/-- **THE ENDGAME**: an H4-style atlas covering the punctured u-plane, together with a
genuine cusp lift at each of the three punctures in its H2-dictated frame (`λ` at `∞`,
`1 − λ` at the monopole, `(λ−1)/λ` at the dyon), satisfies ALL of `SWModulusData`.
Combined with `swModulusData_eq_crossRatio` and `sw_su2_unique_of_modulusData`, this
completes the chain: **H2+H3+H4 (+qualitative H6) data ⟹ cusp data ⟹ the developing
formula ⟹ uniqueness up to `Γ(2)`** — every arrow a theorem. -/
theorem swModulusData_of_atlas_and_lifts {Λ : ℂ} {ι : Type*} {chart : ι → Set ℂ}
    {τloc : ι → ℂ → ℂ}
    (h : IsSWCouplingAtlas {u : ℂ | u ≠ Λ ^ 2 ∧ u ≠ -Λ ^ 2} chart τloc)
    {kw km kd : ℕ} {Tw Tm Td : ℂ → ℂ}
    (hTw : IsGenuineCuspLift kw Tw) (hTm : IsGenuineCuspLift km Tm)
    (hTd : IsGenuineCuspLift kd Td)
    (hJw : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop,
      atlasModulus chart τloc ((Function.Periodic.qParam 1 w)⁻¹)
        = modularLambdaFn (Tw w))
    (hJm : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop,
      atlasModulus chart τloc (Λ ^ 2 + Function.Periodic.qParam 1 w)
        = 1 - modularLambdaFn (Tm w))
    (hJd : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop,
      atlasModulus chart τloc (-Λ ^ 2 + Function.Periodic.qParam 1 w)
        = (modularLambdaFn (Td w) - 1) / modularLambdaFn (Td w)) :
    SWModulusData Λ (atlasModulus chart τloc) := by
  apply swModulusData_of_atlas h
  · -- monopole: J → 1
    have h1 : Filter.Tendsto (fun w : ℂ => 1 - modularLambdaFn (Tm w))
        (Filter.comap Complex.im Filter.atTop) (nhds 1) := by
      have := (tendsto_const_nhds (x := (1:ℂ))).sub hTm.lambda_tendsto
      simpa using this
    have hup := h1.congr' (hJm.mono fun w hw => hw.symm)
    have h2 : Filter.Tendsto (atlasModulus chart τloc)
        (Filter.map (fun w : ℂ => Λ ^ 2 + Function.Periodic.qParam 1 w)
          (Filter.comap Complex.im Filter.atTop)) (nhds 1) := by
      rw [Filter.tendsto_map'_iff]
      exact hup
    exact h2.mono_left (nhdsNE_le_map_qParam (Λ ^ 2))
  · -- dyon: J⁻¹ → 0
    have hev : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop,
        modularLambdaFn (Td w) / (modularLambdaFn (Td w) - 1)
          = (atlasModulus chart τloc (-Λ ^ 2 + Function.Periodic.qParam 1 w))⁻¹ := by
      filter_upwards [hJd] with w hw
      rw [hw, inv_div]
    have h1 : Filter.Tendsto
        (fun w : ℂ => modularLambdaFn (Td w) / (modularLambdaFn (Td w) - 1))
        (Filter.comap Complex.im Filter.atTop) (nhds 0) := by
      have := hTd.lambda_tendsto.div (hTd.lambda_tendsto.sub_const 1)
        (by norm_num : (0 : ℂ) - 1 ≠ 0)
      simpa using this
    have hup := h1.congr' hev
    have h2 : Filter.Tendsto (fun u : ℂ => (atlasModulus chart τloc u)⁻¹)
        (Filter.map (fun w : ℂ => -Λ ^ 2 + Function.Periodic.qParam 1 w)
          (Filter.comap Complex.im Filter.atTop)) (nhds 0) := by
      rw [Filter.tendsto_map'_iff]
      exact hup
    exact h2.mono_left (nhdsNE_le_map_qParam (-Λ ^ 2))
  · -- weak coupling: J → 0
    have hup := hTw.lambda_tendsto.congr' (hJw.mono fun w hw => hw.symm)
    have h2 : Filter.Tendsto (atlasModulus chart τloc)
        (Filter.map (fun w : ℂ => (Function.Periodic.qParam 1 w)⁻¹)
          (Filter.comap Complex.im Filter.atTop)) (nhds 0) := by
      rw [Filter.tendsto_map'_iff]
      exact hup
    exact h2.mono_left cocompact_le_map_inv_qParam

/-- **Uniqueness on the whole Coulomb branch** — the chart bookkeeping discharged. On the
maximal domain `ℂ∖{±Λ²}` the (chart) hypotheses of the uniqueness theorem are supplied by
proved facts: the complement of a finite set in `ℂ` is open, path-connected (rank 2 over
`ℝ`), and nonempty. The assumed content is exactly the H1 shadows and the modulus data. -/
theorem sw_su2_unique_coulomb {Λ : ℂ} (hΛ : Λ ≠ 0) {J : ℂ → ℂ}
    (hJ : SWModulusData Λ J) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f ({Λ ^ 2, -Λ ^ 2} : Set ℂ)ᶜ)
    (hfH : ∀ u ∈ ({Λ ^ 2, -Λ ^ 2} : Set ℂ)ᶜ, 0 < (f u).im)
    (hg : AnalyticOnNhd ℂ g ({Λ ^ 2, -Λ ^ 2} : Set ℂ)ᶜ)
    (hgH : ∀ u ∈ ({Λ ^ 2, -Λ ^ 2} : Set ℂ)ᶜ, 0 < (g u).im)
    (hdevf : ∀ u ∈ ({Λ ^ 2, -Λ ^ 2} : Set ℂ)ᶜ, modularLambdaFn (f u) = J u)
    (hdevg : ∀ u ∈ ({Λ ^ 2, -Λ ^ 2} : Set ℂ)ᶜ, modularLambdaFn (g u) = J u) :
    ∃ γ ∈ Gamma2, Set.EqOn f (fun u => moebiusOn γ (g u))
      ({Λ ^ 2, -Λ ^ 2} : Set ℂ)ᶜ := by
  have hfin : ({Λ ^ 2, -Λ ^ 2} : Set ℂ).Finite := (Set.finite_singleton _).insert _
  have hconn : IsConnected (({Λ ^ 2, -Λ ^ 2} : Set ℂ)ᶜ) :=
    Set.Countable.isConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) hfin.countable
  obtain ⟨u₀, hu₀⟩ := hconn.nonempty
  exact sw_su2_unique_of_modulusData hΛ hJ hfin.isClosed.isOpen_compl
    hconn.isPreconnected hu₀
    (fun u hu => by simpa [not_or] using hu) hf hfH hg hgH hdevf hdevg

end SU2
end SeibergWitten.Physics
