/-
# Chipping the uniformization axiom: the modular `λ` as a concrete theta ratio

`ModularLambda.lean` isolated the SU(2) uniformization as the single abstract axiom
`AX_thrice_punctured_uniformization` (a cover `ℍ → ℂ∖{0,1}` exists). Here we begin
**replacing the abstraction by the concrete function**: we *define* the modular
`λ = θ₂⁴/θ₃⁴` from Mathlib's `jacobiTheta₂`, prove the facts that reuse Mathlib, and break
the remaining content into elementary, individually-classical pieces.

## Defined (concrete, from Mathlib)

The Jacobi theta-nulls as half-period values of `jacobiTheta₂ z τ = ∑ₙ exp(2πinz + πin²τ)`:
`θ₃ = jacobiTheta₂ 0 τ`, `θ₄ = jacobiTheta₂ (1/2) τ`, `θ₂ = exp(πiτ/4)·jacobiTheta₂ (τ/2) τ`,
and `modularLambdaFn = θ₂⁴/θ₃⁴`. These match the standard nulls (so the classical
identities below are *true* of these definitions, not just postulated of an abstract `λ`).

## Proved (standard-3, reusing Mathlib)

* `theta3_eq_jacobiTheta` — `θ₃` is Mathlib's one-variable `jacobiTheta`.
* `theta3_add_two`, `theta4_add_two` — period-2 in `τ` (from `jacobiTheta₂_add_right`).
* `oneMinusLambda` — `1 − λ = θ₄⁴/θ₃⁴` (so `0` and `1` enter symmetrically), derived from
  the two classical facts below.

## What remains — now elementary and explicit (was hidden in the monolith)

* `AX_jacobi_quartic` — `θ₃⁴ = θ₂⁴ + θ₄⁴` (Jacobi's identity). A concrete theta-series
  computation; a bounded target, not analysis.
* `AX_theta3_ne_zero` — `θ₃ ≠ 0` on `ℍ`. A standard non-vanishing lemma.
* The covering/Hauptmodul property of *this* `modularLambdaFn` (Γ(2)-invariance,
  surjectivity onto `ℂ∖{0,1}`, fibres = orbits) — still `AX_thrice_punctured_uniformization`,
  now realized by a concrete function. Mathlib's `jacobiTheta_S_smul` / `_T_sq_smul` are the
  footholds for the eventual `Γ(2)`-invariance proof.

So the one abstract axiom is refined into: a concrete `λ`, two elementary classical theta
facts, and the (still deep) covering. References: Diamond–Shurman §1; Ahlfors,
*Conformal Invariants*; classical Jacobi theta identities.
-/
import SeibergWitten.Physics.ModularLambda
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

open Complex

namespace SeibergWitten.Physics

/-- The `θ₃` null: `θ₃(τ) = ∑ₙ exp(πin²τ) = jacobiTheta₂ 0 τ`. -/
noncomputable def theta3 (τ : ℂ) : ℂ := jacobiTheta₂ 0 τ

/-- The `θ₄` null: `θ₄(τ) = ∑ₙ (−1)ⁿ exp(πin²τ) = jacobiTheta₂ (1/2) τ`. -/
noncomputable def theta4 (τ : ℂ) : ℂ := jacobiTheta₂ (1 / 2) τ

/-- The `θ₂` null: `θ₂(τ) = ∑ₙ exp(πi(n+1/2)²τ) = exp(πiτ/4)·jacobiTheta₂ (τ/2) τ`. -/
noncomputable def theta2 (τ : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ

/-- **The modular lambda function** `λ = θ₂⁴/θ₃⁴`, defined concretely from Mathlib's
`jacobiTheta₂`. The Hauptmodul for `Γ(2)` uniformizing `ℂ∖{0,1}`. -/
noncomputable def modularLambdaFn (τ : ℂ) : ℂ := theta2 τ ^ 4 / theta3 τ ^ 4

/-- `θ₃` is Mathlib's one-variable Jacobi theta function. -/
theorem theta3_eq_jacobiTheta (τ : ℂ) : theta3 τ = jacobiTheta τ := by
  unfold theta3; exact (jacobiTheta_eq_jacobiTheta₂ τ).symm

/-- `θ₃` has period 2 in `τ` (from `jacobiTheta₂_add_right`). -/
theorem theta3_add_two (τ : ℂ) : theta3 (τ + 2) = theta3 τ := by
  unfold theta3; exact jacobiTheta₂_add_right 0 τ

/-- `θ₄` has period 2 in `τ`. -/
theorem theta4_add_two (τ : ℂ) : theta4 (τ + 2) = theta4 τ := by
  unfold theta4; exact jacobiTheta₂_add_right (1 / 2) τ

/-- **Jacobi's quartic identity** `θ₃⁴ = θ₂⁴ + θ₄⁴` (classical; a theta-series computation).
    Reference: Diamond–Shurman §1; classical. (NOT VERIFIED.) -/
axiom AX_jacobi_quartic (τ : ℂ) : theta3 τ ^ 4 = theta2 τ ^ 4 + theta4 τ ^ 4

/-- **`θ₃ ≠ 0` on the upper half plane** (classical non-vanishing). (NOT VERIFIED.) -/
axiom AX_theta3_ne_zero (τ : UpperHalfPlane) : theta3 (τ : ℂ) ≠ 0

/-- `1 − λ = θ₄⁴/θ₃⁴`: the points `0` and `1` of `ℂ∖{0,1}` enter symmetrically
(`λ ↔ θ₂`, `1−λ ↔ θ₄`). Proved from the Jacobi identity and `θ₃ ≠ 0`. -/
theorem oneMinusLambda (τ : UpperHalfPlane) :
    1 - modularLambdaFn (τ : ℂ) = theta4 (τ : ℂ) ^ 4 / theta3 (τ : ℂ) ^ 4 := by
  have h3 : theta3 (τ : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 (AX_theta3_ne_zero τ)
  have hq : theta3 (τ : ℂ) ^ 4 = theta2 (τ : ℂ) ^ 4 + theta4 (τ : ℂ) ^ 4 :=
    AX_jacobi_quartic (τ : ℂ)
  rw [modularLambdaFn, eq_div_iff h3, sub_mul, div_mul_cancel₀ _ h3, one_mul]
  linear_combination hq

/-! ## `T²`-invariance of `λ` (a proved piece of the `Γ(2)`-Hauptmodul property) -/

/-- Normal form for `θ₂⁴`: `θ₂(τ)⁴ = exp(πiτ)·jacobiTheta₂(τ/2,τ)⁴` (the `exp(πiτ/4)`
prefactor becomes `exp(πiτ)` on the fourth power). -/
theorem theta2_pow_four (τ : ℂ) :
    theta2 τ ^ 4 = Complex.exp ((Real.pi : ℂ) * I * τ) * jacobiTheta₂ (τ / 2) τ ^ 4 := by
  unfold theta2
  rw [mul_pow, ← Complex.exp_nat_mul]
  have h : ((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * I * τ / 4) = (Real.pi : ℂ) * I * τ := by
    push_cast; ring
  rw [h]

/-- `θ₂⁴` is invariant under `τ ↦ τ + 2`: the `i = exp(πi/2)` factor from the prefactor is
killed by the fourth power (`i⁴ = 1`), and `jacobiTheta₂` is `2`-periodic in `τ` and
`1`-periodic in `z`. -/
theorem theta2_add_two_pow_four (τ : ℂ) : theta2 (τ + 2) ^ 4 = theta2 τ ^ 4 := by
  have harg : (τ + 2) / 2 = τ / 2 + 1 := by ring
  rw [theta2_pow_four (τ + 2), theta2_pow_four τ, harg, jacobiTheta₂_add_right,
    jacobiTheta₂_add_left]
  rw [show (Real.pi : ℂ) * I * (τ + 2) = (Real.pi : ℂ) * I * τ + 2 * (Real.pi : ℂ) * I from by
    ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **`T²`-invariance of the modular `λ`**: `λ(τ + 2) = λ(τ)`. Since `T² = [[1,2],[0,1]] ∈
Γ(2)`, this is a *proved* instance of the `Γ(2)`-invariance that the uniformization axiom
`AX_thrice_punctured_uniformization` postulates — a genuine dent in that gap. -/
theorem modularLambda_add_two (τ : ℂ) : modularLambdaFn (τ + 2) = modularLambdaFn τ := by
  unfold modularLambdaFn
  rw [theta2_add_two_pow_four, theta3_add_two]

/-! ## S-transformation of `λ`: `λ(-1/τ) = 1 − λ(τ)` -/

/-- **`θ₃` S-transformation** `θ₃(-1/τ) = (-iτ)^{1/2}·θ₃(τ)`, proved from Mathlib's
`jacobiTheta₂_functional_equation` at `z = 0`. -/
theorem theta3_neg_inv (τ : UpperHalfPlane) :
    theta3 (-1 / (τ : ℂ)) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * theta3 (τ : ℂ) := by
  have hτ0 : (τ : ℂ) ≠ 0 := ne_of_apply_ne Complex.im (Complex.zero_im.symm ▸ ne_of_gt τ.2)
  have hA : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ0)
  unfold theta3
  have FE := jacobiTheta₂_functional_equation 0 (τ : ℂ)
  simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Complex.exp_zero, mul_one] at FE
  rw [FE, ← mul_assoc, mul_one_div, div_self hA, one_mul]

/-- **`θ₂` S-transformation** `θ₂(-1/τ) = (-iτ)^{1/2}·θ₄(τ)`, proved from Mathlib's
`jacobiTheta₂_functional_equation` at `z = -1/2` (with `jacobiTheta₂_neg_left`). The
`exp(πiτ/4)` prefactor of `θ₂(-1/τ)` is *exactly* the `exp(-πi z²/τ)` factor the functional
equation produces at `z = -1/2`, so they coincide and the `θ₂↔θ₄` swap drops out. -/
theorem theta2_neg_inv (τ : UpperHalfPlane) :
    theta2 (-1 / (τ : ℂ)) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * theta4 (τ : ℂ) := by
  have hτ0 : (τ : ℂ) ≠ 0 := ne_of_apply_ne Complex.im (Complex.zero_im.symm ▸ ne_of_gt τ.2)
  have hA : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ0)
  have FE := jacobiTheta₂_functional_equation (-(1 / 2)) (τ : ℂ)
  rw [jacobiTheta₂_neg_left] at FE
  unfold theta2 theta4
  rw [show (-1 / (τ : ℂ)) / 2 = -(1 / 2 : ℂ) / (τ : ℂ) from by ring, FE,
    show (Real.pi : ℂ) * I * (-1 / (τ : ℂ)) / 4
        = -(Real.pi : ℂ) * I * (-(1 / 2 : ℂ)) ^ 2 / (τ : ℂ) from by ring,
    ← mul_assoc, ← mul_assoc, mul_one_div, div_self hA, one_mul]

/-- **S-transformation of the modular `λ`**: `λ(-1/τ) = 1 − λ(τ)`. The automorphy factor
`(-iτ)^{1/2}` cancels in the ratio `θ₂⁴/θ₃⁴`, and `θ₂↔θ₄` under `S` turns `λ` into
`θ₄⁴/θ₃⁴ = 1 − λ` (`oneMinusLambda`). Combined with `T²`-invariance
(`modularLambda_add_two`) this gives the full `Γ(2)`-invariance the uniformization axiom
postulates: `Γ(2) = ⟨T², ST²S⁻¹⟩`, and `S` sends `λ ↦ 1−λ`. -/
theorem modularLambda_S (τ : UpperHalfPlane) :
    modularLambdaFn (-1 / (τ : ℂ)) = 1 - modularLambdaFn (τ : ℂ) := by
  have hτ0 : (τ : ℂ) ≠ 0 := ne_of_apply_ne Complex.im (Complex.zero_im.symm ▸ ne_of_gt τ.2)
  have hA : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ0)
  rw [oneMinusLambda]
  unfold modularLambdaFn
  rw [theta2_neg_inv, theta3_neg_inv, mul_pow, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero 4 hA)]

/-- **Invariance of `λ` under the second `Γ(2)` generator** `ST²S⁻¹ = [[1,0],[-2,1]]`,
which sends `τ ↦ -1/(-1/τ + 2)`. Proved purely by chaining the two transformation laws:
`λ(-1/(-1/τ+2)) = 1 − λ(-1/τ+2)` (`S`) `= 1 − λ(-1/τ)` (`T²`) `= 1 − (1−λτ) = λτ` (`S`).
Together with `modularLambda_add_two` (`T²`-invariance) this establishes invariance under
both generators of `Γ(2) = ⟨T², ST²S⁻¹⟩` — i.e. `λ` is a genuine `Γ(2)`-Hauptmodul, the
invariance clause of `AX_thrice_punctured_uniformization` now proved (only surjectivity /
fibres remain). -/
theorem modularLambda_ST2S (τ : UpperHalfPlane) :
    modularLambdaFn (-1 / (-1 / (τ : ℂ) + 2)) = modularLambdaFn (τ : ℂ) := by
  have hρim : 0 < (-1 / (τ : ℂ) + 2).im := by
    rw [show (-1 / (τ : ℂ) + 2) = (-(τ : ℂ))⁻¹ + 2 from by ring, Complex.add_im]
    simpa using τ.im_inv_neg_coe_pos
  have e1 := modularLambda_S ⟨-1 / (τ : ℂ) + 2, hρim⟩
  rw [e1, modularLambda_add_two, modularLambda_S τ]
  ring

end SeibergWitten.Physics
