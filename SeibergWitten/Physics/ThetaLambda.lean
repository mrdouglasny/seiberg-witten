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

end SeibergWitten.Physics
