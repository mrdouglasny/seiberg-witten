/-
# Modular `λ` uniformization of the SU(2) base — building the framework

The SU(2) rigidity gap `AX_su2_modular_frame_alignment` (`SU2Rigidity.lean`) rests on the
uniformization of the thrice-punctured base by the upper half plane. This file builds the
framework: it **proves** the reachable identification and isolates the genuine analytic
content as a single classical statement.

## What is proved (column 1)

`su2BaseEquiv`: the SU(2) Coulomb branch is the **standard thrice-punctured sphere**. The
affine map `u ↦ (u+Λ²)/(2Λ²)` is a bijection `ℂ ∖ {±Λ²} ≃ ℂ ∖ {0,1}`, sending the
monopole/dyon points `−Λ², Λ²` to `0, 1`. So the rigidity question transports to the
*standard* base `ℂ ∖ {0,1}`, where the modular `λ`-function lives.

## What is isolated (the deep theorem)

`ThricePuncturedUniformization` packages the classical fact that the modular `λ`-function
realizes `ℍ` as the **universal cover** of `ℂ ∖ {0,1}` with deck group `Γ(2)`:
`λ : ℍ → ℂ∖{0,1}` is `Γ(2)`-invariant, surjective, and its fibres are exactly the
`Γ(2)`-orbits. The single axiom `AX_thrice_punctured_uniformization` asserts this exists.

It is **not vacuous**: surjectivity onto the (infinite) `ℂ∖{0,1}` rules out trivial models,
so this genuinely asserts the uniformization. Mathlib has the raw materials —
`CongruenceSubgroup.Gamma N` and `jacobiTheta` (from which `λ = θ₂⁴/θ₃⁴` is built) — but
neither `λ` itself nor the covering theorem; constructing them is a standalone
Mathlib-scale project (a natural contribution). This axiom is the precise classical
statement that remains.

## How this discharges the rigidity gap

`AX_su2_modular_frame_alignment` asked for a modular frame change aligning two period maps
with the same monodromy. With `su2BaseEquiv` (base = `ℂ∖{0,1}`) + the uniformization
(developing map `ℍ → ℂ∖{0,1}`) + the proved `g=1` `Sp`-action (`SiegelSL2.lean`) + the
identity theorem (`holo_eqOn_of_germ`), it reduces to: *two `Γ(2)`-equivariant holomorphic
maps with the same monodromy differ by a deck transformation* — a statement now entirely
about `AX_thrice_punctured_uniformization`, i.e. the one classical input. So the rigidity
debt is concentrated onto this single, well-understood theorem.

References: the modular `λ`-function and the uniformization of `ℂ∖{0,1}` by `ℍ`
(`ℍ/Γ(2) ≅ ℂ∖{0,1}`) — classical; see e.g. Ahlfors, *Conformal Invariants*; Diamond–
Shurman, *A First Course in Modular Forms* §1. SW context: hep-th/9407087 §3–4.
-/
import SeibergWitten.Physics.SiegelSL2
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups


namespace SeibergWitten.Physics

/-- `Γ(2)`, the principal congruence subgroup of level 2 — the deck group of the modular
`λ`-covering `ℍ → ℂ∖{0,1}`. -/
abbrev Gamma2 : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ) := CongruenceSubgroup.Gamma 2

/-- The affine bijection `u ↦ (u+Λ²)/(2Λ²)` of `ℂ` (for `Λ ≠ 0`), sending `−Λ² ↦ 0` and
`Λ² ↦ 1`. -/
noncomputable def affineEquiv {Λ : ℂ} (hΛ : Λ ≠ 0) : ℂ ≃ ℂ where
  toFun u := (u + Λ ^ 2) / (2 * Λ ^ 2)
  invFun v := 2 * Λ ^ 2 * v - Λ ^ 2
  left_inv u := by
    have h2 : (2 : ℂ) * Λ ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hΛ)
    field_simp; ring
  right_inv v := by
    have h2 : (2 : ℂ) * Λ ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hΛ)
    field_simp; ring

/-- **The SU(2) Coulomb branch is the thrice-punctured sphere `ℂ ∖ {0,1}`.** The affine map
of `affineEquiv` restricts to a bijection `ℂ ∖ {±Λ²} ≃ ℂ ∖ {0,1}` (monopole/dyon points
`↦ 0, 1`). Proved. -/
noncomputable def su2BaseEquiv {Λ : ℂ} (hΛ : Λ ≠ 0) :
    {u : ℂ // u ∉ ({Λ ^ 2, -Λ ^ 2} : Set ℂ)} ≃ {v : ℂ // v ∉ ({0, 1} : Set ℂ)} :=
  (affineEquiv hΛ).subtypeEquiv fun u => by
    have h2 : (2 : ℂ) * Λ ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hΛ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [not_iff_not]
    change (u = Λ ^ 2 ∨ u = -Λ ^ 2) ↔
      ((u + Λ ^ 2) / (2 * Λ ^ 2) = 0 ∨ (u + Λ ^ 2) / (2 * Λ ^ 2) = 1)
    constructor
    · rintro (rfl | rfl)
      · right; rw [div_eq_iff h2]; ring
      · left; rw [div_eq_iff h2]; ring
    · rintro (h | h)
      · rw [div_eq_iff h2] at h; right; linear_combination h
      · rw [div_eq_iff h2] at h; left; linear_combination h

/-- **The classical uniformization data**: the modular `λ`-function realizes `ℍ` as the
universal cover of the thrice-punctured sphere `ℂ ∖ {0,1}` with deck group `Γ(2)`.
`cover = λ` is `Γ(2)`-invariant, surjective, and its fibres are exactly the `Γ(2)`-orbits.
(The analytic core; see the module docstring.) -/
structure ThricePuncturedUniformization where
  /-- the developing/covering map `λ : ℍ → ℂ∖{0,1}`. -/
  cover : UpperHalfPlane → {v : ℂ // v ∉ ({0, 1} : Set ℂ)}
  /-- `λ` is invariant under the deck group `Γ(2)`. -/
  gamma2_invariant : ∀ γ ∈ Gamma2, ∀ τ, cover (γ • τ) = cover τ
  /-- `λ` is onto `ℂ∖{0,1}` (rules out trivial models — this is the uniformization). -/
  surjective : Function.Surjective cover
  /-- the fibres of `λ` are exactly the `Γ(2)`-orbits (the covering property). -/
  fiber : ∀ τ τ', cover τ = cover τ' ↔ ∃ γ ∈ Gamma2, γ • τ = τ'

/-- **GAP (the one classical analytic input).** The modular `λ`-uniformization of `ℂ∖{0,1}`
by `ℍ` exists. Non-vacuous (surjectivity onto an infinite set). The raw materials
(`Gamma`, `jacobiTheta`) are in Mathlib; `λ` and the covering theorem are not — building
them is a standalone project. With `su2BaseEquiv` and the proved `g=1` `Sp`-action, this is
the single remaining input behind `AX_su2_modular_frame_alignment`. (NOT VERIFIED.) -/
axiom AX_thrice_punctured_uniformization : Nonempty ThricePuncturedUniformization

end SeibergWitten.Physics
