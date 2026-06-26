/-
# Genus-1 bridge: the SU(2) Seiberg–Witten curve family as `jacobian-challenge` data

Experiment from `audit/PERIOD_LAYER_SCOPING.md`: realize the SU(2) SW elliptic fiber
`y² = (x²−u)² − Λ⁴` as `Jacobians.ProjectiveCurve.HyperellipticData`, over the modulus `u`, and
confirm **genus 1** — measuring how much of the period layer's per-fiber side is reusable from
`jacobian-challenge` (already this project's `Jacobians` dependency).

**Finding (measured here).** The *fiber* is reusable: each smooth `u` (`f` squarefree ⟺
`u ∉ {±Λ²}`) gives a genus-1 `HyperellipticData`, with genus discharged by `jacobian-challenge`'s
own `genus_eq_of_natDegree_eq_two_mul_add_two` — so the SW curve lives in its curve type, and the
single-fiber period machinery (holomorphic forms, period matrix, Riemann bilinear) applies. The
*variation over `u`* — the period **as a function of `u`**, its Picard–Fuchs ODE and Gauss–Manin
`SL(2,ℤ)` monodromy — is **not** in `jacobian-challenge` (it has no curve-in-a-parameter notion);
`swFamily` below is the dependent map, and its period-variation is the genuinely new build the
period layer (`PeriodLayer.rigidity`) needs.
-/
import Mathlib
import Jacobians.ProjectiveCurve.Hyperelliptic.Basic

namespace SeibergWitten.Physics

open Polynomial Jacobians.ProjectiveCurve

/-- The SU(2) SW curve polynomial in the fiber variable `x`: `f_{Λ,u}(x) = (x²−u)² − Λ⁴`
(the curve is `y² = f`). Degree 4, hence genus 1. -/
noncomputable def swQuartic (Λ u : ℂ) : Polynomial ℂ := (X ^ 2 - C u) ^ 2 - C (Λ ^ 4)

@[simp] theorem swQuartic_natDegree (Λ u : ℂ) : (swQuartic Λ u).natDegree = 4 := by
  unfold swQuartic
  compute_degree!

/-- The SW elliptic fiber at a smooth modulus `u` (`f` squarefree ⟺ `u ∉ {±Λ²}`), packaged as
`jacobian-challenge` hyperelliptic data. -/
noncomputable def swEllipticData (Λ u : ℂ) (hsf : Squarefree (swQuartic Λ u)) :
    HyperellipticData where
  f := swQuartic Λ u
  h_squarefree := hsf
  h_degree := by rw [swQuartic_natDegree]; norm_num

/-- **The SW fiber has genus 1** — so its period domain is `Siegel 1 ≅ ℍ` and the duality group
is `SL(2,ℤ)`, matching the rank-1 layer. Proved via `jacobian-challenge`'s genus formula. -/
theorem swEllipticData_genus (Λ u : ℂ) (hsf : Squarefree (swQuartic Λ u)) :
    (swEllipticData Λ u hsf).genus = 1 := by
  apply HyperellipticData.genus_eq_of_natDegree_eq_two_mul_add_two
  show (swQuartic Λ u).natDegree = 2 * 1 + 2
  simp

/-- The SW elliptic **family** over the smooth locus: each modulus `u` with squarefree fiber maps
to its genus-1 hyperelliptic datum. `jacobian-challenge` has no notion of a curve varying in a
parameter, so this dependent map — and, on top of it, the `u`-variation of the periods (the
Picard–Fuchs ODE / Gauss–Manin monodromy) — is the new content the period layer must supply. -/
noncomputable def swFamily (Λ : ℂ) :
    (u : ℂ) → Squarefree (swQuartic Λ u) → HyperellipticData :=
  swEllipticData Λ

end SeibergWitten.Physics
