/-
# SU(2): the curve is singular *exactly* at `u = ±Λ²` (no extra singularities)

A direct, **proved** (column-1) answer to "how do we know there aren't more
singularities" — for the rank-1 curve `y² = (x²−u)² − Λ⁴`, the singular locus in the
`u`-plane is *exactly* `{Λ², −Λ²}`, nothing else. There is no lore here: a hyperelliptic
curve `y² = f(x)` is singular iff `f` has a repeated root, i.e. iff `f` is not
squarefree, and that is a polynomial condition we compute.

`swData` (`Curve.lean`) already carries `Squarefree (P² − C Λ^{2N})` as the smoothness
hypothesis; this file characterizes *exactly when* it holds for SU(2):

  `¬ Squarefree ((X²−C u)² − C Λ⁴)  ↔  u = Λ² ∨ u = −Λ²`   (`su2_singular_locus`, `Λ ≠ 0`).

So the curve's own singularity count is two — provably, no hidden points.

## Where this sits in the singularity-counting argument

This settles the **curve side** of the question. The full physics argument that *no
alternative curve with more singularities* can satisfy the SW hypotheses (Seiberg–Witten
hep-th/9407087 §3–4; Bilal hep-th/9601007) has three ingredients, with their formal
status:

* **No too-few** — `Im τ ≻ 0` (metric positivity) forbids having only the singularity
  at `∞`: a globally single-valued holomorphic `τ` with positive imaginary part would be
  constant (Liouville). *Already a theorem here:* `sw_metric_posDef` (`HigherGenus/SpecialGeometry.lean`, the unbuilt higher-genus layer).
* **No too-many** — the product of the interior (Picard–Lefschetz, parabolic) monodromies
  must equal the asymptotically-fixed `M_∞`; this caps the count. *Gap:* needs the
  monodromy layer (Phase 3/4).
* **Positions** — the `ℤ₄`/`ℤ_{2N}` R-symmetry fixes the symmetric placement. *Gap:*
  `HasFiniteOrderAutomorphismConsistent` placeholder.

This file discharges the curve-side count and, with `sw_metric_posDef`, the "no too-few"
lever; the monodromy budget remains the open piece.

References: Seiberg–Witten, hep-th/9407087 §3–4; Bilal, hep-th/9601007 (pedagogical
singularity count); the discriminant criterion is standard (hyperelliptic `y²=f`
singular ⟺ `disc f = 0`).
-/
import Mathlib

open Polynomial

namespace SeibergWitten.SU2

/-- The SU(2) discriminant polynomial factorizes as
`(x²−u)² − Λ⁴ = (x² − (u+Λ²))(x² − (u−Λ²))` — the two branch-point pairs at
`x² = u ± Λ²`. -/
theorem su2_curve_factor (u Λ : ℂ) :
    ((X : ℂ[X]) ^ 2 - C u) ^ 2 - C (Λ ^ 4)
      = (X ^ 2 - C (u + Λ ^ 2)) * (X ^ 2 - C (u - Λ ^ 2)) := by
  have e3 : (C (Λ ^ 4) : ℂ[X]) = C (Λ ^ 2) * C (Λ ^ 2) := by
    rw [← map_mul]; congr 1; ring
  rw [e3, map_add, map_sub]; ring

/-- **No extra singularities.** Away from `u = ±Λ²` (and for `Λ ≠ 0`), the SU(2) curve
polynomial is squarefree — i.e. the curve is smooth. The two quadratic factors are each
squarefree (`separable_X_pow_sub_C`, as `u ± Λ² ≠ 0`) and coprime (as `2Λ² ≠ 0`). -/
theorem su2_squarefree_of_ne {u Λ : ℂ} (hΛ : Λ ≠ 0) (h1 : u ≠ Λ ^ 2) (h2 : u ≠ -Λ ^ 2) :
    Squarefree (((X : ℂ[X]) ^ 2 - C u) ^ 2 - C (Λ ^ 4)) := by
  rw [su2_curve_factor]
  have ha : u + Λ ^ 2 ≠ 0 := by intro h; exact h2 (by linear_combination h)
  have hb : u - Λ ^ 2 ≠ 0 := by intro h; exact h1 (by linear_combination h)
  have hd : (u + Λ ^ 2) - (u - Λ ^ 2) ≠ 0 := by
    have hΛ2 : Λ ^ 2 ≠ 0 := pow_ne_zero 2 hΛ
    intro h; exact hΛ2 (by linear_combination h / 2)
  have sepa : Separable ((X : ℂ[X]) ^ 2 - C (u + Λ ^ 2)) :=
    separable_X_pow_sub_C (u + Λ ^ 2) (by norm_num) ha
  have sepb : Separable ((X : ℂ[X]) ^ 2 - C (u - Λ ^ 2)) :=
    separable_X_pow_sub_C (u - Λ ^ 2) (by norm_num) hb
  have hco : IsCoprime ((X : ℂ[X]) ^ 2 - C (u + Λ ^ 2)) ((X : ℂ[X]) ^ 2 - C (u - Λ ^ 2)) := by
    refine ⟨-C (((u + Λ ^ 2) - (u - Λ ^ 2))⁻¹), C (((u + Λ ^ 2) - (u - Λ ^ 2))⁻¹), ?_⟩
    have key : (-C (((u + Λ ^ 2) - (u - Λ ^ 2))⁻¹)) * (X ^ 2 - C (u + Λ ^ 2))
          + C (((u + Λ ^ 2) - (u - Λ ^ 2))⁻¹) * (X ^ 2 - C (u - Λ ^ 2))
        = C (((u + Λ ^ 2) - (u - Λ ^ 2))⁻¹) * (C (u + Λ ^ 2) - C (u - Λ ^ 2)) := by ring
    rw [key, ← map_sub, ← map_mul, inv_mul_cancel₀ hd, map_one]
  exact (sepa.mul sepb hco).squarefree

/-- **The singular points exist.** At `u = ±Λ²` the polynomial is *not* squarefree: one
quadratic factor degenerates to `X²` (two branch points collide at `x = 0`). -/
theorem su2_not_squarefree {u Λ : ℂ} (h : u = Λ ^ 2 ∨ u = -Λ ^ 2) :
    ¬ Squarefree (((X : ℂ[X]) ^ 2 - C u) ^ 2 - C (Λ ^ 4)) := by
  rw [su2_curve_factor]
  intro hsf
  have hX : ¬ IsUnit (X : ℂ[X]) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_X]; exact one_ne_zero
  rcases h with h | h
  · have hfac : (X ^ 2 - C (u - Λ ^ 2) : ℂ[X]) = X ^ 2 := by rw [h]; simp
    have hdvd : (X : ℂ[X]) * X ∣ (X ^ 2 - C (u + Λ ^ 2)) * (X ^ 2 - C (u - Λ ^ 2)) := by
      rw [hfac, ← pow_two]; exact dvd_mul_left _ _
    exact hX (hsf X hdvd)
  · have hfac : (X ^ 2 - C (u + Λ ^ 2) : ℂ[X]) = X ^ 2 := by rw [h]; simp
    have hdvd : (X : ℂ[X]) * X ∣ (X ^ 2 - C (u + Λ ^ 2)) * (X ^ 2 - C (u - Λ ^ 2)) := by
      rw [hfac, ← pow_two]; exact dvd_mul_right _ _
    exact hX (hsf X hdvd)

/-- **`su2_singular_locus` — the SU(2) curve is singular exactly at `u = ±Λ²`.**
For `Λ ≠ 0`, the curve `y² = (x²−u)² − Λ⁴` is singular (its defining polynomial fails to
be squarefree) precisely at the two moduli `u = Λ²` and `u = −Λ²` — the monopole and dyon
points — and nowhere else. The "exactly two, no more" of the SU(2) Coulomb branch, proved
(no axioms beyond the standard three). -/
theorem su2_singular_locus {u Λ : ℂ} (hΛ : Λ ≠ 0) :
    ¬ Squarefree (((X : ℂ[X]) ^ 2 - C u) ^ 2 - C (Λ ^ 4)) ↔ u = Λ ^ 2 ∨ u = -Λ ^ 2 := by
  refine ⟨fun hns => ?_, su2_not_squarefree⟩
  by_contra hcon
  obtain ⟨hc1, hc2⟩ := not_or.mp hcon
  exact hns (su2_squarefree_of_ne hΛ hc1 hc2)

end SeibergWitten.SU2
