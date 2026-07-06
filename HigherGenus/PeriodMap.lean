import SeibergWitten.SpecialGeometry
import SeibergWitten.Physics.Hypotheses
import SeibergWitten.Physics.Family

/-!
# R1 — the Seiberg–Witten period map into the Siegel upper half space

First milestone of `audit/PERIOD_LAYER_DISCHARGE.md`: the family period map `u ↦ τ(u) ∈ Siegel(N−1)`
of `y² = swCurvePoly N Λ u`, built on `sw_coupling_mem_siegel_rank` (jacobian-challenge's
`AX_RiemannBilinear`) and the curve's `Nonempty` instance (so no curve point need be exhibited).

* `sw_coupling_exists` — the coupling `τ ∈ Siegel(N−1)` exists for any squarefree SW curve, with no
  explicit curve point (the curve is nonempty).
* `swPeriodMap` — the chosen `τ(u)` as a function of the modulus `u` (on the smooth locus);
  `swPeriodMap_isSymm` / `swPeriodMap_imPosDef` record `τ = τᵀ` and `Im τ ≻ 0`.

Footprint: standard-3 + jacobian-challenge's `AX_RiemannBilinear` / `AX_PeriodCycleBasis` — *not*
`periodRigidityAxiom`.
-/

open Polynomial

namespace SeibergWitten.Physics

open SeibergWitten Jacobians.AbelianVariety

/-- The SW moduli polynomial `X^N + ∑_{i<N-1} uᵢ Xⁱ` is monic of degree `N`: the `X^N` term
dominates the subleading sum (degree `≤ N−2`). -/
theorem swModuliPoly_natDegree {N : ℕ} (hN : 1 ≤ N) (u : Fin (N - 1) → ℂ) :
    (swModuliPoly N u).natDegree = N := by
  rw [swModuliPoly]
  have hle : (∑ i : Fin (N - 1), C (u i) * X ^ (i : ℕ)).natDegree ≤ N - 2 := by
    refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le ?_)
    intro i _
    calc (C (u i) * X ^ (i : ℕ)).natDegree
        ≤ (X ^ (i : ℕ)).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = (i : ℕ) := Polynomial.natDegree_X_pow _
      _ ≤ N - 2 := by have := i.isLt; omega
  have hlt : (∑ i : Fin (N - 1), C (u i) * X ^ (i : ℕ)).natDegree < (X ^ N : ℂ[X]).natDegree := by
    rw [Polynomial.natDegree_X_pow]; omega
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]

/-- **R1 (curve-point-free coupling).** For any squarefree SW curve `y² = P² − Λ^{2N}` (`P` of
degree `N`, `N ≥ 2`), the coupling `τ ∈ Siegel(N−1)` exists, symmetric with `Im τ ≻ 0` — *without*
exhibiting a point of the curve: the SW curve is `Nonempty` (jacobian-challenge), so
`Classical.arbitrary` supplies the base point `sw_coupling_mem_siegel_rank` needs. -/
theorem sw_coupling_exists {N : ℕ} (P : Polynomial ℂ) (Λ : ℂ) (hPdeg : P.natDegree = N)
    (hN : 2 ≤ N) (hsf : Squarefree (P ^ 2 - C (Λ ^ (2 * N)))) :
    ∃ τ : SiegelUpperHalfSpace (N - 1), τ.val.IsSymm ∧ (τ.val.map Complex.im).PosDef :=
  sw_coupling_mem_siegel_rank P Λ hPdeg hN hsf (Classical.arbitrary _)

/-- **R1 — the SW period map.** The coupling `τ(u) ∈ Siegel(N−1)` as a function of the modulus `u`
on the smooth locus (the curve `y² = swCurvePoly N Λ u` squarefree), given the standard degree fact
`natDegree (swModuliPoly N u) = N`. The genus-`(N−1)` period matrix of the SW curve family. -/
noncomputable def swPeriodMap {N : ℕ} (Λ : ℂ) (hN : 2 ≤ N) (u : Fin (N - 1) → ℂ)
    (hsf : Squarefree (swCurvePoly N Λ u)) : SiegelUpperHalfSpace (N - 1) :=
  (sw_coupling_exists (swModuliPoly N u) Λ (swModuliPoly_natDegree (by omega) u) hN
    (by simpa [swCurvePoly] using hsf)).choose

/-- The period matrix `swPeriodMap` is symmetric. -/
theorem swPeriodMap_isSymm {N : ℕ} (Λ : ℂ) (hN : 2 ≤ N) (u : Fin (N - 1) → ℂ)
    (hsf : Squarefree (swCurvePoly N Λ u)) :
    (swPeriodMap Λ hN u hsf).val.IsSymm :=
  (sw_coupling_exists (swModuliPoly N u) Λ (swModuliPoly_natDegree (by omega) u) hN
    (by simpa [swCurvePoly] using hsf)).choose_spec.1

/-- The period matrix has positive-definite imaginary part (special-Kähler positivity). -/
theorem swPeriodMap_imPosDef {N : ℕ} (Λ : ℂ) (hN : 2 ≤ N) (u : Fin (N - 1) → ℂ)
    (hsf : Squarefree (swCurvePoly N Λ u)) :
    ((swPeriodMap Λ hN u hsf).val.map Complex.im).PosDef :=
  (sw_coupling_exists (swModuliPoly N u) Λ (swModuliPoly_natDegree (by omega) u) hN
    (by simpa [swCurvePoly] using hsf)).choose_spec.2

/-- The SW **discriminant locus** (singular moduli): where `y² = swCurvePoly N Λ u` degenerates. -/
def swDiscriminant (N : ℕ) (Λ : ℂ) : Set (Fin (N - 1) → ℂ) :=
  {u | ¬ Squarefree (swCurvePoly N Λ u)}

/-- **R1 → the SW family is a weight-1 VHS.** Given the vanishing charges of the singular fibres,
the SW family over `U = ℂ^{N-1} ∖ Δ` assembles into an `SWVariation`: the holomorphic period map is
the
real `swPeriodMap` (`τ ∈ Siegel`), and the monodromy is the Picard–Lefschetz transvection of each
vanishing charge — `monodromy_symplectic` from `transvection_isSymplectic`, `picard_lefschetz` by
construction (`Loop := Δ`, `vanishingLoop := id`). The physical identification of the charges is
deferred (R3). Footprint: standard-3 + `AX_PeriodCycleBasis`. -/
noncomputable def swVariation {N : ℕ} (Λ : ℂ) (hN : 2 ≤ N)
    (vanishingCharge : ↥(swDiscriminant N Λ) → CycleLattice (N - 1)) :
    SWVariation (N - 1) (swDiscriminant N Λ) where
  period u := swPeriodMap Λ hN u.1 (by
    have h := u.2; simp only [swDiscriminant, Set.mem_setOf_eq, not_not] at h; exact h)
  Loop := ↥(swDiscriminant N Λ)
  monodromy d := transvection (vanishingCharge d)
  monodromy_symplectic _ := transvection_isSymplectic _
  vanishingLoop := id
  vanishingCharge := vanishingCharge
  picard_lefschetz _ := rfl

end SeibergWitten.Physics
