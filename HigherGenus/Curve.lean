/-
# The Seiberg–Witten curve of N=2 SU(N) super Yang–Mills (Phase 0)

The low-energy solution of pure N=2 SU(N) SYM (Seiberg–Witten for SU(2);
Klemm–Lerche–Yankielowicz–Theisen and Argyres–Faraggi for SU(N)) is encoded by the
hyperelliptic curve

  `y² = P_N(x)² − Λ^{2N}`,

where `P_N(x) = det(x − Φ) = x^N − u₂ x^{N−2} − … − u_N` is the (monic, degree-`N`)
characteristic polynomial of the adjoint scalar and the `uₖ` are the Coulomb-branch
moduli. Generic moduli give a smooth curve, i.e. `P_N² − Λ^{2N}` squarefree.

This file (Phase 0) realizes that curve as an instance of `jacobian-challenge`'s
hyperelliptic family and proves its **genus is `N − 1`** — the rank of the gauge
group — by instantiating `genus_HyperellipticEven_eq`. Later phases add the period
matrix / special geometry (`τ = τᵀ`, `Im τ ≻ 0`), the special coordinates, and the
prepotential.

References: Seiberg–Witten, *Nucl. Phys.* B426 (1994); Klemm–Lerche–Yankielowicz–
Theisen, *Phys. Lett.* B344 (1995); Argyres–Faraggi, *Phys. Rev. Lett.* 74 (1995);
Lerche, *Introduction to Seiberg–Witten theory*, hep-th/9611190.
-/
import Jacobians.Extensions.HyperellipticEven

open Polynomial
open Jacobians.ProjectiveCurve

namespace SeibergWitten

/-- Seiberg–Witten curve data for pure N=2 SU(N) SYM: the hyperelliptic curve
`y² = P(x)² − Λ^{2N}` with `P` the degree-`N` characteristic polynomial of the
adjoint scalar. `hsf` is the smoothness (squarefree) condition selecting the regular
locus of the Coulomb branch. -/
noncomputable def swData {N : ℕ} (P : Polynomial ℂ) (Λ : ℂ)
    (hPdeg : P.natDegree = N) (hN : 2 ≤ N)
    (hsf : Squarefree (P ^ 2 - C (Λ ^ (2 * N)))) : HyperellipticData where
  f := P ^ 2 - C (Λ ^ (2 * N))
  h_squarefree := hsf
  h_degree := by
    have h : (P ^ 2 - C (Λ ^ (2 * N))).natDegree = 2 * N := by
      rw [natDegree_sub_C, natDegree_pow, hPdeg]
    omega

/-- The SW curve has even degree `2N`. -/
theorem swData_f_natDegree {N : ℕ} (P : Polynomial ℂ) (Λ : ℂ)
    (hPdeg : P.natDegree = N) (hN : 2 ≤ N)
    (hsf : Squarefree (P ^ 2 - C (Λ ^ (2 * N)))) :
    (swData P Λ hPdeg hN hsf).f.natDegree = 2 * N := by
  change (P ^ 2 - C (Λ ^ (2 * N))).natDegree = 2 * N
  rw [natDegree_sub_C, natDegree_pow, hPdeg]

/-- The SW curve degree is even, so the even-atlas `Fact` (needed by the genus/atlas
instances of `HyperellipticEvenProj`) is satisfied for every SW curve. -/
instance instFactEvenSW {N : ℕ} {P : Polynomial ℂ} {Λ : ℂ}
    {hPdeg : P.natDegree = N} {hN : 2 ≤ N}
    {hsf : Squarefree (P ^ 2 - C (Λ ^ (2 * N)))} :
    Fact (¬ Odd (swData P Λ hPdeg hN hsf).f.natDegree) :=
  ⟨by rw [swData_f_natDegree, Nat.odd_iff]; omega⟩

/-- **Phase 0 — the genus of the SU(N) Seiberg–Witten curve is `N − 1`**
(the rank of the gauge group). Instantiates jacobian-challenge's hyperelliptic
genus theorem on the SW family. Axiom-clean (inherits only the standard three). -/
theorem genus_swCurve {N : ℕ} (P : Polynomial ℂ) (Λ : ℂ)
    (hPdeg : P.natDegree = N) (hN : 2 ≤ N)
    (hsf : Squarefree (P ^ 2 - C (Λ ^ (2 * N)))) :
    Jacobians.RiemannSurface.genus
      (HyperellipticEvenProj (swData P Λ hPdeg hN hsf)) = N - 1 := by
  rw [Jacobians.Extensions.HyperellipticEven.genus_HyperellipticEven_eq,
      swData_f_natDegree]
  omega

/-! ## The original Seiberg–Witten case: SU(2), `P(x) = x² − u` -/

/-- For the SU(2) characteristic polynomial `P = x² − u`, `natDegree P = 2`. -/
theorem natDegree_su2P (u : ℂ) : ((X : Polynomial ℂ) ^ 2 - C u).natDegree = 2 := by
  rw [natDegree_sub_C, natDegree_pow, natDegree_X]

/-- **SU(2) (the original Seiberg–Witten curve).** `y² = (x² − u)² − Λ⁴` has
genus `1` — consistent with rank `N − 1 = 1`. -/
theorem genus_swCurve_su2 (u Λ : ℂ)
    (hsf : Squarefree (((X : Polynomial ℂ) ^ 2 - C u) ^ 2 - C (Λ ^ (2 * 2)))) :
    Jacobians.RiemannSurface.genus
      (HyperellipticEvenProj
        (swData ((X : Polynomial ℂ) ^ 2 - C u) Λ (natDegree_su2P u) (by norm_num) hsf)) = 1 := by
  simpa using genus_swCurve ((X : Polynomial ℂ) ^ 2 - C u) Λ (natDegree_su2P u) (by norm_num) hsf

end SeibergWitten
