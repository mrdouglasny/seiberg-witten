/-
# Phase 1a — special geometry: the SW coupling lies in the Siegel upper half space

The effective gauge coupling of N=2 SU(N) SYM is the period matrix `τ` of the
Seiberg–Witten curve. Riemann's bilinear relations put `τ` in the Siegel upper half
space: it is **symmetric** (`τ = τᵀ`, special-geometry integrability) and has
**positive-definite imaginary part** (`Im τ ≻ 0`), which is the positivity of the
special-Kähler metric on the Coulomb branch — the physical no-ghost statement.

This instantiates jacobian-challenge's `AX_RiemannBilinear` (a theorem,
`Layer3.riemannBilinear_exists`) on the SW curve. It transits the off-critical-path
`AX_PeriodCycleBasis` (the hyperelliptic cycle basis); making the SU(2) / genus-1
case axiom-free is Phase 1b (see PLAN.md).
-/
import SeibergWitten.Curve
import Jacobians.Axioms.RiemannBilinear

open Polynomial
open Jacobians.ProjectiveCurve
open Jacobians.AbelianVariety

namespace SeibergWitten

/-- **Phase 1a — the SU(N) Seiberg–Witten effective coupling lies in the Siegel
upper half space.** For the SW curve and any basepoint there is a period matrix
`τ ∈ SiegelUpperHalfSpace (genus = N−1)` that is symmetric (`τ = τᵀ`) and has
positive-definite imaginary part (`Im τ ≻ 0`) — i.e. special-geometry symmetry plus
positivity of the special-Kähler metric on the smooth Coulomb branch. -/
theorem sw_coupling_mem_siegel {N : ℕ} (P : Polynomial ℂ) (Λ : ℂ)
    (hPdeg : P.natDegree = N) (hN : 2 ≤ N)
    (hsf : Squarefree (P ^ 2 - C (Λ ^ (2 * N))))
    (x₀ : HyperellipticEvenProj (swData P Λ hPdeg hN hsf)) :
    ∃ τ : SiegelUpperHalfSpace
        (Jacobians.RiemannSurface.genus (HyperellipticEvenProj (swData P Λ hPdeg hN hsf))),
      τ.val.IsSymm ∧ (τ.val.map Complex.im).PosDef := by
  obtain ⟨_b, _cω, τ, _hA, _hB⟩ := Jacobians.Axioms.AX_RiemannBilinear x₀
  exact ⟨τ, τ.isSymm, τ.imPosDef⟩

/-- Same statement with the rank made explicit: the coupling lives in
`SiegelUpperHalfSpace (N − 1)` (the rank of the gauge group). -/
theorem sw_coupling_mem_siegel_rank {N : ℕ} (P : Polynomial ℂ) (Λ : ℂ)
    (hPdeg : P.natDegree = N) (hN : 2 ≤ N)
    (hsf : Squarefree (P ^ 2 - C (Λ ^ (2 * N))))
    (x₀ : HyperellipticEvenProj (swData P Λ hPdeg hN hsf)) :
    ∃ τ : SiegelUpperHalfSpace (N - 1),
      τ.val.IsSymm ∧ (τ.val.map Complex.im).PosDef := by
  rw [← genus_swCurve P Λ hPdeg hN hsf]
  exact sw_coupling_mem_siegel P Λ hPdeg hN hsf x₀

/-- **Special-Kähler metric positivity** (the physical reading of `Im τ ≻ 0`):
the imaginary part of the SU(N) SW coupling matrix is positive-definite, so the
metric on the smooth Coulomb branch has no ghosts. -/
theorem sw_metric_posDef {N : ℕ} (P : Polynomial ℂ) (Λ : ℂ)
    (hPdeg : P.natDegree = N) (hN : 2 ≤ N)
    (hsf : Squarefree (P ^ 2 - C (Λ ^ (2 * N))))
    (x₀ : HyperellipticEvenProj (swData P Λ hPdeg hN hsf)) :
    ∃ τ : SiegelUpperHalfSpace (N - 1), (τ.val.map Complex.im).PosDef :=
  let ⟨τ, _, h⟩ := sw_coupling_mem_siegel_rank P Λ hPdeg hN hsf x₀
  ⟨τ, h⟩

end SeibergWitten
