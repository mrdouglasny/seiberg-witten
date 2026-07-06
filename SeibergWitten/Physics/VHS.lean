/-
# Variation of Hodge structure over a base — scoping the keystone (weight 1)

The family layer (`Family.lean`) bottoms out in a **polarized integral variation of
Hodge structure (VHS) of weight 1** over the base `B = U = ℂ^r ∖ Δ`. This file scopes
that object *base-agnostically* — it is not SW-specific, and is a natural standalone
contribution (Mathlib has Hodge structures nowhere near this; `jacobian-challenge` has a
single curve's `H₁`, not a variation).

## What a weight-1 VHS over `B` is

For weight 1 (curves / abelian varieties) the abstract Griffiths data collapses to a
remarkably clean package:

* **Local system** `V_ℤ` of rank `2g` over `B` — equivalently the **monodromy
  representation** `ρ : π₁(B) → Sp(2g,ℤ)` preserving the polarization (intersection form).
* **Period map** `p : B̃ → 𝔥_g` to the Siegel upper half space (the period domain
  `Sp(2g,ℤ)\𝔥_g`), holomorphic and `ρ`-equivariant: `p(γ·x) = ρ(γ) · p(x)`.
* **Gauss–Manin connection** — the flat connection with `V_ℂ` as flat sections; its
  horizontal sections solve the Picard–Fuchs ODEs.
* **Hodge–Riemann relations** — *already encoded in the target type*
  `SiegelUpperHalfSpace g` (symmetric, `Im ≻ 0`). **Griffiths transversality** is
  *automatic in weight 1* (`∇F¹ ⊆ F⁰ ⊗ Ω¹ = V ⊗ Ω¹`, vacuous). So the only genuine
  analytic data beyond the discrete `(ρ, p)` is holomorphy + flatness of `p`.

## What is provided here

`WeightOneVHS g B Γ` — the discrete/algebraic core of the structure: a period map
`B → SiegelUpperHalfSpace g` and a monodromy representation `Γ → Sp(2g,ℤ)` (via
`IsSymplectic`). It is the base-agnostic generalization of `SWVariation`; we exhibit the
SW data as an instance (`SWVariation.toVHS`) and reuse the proved `symplecticMonoid`
backbone for it. No new axioms.

## The two concrete build targets (Mathlib status)

1. **The `Sp(2g,ℤ)` action on the Siegel space** `τ ↦ (Aτ+B)(Cτ+D)⁻¹` — needed even to
   *state* `ρ`-equivariance and the period-domain quotient. **Missing from Mathlib for
   `g > 1`**; for `g = 1` it is exactly Mathlib's `SL(2,ℝ)`-action on `UpperHalfPlane`
   (the foothold). Well-definedness (the transform stays symmetric with `Im ≻ 0`) is the
   crux computation. *This is the next reachable target.*
2. **Gauss–Manin / holomorphy of the period map** — the local system from a topological
   fibration `R¹π_*ℤ`, its flat connection, and holomorphy of `p`. The largest piece;
   the Picard–Fuchs (asymptotics) route is `math-commons/picard-lefschetz` (PLAN Phase 3).

References: Griffiths, *Periods of integrals on algebraic manifolds*; Voisin, *Hodge
Theory and Complex Algebraic Geometry* I §10 (VHS, Gauss–Manin); Carlson–Müller-Stach–
Peters, *Period Mappings and Period Domains*. SW context: hep-th/9407087 §3–4.
-/
import SeibergWitten.Physics.Family


namespace SeibergWitten.Physics

variable {g : ℕ}

/-- **The algebraic core of a weight-1 polarized VHS over a base** `B` with fundamental
group `Γ`: a period map to the Siegel space and a symplectic monodromy representation.
Base-agnostic (not SW-specific). The analytic enrichment — holomorphy + flatness
(Gauss–Manin) of the period map and `ρ`-equivariance — is layered on top (see the module
docstring); the Hodge–Riemann relations are already in `SiegelUpperHalfSpace`. -/
structure WeightOneVHS (g : ℕ) (B : Type*) (Γ : Type*) where
  /-- the period map `B → 𝔥_g` (the Hodge filtration `F¹`). -/
  period : B → SiegelUpperHalfSpace g
  /-- the monodromy representation `ρ : Γ → GL(V_ℤ)`. -/
  monodromy : Γ → (CycleLattice g → CycleLattice g)
  /-- `ρ` preserves the polarization (intersection form): it lands in `Sp(2g,ℤ)`. -/
  monodromy_symplectic : ∀ γ, IsSymplectic (monodromy γ)

namespace WeightOneVHS

variable {B Γ : Type*}

/-- The monodromy of a weight-1 VHS lands in `symplecticMonoid g` (`Sp(2g,ℤ)`). -/
theorem monodromy_mem_symplecticMonoid (V : WeightOneVHS g B Γ) (γ : Γ) :
    (V.monodromy γ : Function.End (CycleLattice g)) ∈ symplecticMonoid g :=
  V.monodromy_symplectic γ

end WeightOneVHS

/-- **The SW family is a weight-1 VHS.** The `SWVariation` data (`Family.lean`) forgets to
the base-agnostic VHS over `U = ℂ^r ∖ Δ`: same period map, same symplectic monodromy
representation. This exhibits Seiberg–Witten as an instance of the general object — the
SW-specific content is the *extra* Picard–Lefschetz generator data (`vanishingLoop`,
`picard_lefschetz`), which the bare VHS does not see. -/
def SWVariation.toVHS {r : ℕ} {Δ : Set (Fin r → ℂ)} (V : SWVariation r Δ) :
    WeightOneVHS r {u : Fin r → ℂ // u ∉ Δ} V.Loop where
  period := V.period
  monodromy := V.monodromy
  monodromy_symplectic := V.monodromy_symplectic

end SeibergWitten.Physics
