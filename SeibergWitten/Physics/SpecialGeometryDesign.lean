/-
# DRAFT — a strengthened carrier for special geometry (H1) and masslessness (H2)

**Proposal only.** Not wired into the build and not replacing `Hypotheses.lean`; here to look
at before refactoring. It fixes the vacuity flagged in review:

* the current `SpecialGeometry`/`BecomesMasslessAt` are *opaque* predicates with no body, so H1
  never says `aD = ∂F/∂a, τ = ∂²F/∂a²` and H2 never says the mass vanishes;
* the root cause is that the carrier `SmoothCover` is a structureless `Type`, so one cannot
  even write `∂/∂a` or a limit on it.

Here the periods `a, aD` are **genuine holomorphic functions** on an open chart
`U ⊆ ℂ^r ∖ Δ` of the smooth Coulomb branch (gauge-invariant moduli `u`). That makes both
hypotheses *contentful*:

* **H1** states the prepotential relations `aD = ∂F/∂a`, `τ = ∂²F/∂a²` (`Im τ ≻ 0` is carried
  by the `SiegelUpperHalfSpace` type, and symmetry of `τ` is then automatic — it is a Hessian);
* **H2** *defines* "charge `n` becomes massless at `u₀ ∈ Δ`" as the central charge `Z_n → 0`
  along `𝓝[U] u₀`, and asserts every BPS state is massive at smooth points;
* H2 and H3 can now share the **vanishing charge `n`** (the same `n` that drives the
  Picard–Lefschetz monodromy), and Argyres–Douglas is two mutually-non-local such `n`.

A second, equivalent encoding (prepotential-primitive: make `F` the datum and *derive* `aD`,
`τ`) is sketched in the closing comment.
-/
import SeibergWitten.Physics.Hypotheses
import Mathlib

open Complex Filter Topology Matrix Jacobians.AbelianVariety

namespace SeibergWitten.Physics.Design

variable {r : ℕ}

/-- `∂F/∂xᵢ` at `x`, for a holomorphic `F : ℂ^r → ℂ` (the `i`-th partial of the prepotential). -/
noncomputable def partialDeriv (F : (Fin r → ℂ) → ℂ) (i : Fin r) (x : Fin r → ℂ) : ℂ :=
  fderiv ℂ F x (Pi.single i 1)

/-- `∂²F/∂xᵢ∂xⱼ` at `x`. -/
noncomputable def partialDeriv2 (F : (Fin r → ℂ) → ℂ) (i j : Fin r) (x : Fin r → ℂ) : ℂ :=
  partialDeriv (fun y => partialDeriv F i y) j x

/-- **Strengthened low-energy data** on a chart `U ⊆ ℂ^r ∖ Δ` of the smooth Coulomb branch.
Unlike the opaque skeleton, the special coordinates `a` and their duals `aD` are *genuine
holomorphic functions of the modulus* `u`, and the coupling `τ` lands in the Siegel upper half
space (so `Im τ ≻ 0` — the no-ghost metric — is part of the type). -/
structure SpecialGeometryData (Δ : Set (Fin r → ℂ)) where
  /-- a chart of the smooth Coulomb branch -/
  U : Set (Fin r → ℂ)
  hUopen : IsOpen U
  hUsmooth : U ⊆ Δᶜ
  /-- special coordinates `aᵢ(u)`, holomorphic on `U` -/
  a : (Fin r → ℂ) → (Fin r → ℂ)
  ha : DifferentiableOn ℂ a U
  /-- dual special coordinates `a_{D,i}(u)`, holomorphic on `U` -/
  aD : (Fin r → ℂ) → (Fin r → ℂ)
  haD : DifferentiableOn ℂ aD U
  /-- effective coupling `τ(u) ∈ SiegelUpperHalfSpace r` (symmetric, `Im ≻ 0`) -/
  tau : (Fin r → ℂ) → SiegelUpperHalfSpace r

namespace SpecialGeometryData

variable {Δ : Set (Fin r → ℂ)} (d : SpecialGeometryData Δ)

/-- **Central charge** `Z_n(u) = nₑ · a(u) + n_m · a_D(u)` — now a genuine holomorphic function
of the modulus `u`. Its modulus is `‖Z_n‖`, and the BPS mass is `√2 ‖Z_n‖`. -/
noncomputable def centralCharge (u : Fin r → ℂ) (n : ChargeLattice r) : ℂ :=
  (∑ i, (n.1 i : ℂ) * d.a u i) + (∑ i, (n.2 i : ℂ) * d.aD u i)

/-- **BPS mass** `M_n(u) = √2 ‖Z_n(u)‖`. -/
noncomputable def bpsMass (u : Fin r → ℂ) (n : ChargeLattice r) : ℝ :=
  Real.sqrt 2 * ‖d.centralCharge u n‖

/-- **H1 — special geometry (prepotential form), now contentful.** There is a holomorphic
prepotential `F` on the special-coordinate image such that the duals are its first derivatives
and the coupling is its Hessian:
`a_{D,i} = ∂F/∂aᵢ` and `τ_{ij} = ∂²F/∂aᵢ∂aⱼ`.
Symmetry of `τ` is automatic (it is a Hessian — Clairaut) and `Im τ ≻ 0` is carried by the
`SiegelUpperHalfSpace` type, so this single statement encodes the full special-Kähler
structure. (One-loop-exactness of the perturbative part of `F` is the remaining genuine input,
added as a separate clause when the asymptotics layer is in place.) -/
def SpecialGeometry : Prop :=
  ∃ F : (Fin r → ℂ) → ℂ, DifferentiableOn ℂ F (d.a '' d.U) ∧
    (∀ u ∈ d.U, ∀ i, d.aD u i = partialDeriv F i (d.a u)) ∧
    (∀ u ∈ d.U, ∀ i j, (d.tau u).val i j = partialDeriv2 F i j (d.a u))

/-- **H2 — masslessness, now defined via the central charge.** The BPS state of charge `n`
becomes massless at `u₀ ∈ Δ` iff its central charge `Z_n → 0` as the modulus approaches `u₀`
from within the smooth chart `U`. (`a, aD` stay finite at `Δ`; it is the combination `Z_n`
that vanishes — e.g. `a_D → 0` at the monopole point, `n = (0,1)`.) -/
def BecomesMasslessAt (u₀ : Fin r → ℂ) (n : ChargeLattice r) : Prop :=
  Tendsto (fun u => d.centralCharge u n) (𝓝[d.U] u₀) (𝓝 0)

/-- **H2 — exact singularity structure, now contentful.** Two halves:
* *massive off `Δ`*: at every smooth point every nonzero BPS charge has `Z_n ≠ 0`;
* *massless on `Δ`*: every boundary point of the chart lying in `Δ` is one where some nonzero
  BPS charge becomes massless. -/
def SingularitiesAreBPS : Prop :=
  (∀ u ∈ d.U, ∀ n : ChargeLattice r, n ≠ 0 → d.centralCharge u n ≠ 0) ∧
  (∀ u₀ ∈ closure d.U ∩ Δ, ∃ n : ChargeLattice r, n ≠ 0 ∧ d.BecomesMasslessAt u₀ n)

/-- **Argyres–Douglas locus (derived).** Boundary points where two *mutually non-local*
charges (`diracPairing ≠ 0`) become massless together — the coalescence producing an
interacting SCFT. Built from `BecomesMasslessAt` and `diracPairing`, not posited. -/
def ArgyresDouglasLocus : Set (Fin r → ℂ) :=
  { u₀ | ∃ n n' : ChargeLattice r, n ≠ 0 ∧ n' ≠ 0 ∧ diracPairing n n' ≠ 0 ∧
        d.BecomesMasslessAt u₀ n ∧ d.BecomesMasslessAt u₀ n' }

end SpecialGeometryData

/-
## The prepotential-primitive variant (alternative encoding of H1)

Instead of carrying `aD, tau` as fields and *asserting* the relations, make the prepotential
the only datum and *derive* the rest:

    structure SpecialGeometryData' (Δ) where
      U   : Set (Fin r → ℂ)
      hU  : IsOpen U
      F   : (Fin r → ℂ) → ℂ            -- the prepotential (in special coordinates a = u here)
      hF  : DifferentiableOn ℂ F U
    def aD'  (d) (a) (i) : ℂ           := partialDeriv d.F i a        -- ∂F/∂aᵢ, by definition
    def tau' (d) (a) (i j) : ℂ         := partialDeriv2 d.F i j a      -- ∂²F/∂aᵢ∂aⱼ
    -- `SpecialGeometry'` then only needs:  Im(tau') ≻ 0  +  one-loop-exactness of F.

Here `aD`, `τ` *cannot* be inconsistent with a prepotential — they are its derivatives — so
special geometry is built into the types rather than asserted. The trade-off: the
gauge-invariant moduli `u`, the singular locus `Δ`, and masslessness then live one layer up
(a map from `a`-space to `u`-space), which is the cleaner place to put the global monodromy.
-/

end SeibergWitten.Physics.Design
