/-
# The physical hypotheses behind the Seiberg–Witten solution (skeleton)

The rigorous spine of this repo (Phases 0–2) proves *implications* of the form
`A,B,C ⇒ X,Y,Z`: **given** the curve `y² = P_N² − Λ^{2N}` and the period geometry of
`jacobian-challenge`, **then** `τ = τᵀ`, `Im τ ≻ 0`, `a_D = ∂F/∂a`, `τ = ∂²F/∂a²`, … .
Those are theorems of mathematics.

What singled out *this* curve in the first place is **physical lore** — a tight web of
assumptions the community trusts but which is not a theorem of ZFC and may never be.
This file codifies that lore as a small set of explicit, named hypotheses, so that the
residual trust collapses onto them (visible in `#print axioms`) rather than being
spread through a long informal argument. See
`docs/foundations-for-physical-reasoning.md`.

## Faithfulness of the carrier (why the data lives on the cover)

A subtle point, flagged in external review (GR): the special coordinates `a, a_D` and
the coupling `τ` are **not** single-valued functions on the Coulomb branch `ℂ^r`.

* `a, a_D` are multivalued — encircling a singularity acts on the pair by an
  `Sp(2r, ℤ)` monodromy; the electromagnetic charge lattice is a *local system* over
  `U = ℂ^r ∖ Δ`, not a global `ℤ^{2r}`.
* `τ(u)` would, if globally single-valued and holomorphic `ℂ^r → SiegelUpperHalfSpace`,
  be **constant** by Liouville — i.e. a free theory. The interacting theory requires
  the data to live on `U` (where `τ` can vary) / its universal cover (where the
  multivalued `a, a_D` become single-valued).

So the carrier `LowEnergyData r Δ` puts `a, a_D, τ` on the universal cover
`SmoothCover Δ` of `U = ℂ^r ∖ Δ`. The central charge `Z = nₑ·a + n_m·a_D` is the
duality-invariant combination that descends to a single-valued function on `U` (the
physical BPS mass).

## The physical inputs (codified as named hypotheses)

Seiberg–Witten 1994; KLYT 1995; Argyres–Faraggi 1995:

1. **Special geometry / holomorphy** (`SpecialGeometry`) — N=2 SUSY ⇒ a holomorphic
   prepotential `F` with `a_D = ∂F/∂a`, `τ = ∂²F/∂a²` (so `τ` symmetric), one-loop
   exact perturbation theory.
2. **Exact singularity structure** (`SingularitiesAreBPS`) — `U` is singular *exactly*
   where some BPS state becomes massless, nowhere else.
3. **Picard–Lefschetz monodromy class** (`PicardLefschetzAtGenericSingularities`) — at
   the *generic* (smooth, simple-zero, codimension-1) stratum of `Δ` a single N=2
   hypermultiplet goes massless, so the local monodromy is the Picard–Lefschetz
   reflection `v ↦ v + ⟨v, nₐ⟩ nₐ` of its vanishing charge `nₐ`. (Without this one can
   invent wild singularities with `Z = 0` that are not local QFTs — flagged in review.)
   Restricted to the *generic* stratum because the deeper strata host Argyres–Douglas
   points (below), where a single reflection fails.
4. **Electric–magnetic duality** (`EMDualityConsistent`) — the monodromies lie in
   `Sp(2r, ℤ)` and compose to the weak-coupling (semiclassical) monodromy.
5. **R-symmetry** (`RSymmetryConsistent`) — the anomalous `U(1)_R → ℤ_{2N}` acts on the
   moduli, fixing the symmetric distribution of `Δ` (the asymptotics fix the *number*
   of singularities; the R-symmetry fixes their *positions*).
6. **Asymptotic matching** (`AsymptoticMatch`) — the weak-coupling (one-loop +
   instanton) expansion, with the correct leading β-function coefficient, is asymptotic
   to the exact periods.

Together these are believed to fix the curve **uniquely up to `Sp(2r, ℤ)` duality**
(the periods are only defined up to a frame change). That is the headline statement,
recorded as a physical axiom.

## Argyres–Douglas points (a *derived* notion, not a new axiom)

In reality `Δ` is stratified and its deeper strata carry more than one vanishing cycle.
Argyres–Douglas (AD) points are where ≥2 vanishing cycles **coalesce** and are
**mutually non-local** — their Dirac pairing `⟨nₐ, n_b⟩ ≠ 0` — so a monopole and a
dyon become massless simultaneously and *no* duality frame makes all light states
local (an interacting N=2 SCFT, no Lagrangian). Crucially this is **not** a new physical
input: it is *defined* (`ArgyresDouglasLocus`) from the central charge plus the
`diracPairing` on the charge lattice, both available now. AD points still satisfy H2
(they are massless-BPS loci); what they evade is the *single-reflection* H3, which is
why H3 is restricted to the generic stratum. Coalescence of *mutually local* cycles
(`⟨nₐ,n_b⟩ = 0`) instead gives enhanced non-abelian gauge symmetry — still Lagrangian.
Making `ArgyresDouglasLocus = {higher-order discriminant vanishing}` a *theorem* about
the SW curve is Phase 3 (PLAN.md).

This is a **skeleton**: the carrier cover and predicates (1), (3)–(6) and the duality
equivalence are introduced as *named, uninterpreted* symbols — explicit holes whose
precise content is built in later phases (Phase 2: prepotential / periods; Phase 3:
Picard–Fuchs / monodromy / AD strata; Phase 4: `Sp(2r,ℤ)` action). Every axiom here is
`(NOT VERIFIED)` and tracked in `AXIOM_AUDIT.md`. Reviewed by Gemini (GR) 2026-06-24;
the cover/Liouville, Picard–Lefschetz, R-symmetry, and Argyres–Douglas refinements are
from that review.

References: Seiberg–Witten, *Nucl. Phys.* B426 (1994) [hep-th/9407087]; B431 (1994)
[hep-th/9408099]; Klemm–Lerche–Yankielowicz–Theisen, *Phys. Lett.* B344 (1995);
Argyres–Faraggi, *Phys. Rev. Lett.* 74 (1995); Argyres–Douglas, *Nucl. Phys.* B448
(1995); Lerche, hep-th/9611190 (review).
-/
import SeibergWitten.Curve
import Jacobians.Axioms.RiemannBilinear

open Jacobians.AbelianVariety

namespace SeibergWitten.Physics

/-- The lattice of electric–magnetic charges `(nₑ, n_m) ∈ ℤ^r × ℤ^r` of the
low-energy `U(1)^r` gauge theory (`r = N − 1` is the rank). Over `U = ℂ^r ∖ Δ` this is
the fibre of a local system; a fixed `ChargeLattice r` is a trivialization in one
duality frame (one sheet of the cover). -/
abbrev ChargeLattice (r : ℕ) : Type := (Fin r → ℤ) × (Fin r → ℤ)

/-- **Dirac–Schwinger–Zwanziger pairing** on the charge lattice:
`⟨(eₐ,mₐ), (e_b,m_b)⟩ = eₐ·m_b − mₐ·e_b`. Two charges are **mutually non-local** iff
this is nonzero — they cannot be made simultaneously electric in any duality frame.
This is the antisymmetric form preserved by `Sp(2r, ℤ)`. -/
def diracPairing {r : ℕ} (n n' : ChargeLattice r) : ℤ :=
  (∑ i, n.1 i * n'.2 i) - (∑ i, n.2 i * n'.1 i)

/-- **Universal cover of the smooth Coulomb branch** `U = ℂ^r ∖ Δ`, abstract. The
multivalued special coordinates `a, a_D` become single-valued on it; the projection
lands in `U`. Built concretely in a later phase; here an uninterpreted carrier so the
faithful (multivalued) typing of the data is available now.

    Faithfulness (NOT VERIFIED): skeleton carrier for `univ-cover(ℂ^r ∖ Δ)`. -/
axiom SmoothCover : ∀ {r : ℕ}, Set (Fin r → ℂ) → Type

/-- Projection of the cover to the smooth Coulomb branch `U = ℂ^r ∖ Δ ⊆ ℂ^r`. -/
axiom SmoothCover.proj : ∀ {r : ℕ} {Δ : Set (Fin r → ℂ)}, SmoothCover Δ → (Fin r → ℂ)

/-- **Low-energy effective data on the Coulomb branch**, defined on the universal cover
of `U = ℂ^r ∖ Δ` (so the multivalued `a, a_D` are single-valued and `τ` is free to
vary — see the module docstring on Liouville). At each cover point the data is the
special coordinates `aᵢ`, their duals `a_{D,i}`, and the effective gauge coupling `τ`
in the Siegel upper half space (symmetric, `Im τ ≻ 0`). -/
structure LowEnergyData (r : ℕ) (Δ : Set (Fin r → ℂ)) where
  /-- special coordinates `aᵢ` on the cover (multivalued over `U`). -/
  a : SmoothCover Δ → (Fin r → ℂ)
  /-- dual special coordinates `a_{D,i}`. -/
  aD : SmoothCover Δ → (Fin r → ℂ)
  /-- effective gauge coupling `τ ∈ SiegelUpperHalfSpace r` (holomorphic on the cover). -/
  tau : SmoothCover Δ → SiegelUpperHalfSpace r

namespace LowEnergyData

variable {r : ℕ} {Δ : Set (Fin r → ℂ)}

/-- **Central charge** of a BPS state of charge `(nₑ, n_m)` at a cover point `p`:
`Z = nₑ · a + n_m · a_D`. This is the duality-invariant combination that descends to a
single-valued function on `U` (its modulus is the physical BPS mass). -/
noncomputable def centralCharge (d : LowEnergyData r Δ) (p : SmoothCover Δ)
    (n : ChargeLattice r) : ℂ :=
  (∑ i, (n.1 i : ℂ) * d.a p i) + (∑ i, (n.2 i : ℂ) * d.aD p i)

/-- **BPS mass** of a state of charge `n` at a cover point `p`: `M = √2 · |Z|`. -/
noncomputable def bpsMass (d : LowEnergyData r Δ) (p : SmoothCover Δ)
    (n : ChargeLattice r) : ℝ :=
  Real.sqrt 2 * ‖d.centralCharge p n‖

end LowEnergyData

variable {r : ℕ}

/-! ## The physical hypotheses -/

/-- **H1 — Special geometry / holomorphy / non-renormalization** (N=2 SUSY).

    There is a holomorphic prepotential `F` with `a_{D,i} = ∂F/∂aᵢ` and
    `τ_{ij} = ∂²F/∂aᵢ∂aⱼ` (in particular `τ` is symmetric — the special-geometry
    integrability `∂a_{D,i}/∂a_j = ∂a_{D,j}/∂a_i`), and the perturbative part of `F` is
    one-loop exact (higher corrections purely instantonic, in powers of `Λ^{2N}`).

    Reference: Seiberg–Witten, hep-th/9407087 §2; Lerche, hep-th/9611190 §2.
    Faithfulness (NOT VERIFIED): uninterpreted skeleton predicate. Made precise in
    Phase 2 on the meromorphic-period layer once `F` is constructed. -/
axiom SpecialGeometry : ∀ {r : ℕ} {Δ : Set (Fin r → ℂ)}, LowEnergyData r Δ → Prop

/-- **H2 — Exact singularity structure.** The singular locus `Δ` is *exactly* the set
of moduli where some nonzero BPS state becomes massless (central charge `→ 0` as the
modulus is approached on the cover) — and nowhere else.

    `BecomesMasslessAt Δ d u n` (uninterpreted): the BPS state of charge `n` becomes
    massless as `u ∈ Δ` is approached, i.e. `d.centralCharge p n → 0` along cover
    points `p` whose projection tends to `u`. (The limiting form is forced because
    `a, a_D` are only defined on the cover, not at `Δ` itself — GR review.) -/
axiom BecomesMasslessAt : ∀ {r : ℕ} (Δ : Set (Fin r → ℂ)), LowEnergyData r Δ →
    (Fin r → ℂ) → ChargeLattice r → Prop

/-- The singular locus is exactly the massless-BPS locus. -/
def SingularitiesAreBPS (Δ : Set (Fin r → ℂ)) (d : LowEnergyData r Δ) : Prop :=
  ∀ u : Fin r → ℂ, u ∈ Δ ↔ ∃ n : ChargeLattice r, n ≠ 0 ∧ BecomesMasslessAt Δ d u n

/-- **Argyres–Douglas locus** (a *derived* notion). The moduli where two **mutually
non-local** BPS states (`diracPairing ≠ 0`) become simultaneously massless — the
coalescence of vanishing cycles that produces an interacting N=2 SCFT with no Lagrangian
frame. A subset of `Δ` (by H2). On the SW curve this is expected to coincide with the
higher-order vanishing locus of the discriminant; proving that is a Phase-3 target.
*Definition, not an axiom* — it is built from `BecomesMasslessAt` and `diracPairing`. -/
def ArgyresDouglasLocus (Δ : Set (Fin r → ℂ)) (d : LowEnergyData r Δ) :
    Set (Fin r → ℂ) :=
  { u | ∃ n n' : ChargeLattice r, n ≠ 0 ∧ n' ≠ 0 ∧ diracPairing n n' ≠ 0 ∧
        BecomesMasslessAt Δ d u n ∧ BecomesMasslessAt Δ d u n' }

/-- **H3 — Picard–Lefschetz monodromy class (generic stratum).** At the generic
    (smooth, simple, codimension-1) stratum of `Δ` — i.e. away from `ArgyresDouglasLocus`
    and other deeper strata — a single N=2 hypermultiplet goes massless, so the local
    monodromy on the charge lattice is the Picard–Lefschetz reflection
    `v ↦ v + ⟨v, nₐ⟩ nₐ` of its vanishing charge `nₐ`. This rules out wild singularities
    with `Z = 0` that are not local QFTs.

    Reference: Seiberg–Witten, hep-th/9407087 §3 (monopole/dyon points); Lerche §3.
    Faithfulness (NOT VERIFIED): uninterpreted skeleton predicate; concrete once the
    monodromy representation is built (Phase 3/4). The genericity restriction is what
    makes room for the Argyres–Douglas strata, where a single reflection fails. -/
axiom PicardLefschetzAtGenericSingularities :
    ∀ {r : ℕ} {Δ : Set (Fin r → ℂ)}, LowEnergyData r Δ → Prop

/-- **H4 — Electric–magnetic duality.** The monodromy of `(a, a_D)` around each
    component of `Δ` lies in `Sp(2r, ℤ)`, and the product of the singularity
    monodromies equals the weak-coupling (semiclassical) monodromy.

    Reference: Seiberg–Witten, hep-th/9407087 §3–4; Argyres–Faraggi (SU(N) monodromy).
    Faithfulness (NOT VERIFIED): uninterpreted skeleton predicate; precise in Phase 3/4
    once `π₁(U) → Sp(2r,ℤ)` is built on `jacobian-challenge`'s `H₁` + intersection form. -/
axiom EMDualityConsistent : ∀ {r : ℕ} {Δ : Set (Fin r → ℂ)}, LowEnergyData r Δ → Prop

/-- **H5 — R-symmetry.** The anomalous `U(1)_R → ℤ_{2N}` global symmetry acts on the
    Coulomb branch, fixing the symmetric distribution of the singular locus `Δ` (the
    asymptotics fix the *number* of singularities; the R-symmetry fixes their
    *positions*).

    Reference: Seiberg–Witten, hep-th/9407087 §4; KLYT (SU(N) `ℤ_{2N}`).
    Faithfulness (NOT VERIFIED): uninterpreted skeleton predicate. -/
axiom RSymmetryConsistent : ∀ {r : ℕ} {Δ : Set (Fin r → ℂ)}, LowEnergyData r Δ → Prop

/-- **H6 — Asymptotic matching.** At weak coupling (large moduli) the periods `a, a_D`
    reproduce the one-loop + instanton expansion of `F`, with the correct leading
    β-function coefficient (which fixes the number of singularities).

    Reference: Seiberg–Witten, hep-th/9407087 §2,4; Nekrasov instanton partition
    function (independent cross-check).
    Faithfulness (NOT VERIFIED): uninterpreted skeleton predicate. Made precise in
    Phase 3 via the Picard–Fuchs ODEs for the periods (`math-commons/picard-lefschetz`),
    against which the matching is *checked*, not asserted. -/
axiom AsymptoticMatch : ∀ {r : ℕ} {Δ : Set (Fin r → ℂ)}, LowEnergyData r Δ → Prop

/-- **Electric–magnetic duality equivalence.** Two effective data are duality-equivalent
    iff related by a global `Sp(2r, ℤ)` frame change of `(a, a_D)` (with the induced
    fractional-linear action on `τ`). The periods are only physically defined up to
    this equivalence, so it is the right notion for the uniqueness statement below.

    Faithfulness (NOT VERIFIED): uninterpreted skeleton predicate; the concrete
    `Sp(2r,ℤ)`-action is supplied in Phase 4. -/
axiom DualityEquiv :
    ∀ {r : ℕ} {Δ : Set (Fin r → ℂ)}, LowEnergyData r Δ → LowEnergyData r Δ → Prop

/-- **A Seiberg–Witten effective theory** with singular locus `Δ`: low-energy data
satisfying all six physical hypotheses. -/
structure IsSWEffectiveTheory (Δ : Set (Fin r → ℂ)) (d : LowEnergyData r Δ) : Prop where
  /-- H1 — special geometry / holomorphy. -/
  specialGeometry : SpecialGeometry d
  /-- H2 — singularities are exactly massless-BPS loci. -/
  singularities : SingularitiesAreBPS Δ d
  /-- H3 — Picard–Lefschetz monodromy class on the generic stratum. -/
  picardLefschetz : PicardLefschetzAtGenericSingularities d
  /-- H4 — `Sp(2r,ℤ)` monodromy consistency. -/
  duality : EMDualityConsistent d
  /-- H5 — `ℤ_{2N}` R-symmetry distribution of `Δ`. -/
  rSymmetry : RSymmetryConsistent d
  /-- H6 — weak-coupling asymptotic matching. -/
  matching : AsymptoticMatch d

/-! ## The headline goals: the hypotheses fix the solution

These are **not axioms**. They are the *mathematical implications* the physical hypotheses
H1–H6 are meant to entail — uniqueness (a period-map rigidity statement) and existence — so
each is stated as a **goal** (`theorem … := sorry`), to be proved, not asserted into the
trusted base. Uniqueness is **proved for SU(2)** in `SU2Rigidity.lean` (`sw_su2_unique`,
modulo the classical-math covering/lift axioms); the general-rank statements remain open. -/

/-- **GOAL — uniqueness up to duality** (period-map rigidity; *not* an axiom).

    Any two low-energy effective data with the *same* singular locus `Δ` that both satisfy the
    six physical hypotheses are electric–magnetic duals of one another: special geometry + the
    exact singularity structure + Picard–Lefschetz on the generic stratum + duality consistency
    + R-symmetry + asymptotic matching **fix the Coulomb-branch solution uniquely up to
    `Sp(2r,ℤ)`** — this is why physicists believe the SW curve is *the* answer. (The
    Argyres–Douglas strata are then *forced* as coalescence loci, `ArgyresDouglasLocus`, not
    independent inputs.)

    This is a *consequence* of H1–H6, hence a goal to prove (`sorry`), not a trusted input.
    **Proved for SU(2)** in `sw_su2_unique`; general rank is open.
    Reference: Seiberg–Witten, hep-th/9407087 (the original uniqueness argument);
    Argyres–Faraggi / KLYT for SU(N). -/
theorem sw_effective_theory_unique_up_to_duality
    {r : ℕ} (Δ : Set (Fin r → ℂ)) (d d' : LowEnergyData r Δ)
    (h : IsSWEffectiveTheory Δ d) (h' : IsSWEffectiveTheory Δ d') :
    DualityEquiv d d' := by
  sorry

/-- **GOAL — existence: the SW curve realizes such a theory** (*not* an axiom).

    The hyperelliptic curve `y² = P_N² − Λ^{2N}` (`swData`), via its period geometry, furnishes
    low-energy effective data satisfying the six physical hypotheses, with singular locus the
    discriminant of the curve. Together with uniqueness, this is the statement that the SW curve
    gives *the* (essentially unique) low-energy solution of N=2 SU(N) SYM.

    A goal to prove (`sorry`), not an axiom: the data is constructed from the periods of the
    curve (Phase 2), and the `τ ∈ Siegel` half is already a theorem (`sw_coupling_mem_siegel`).
    Reference: Seiberg–Witten, hep-th/9407087; KLYT / Argyres–Faraggi (SU(N)). -/
theorem sw_curve_admits_effective_theory
    {N : ℕ} (P : Polynomial ℂ) (Λ : ℂ)
    (hPdeg : P.natDegree = N) (hN : 2 ≤ N)
    (hsf : Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * N)))) :
    ∃ (Δ : Set (Fin (N - 1) → ℂ)) (d : LowEnergyData (N - 1) Δ),
      IsSWEffectiveTheory Δ d := by
  sorry

end SeibergWitten.Physics
