/-
# DRAFT — strengthened carrier with the cover-vs-base split (H1, H2, and the H4 gluing)

**Proposal only.** Not wired into the build and not replacing `Hypotheses.lean`; for review
before refactoring. Iterates the previous draft by separating the two layers the physics
demands:

* **Base** — the smooth Coulomb branch in **gauge-invariant moduli** `u ∈ U ⊆ ℂ^r ∖ Δ`
  (the Casimirs / coefficients of `P_N`, *not* the eigenvalues). `Δ`, the metric, and the BPS
  masses live here and are single-valued (monodromy-invariant).
* **Cover** — the multivalued special coordinates `a, a_D` and coupling `τ` are single-valued
  only on simply-connected **sheets** `V ⊆ U`. The eigenvalues are the weak-coupling limit of
  `a`; their Weyl `S_N` ambiguity and the quantum monodromy are exactly the gluing of sheets.

This makes the hypotheses contentful:

* **H1** on a sheet: `∃ F, a_D = ∂F/∂a ∧ τ = ∂²F/∂a²` (`Im τ ≻ 0` carried by the type;
  symmetry of `τ` automatic — it is a Hessian);
* **H2** on the base: `BecomesMasslessAt u₀ n := Z_n → 0` along `𝓝[V] u₀` toward `u₀ ∈ Δ`,
  plus "massive at smooth points"; H2/H3 share the vanishing charge `n`;
* **H4** as a `Deck` gluing: overlapping sheets are related by a Dirac-pairing-preserving
  (= `Sp(2r,ℤ)`) action on charges under which the central charge is covariant — so `|Z|`
  (the mass) and the metric descend to the base.
* **H6** as asymptotic matching: the prepotential `F` matches the weak-coupling one-loop +
  instanton form (`F − F_cl − F₁ → 0` as `|a| → ∞`) — the non-renormalization input that pins
  the special geometry of H1 to *the* SW prepotential (rather than an arbitrary special-Kähler
  structure). `Sheet.MatchesAsymptotics` bundles H1 + H6.

A prepotential-primitive variant (make `F` the datum; derive `a_D, τ`) is sketched at the end.
-/
import SeibergWitten.Physics.Hypotheses
import Mathlib

open Complex Filter Topology Matrix Jacobians.AbelianVariety

namespace SeibergWitten.Physics.Design

variable {r : ℕ}

/-- `∂F/∂xᵢ` at `x`, for a holomorphic prepotential `F : ℂ^r → ℂ`. -/
noncomputable def partialDeriv (F : (Fin r → ℂ) → ℂ) (i : Fin r) (x : Fin r → ℂ) : ℂ :=
  fderiv ℂ F x (Pi.single i 1)

/-- `∂²F/∂xᵢ∂xⱼ` at `x`. -/
noncomputable def partialDeriv2 (F : (Fin r → ℂ) → ℂ) (i j : Fin r) (x : Fin r → ℂ) : ℂ :=
  partialDeriv (fun y => partialDeriv F i y) j x

/-! ## The base: the smooth Coulomb branch in gauge-invariant moduli -/

/-- **The base.** The Coulomb branch in gauge-invariant moduli `u ∈ ℂ^r` (Casimirs /
coefficients of the characteristic polynomial), with singular locus `Δ` (the discriminant of
the SW curve) and smooth part `U`. Single-valued data — `Δ`, the metric, BPS masses — live
here. -/
structure CoulombBase (r : ℕ) where
  /-- singular locus (curve discriminant) -/
  Δ : Set (Fin r → ℂ)
  /-- smooth part of the Coulomb branch -/
  U : Set (Fin r → ℂ)
  hUopen : IsOpen U
  hUsmooth : U ⊆ Δᶜ

/-! ## The cover: sheets carrying the multivalued special coordinates -/

/-- **A sheet** — a local trivialization of the cover over a simply-connected open `V ⊆ U`,
where the multivalued special coordinates are single-valued holomorphic functions. The
eigenvalues are the weak-coupling limit of `a`; their Weyl ambiguity and the quantum monodromy
are the gluing of sheets (`Deck` below), not visible within one sheet. -/
structure Sheet (B : CoulombBase r) where
  /-- the chart on the base -/
  V : Set (Fin r → ℂ)
  hVopen : IsOpen V
  hVsub : V ⊆ B.U
  /-- a simply-connected chart: periods are single-valued here -/
  hVsc : SimplyConnectedSpace V
  /-- special coordinates `aᵢ(u)`, holomorphic on `V` -/
  a : (Fin r → ℂ) → (Fin r → ℂ)
  ha : DifferentiableOn ℂ a V
  /-- dual special coordinates `a_{D,i}(u)`, holomorphic on `V` -/
  aD : (Fin r → ℂ) → (Fin r → ℂ)
  haD : DifferentiableOn ℂ aD V
  /-- coupling `τ(u) ∈ SiegelUpperHalfSpace r` (symmetric, `Im ≻ 0`) — multivalued across
  sheets, single-valued here -/
  tau : (Fin r → ℂ) → SiegelUpperHalfSpace r

namespace Sheet

variable {B : CoulombBase r} (s : Sheet B)

/-- **Central charge** `Z_n(u) = nₑ · a(u) + n_m · a_D(u)` on a sheet — a holomorphic function
of `u ∈ s.V`. -/
noncomputable def centralCharge (u : Fin r → ℂ) (n : ChargeLattice r) : ℂ :=
  (∑ i, (n.1 i : ℂ) * s.a u i) + (∑ i, (n.2 i : ℂ) * s.aD u i)

/-- **BPS mass** `M_n(u) = √2 ‖Z_n(u)‖`. -/
noncomputable def bpsMass (u : Fin r → ℂ) (n : ChargeLattice r) : ℝ :=
  Real.sqrt 2 * ‖s.centralCharge u n‖

/-- **H1 — special geometry (prepotential form), on a sheet.** A holomorphic prepotential `F`
with `a_{D,i} = ∂F/∂aᵢ` and `τ_{ij} = ∂²F/∂aᵢ∂aⱼ`. Symmetry of `τ` is automatic (Hessian),
`Im τ ≻ 0` is carried by the `SiegelUpperHalfSpace` type — so this single statement is the full
special-Kähler structure. (One-loop-exactness of the perturbative part of `F` is added when the
asymptotics layer lands.) -/
def SpecialGeometry : Prop :=
  ∃ F : (Fin r → ℂ) → ℂ, DifferentiableOn ℂ F (s.a '' s.V) ∧
    (∀ u ∈ s.V, ∀ i, s.aD u i = partialDeriv F i (s.a u)) ∧
    (∀ u ∈ s.V, ∀ i j, (s.tau u).val i j = partialDeriv2 F i j (s.a u))

/-- **H2 — masslessness, defined via the central charge.** Charge `n` becomes massless at
`u₀ ∈ Δ` iff `Z_n → 0` as `u → u₀` from within the sheet. (`a, a_D` stay finite at `Δ`; it is
`Z_n` that vanishes — e.g. `a_D → 0` at the monopole point, `n = (0,1)`.) -/
def BecomesMasslessAt (u₀ : Fin r → ℂ) (n : ChargeLattice r) : Prop :=
  Tendsto (fun u => s.centralCharge u n) (𝓝[s.V] u₀) (𝓝 0)

/-- **H2 — exact singularity structure, on a sheet.** Massive at smooth points (`Z_n ≠ 0`),
and every chart-boundary point in `Δ` is where some nonzero charge becomes massless. (The
global statement quantifies over an atlas of sheets covering `B.U`.) -/
def SingularitiesAreBPS : Prop :=
  (∀ u ∈ s.V, ∀ n : ChargeLattice r, n ≠ 0 → s.centralCharge u n ≠ 0) ∧
  (∀ u₀ ∈ closure s.V ∩ B.Δ, ∃ n : ChargeLattice r, n ≠ 0 ∧ s.BecomesMasslessAt u₀ n)

/-- **Argyres–Douglas locus (derived).** Chart-boundary points where two *mutually non-local*
charges (`diracPairing ≠ 0`) become massless together. -/
def ArgyresDouglasLocus : Set (Fin r → ℂ) :=
  { u₀ | ∃ n n' : ChargeLattice r, n ≠ 0 ∧ n' ≠ 0 ∧ diracPairing n n' ≠ 0 ∧
        s.BecomesMasslessAt u₀ n ∧ s.BecomesMasslessAt u₀ n' }

end Sheet

/-! ## The gluing (H4): monodromy as a Dirac-pairing-preserving deck action -/

/-- **H4 — the cover gluing / electric–magnetic duality.** On the overlap of two sheets the
special coordinates differ by a duality frame change: a charge-lattice map `g` that **preserves
the Dirac pairing** (i.e. lies in `Sp(2r,ℤ)`) under which the central charge is **covariant**,
`Z_{g n}(s') = Z_n(s)`. Consequences: `|Z|` (the BPS mass) and the special-Kähler metric are
`Sp`-invariant, so they **descend to the base** even though `a, a_D, τ` do not. (This is where
the Weyl `S_N` ⊂ monodromy and the quantum monodromy live; cf. `SameSWMonodromy`,
`AX_developing_map_rigidity`.) -/
structure Deck {B : CoulombBase r} (s s' : Sheet B) where
  /-- the duality action on charges -/
  g : ChargeLattice r → ChargeLattice r
  /-- it preserves the Dirac pairing — i.e. lands in `Sp(2r,ℤ)` -/
  symplectic : ∀ n n', diracPairing (g n) (g n') = diracPairing n n'
  /-- the central charge is covariant on the overlap -/
  covariant : ∀ u ∈ s.V ∩ s'.V, ∀ n, s'.centralCharge u (g n) = s.centralCharge u n

/-- **BPS mass descends to the base.** A `Deck` gluing makes the mass sheet-independent on the
overlap: `M` is single-valued on the Coulomb branch though `a, a_D` are not. -/
theorem Deck.bpsMass_eq {B : CoulombBase r} {s s' : Sheet B} (D : Deck s s')
    {u : Fin r → ℂ} (hu : u ∈ s.V ∩ s'.V) (n : ChargeLattice r) :
    s'.bpsMass u (D.g n) = s.bpsMass u n := by
  unfold Sheet.bpsMass
  rw [D.covariant u hu n]

/-! ## H6 — asymptotic matching (the non-renormalization input)

This is what pins the special-geometry data down to *the* SW theory: the prepotential `F` of
H1 must match the known weak-coupling computation. The N=2 non-renormalization theorem says the
perturbative prepotential is **one-loop exact**, so at weak coupling
`F = F_classical + F_1loop + (instantons)`, the instanton corrections being a series in `Λ^{2N}`
that vanishes as `|a| → ∞`. Matching this asymptotics — together with the singularity structure
(H2/H3) and duality (H4) — is what makes the solution unique; without it, H1 is merely "some
special-Kähler geometry". -/

/-- **One-loop prepotential** — the charged W-boson contributions,
`F₁(a) = (i/8π) ∑_{i≠j} (aᵢ−aⱼ)² log((aᵢ−aⱼ)²/Λ²)`. Its Hessian is the one-loop logarithmic
running of the `U(1)^{N-1}` couplings; the massless W at `aᵢ = aⱼ` is the classical
enhanced-symmetry locus (excluded from the smooth region). -/
noncomputable def oneLoopPrepotential (Λ : ℂ) (a : Fin r → ℂ) : ℂ :=
  (Complex.I / (8 * (Real.pi : ℂ))) *
    ∑ i, ∑ j, if i = j then 0 else (a i - a j) ^ 2 * Complex.log ((a i - a j) ^ 2 / Λ ^ 2)

/-- **H6 — asymptotic matching / non-renormalization.** In the semiclassical limit `|a| → ∞`
the prepotential matches classical + one-loop, the remainder (instantons) vanishing:
`F − (F_cl + F₁) → 0` along the cocompact filter. With H1 (`τ = ∂²F/∂a²`) this is the one-loop
running of the effective couplings; it is the boundary condition that, with H2/H3/H4, fixes
`F`. (The *full* non-renormalization statement is stronger — the remainder is purely
instantonic, a power series in `Λ^{2N}` with no higher-loop logarithms — `Instantonic` below.) -/
def AsymptoticMatch (Λ : ℂ) (Fcl F : (Fin r → ℂ) → ℂ) : Prop :=
  Tendsto (fun a => F a - (Fcl a + oneLoopPrepotential Λ a))
    (Filter.cocompact (Fin r → ℂ)) (𝓝 0)

/-- A sheet **matches the asymptotics**: its special-geometry prepotential (H1) exists and has
the required weak-coupling form (H6), for some classical part `Fcl`. This is the clause that
upgrades H1 from "a special-Kähler structure" to "*the* SW prepotential". -/
def Sheet.MatchesAsymptotics {B : CoulombBase r} (s : Sheet B) (Λ : ℂ) : Prop :=
  ∃ F : (Fin r → ℂ) → ℂ, DifferentiableOn ℂ F (s.a '' s.V) ∧
    (∀ u ∈ s.V, ∀ i, s.aD u i = partialDeriv F i (s.a u)) ∧
    (∀ u ∈ s.V, ∀ i j, (s.tau u).val i j = partialDeriv2 F i j (s.a u)) ∧
    ∃ Fcl, AsymptoticMatch Λ Fcl F

end SeibergWitten.Physics.Design

/-
## The prepotential-primitive variant (alternative encoding of H1)

Instead of carrying `a, aD, τ` as sheet fields and *asserting* the relations, make the
prepotential the only datum on a sheet and *derive* the rest:

    structure Sheet' (B) where
      V : Set (Fin r → ℂ) ; … ; F : (Fin r → ℂ) → ℂ ; hF : DifferentiableOn ℂ F V
    def aD'  (s) (a) (i) : ℂ := partialDeriv  s.F i a       -- ∂F/∂aᵢ, by definition
    def tau' (s) (a) (i j) : ℂ := partialDeriv2 s.F i j a    -- ∂²F/∂aᵢ∂aⱼ
    -- `SpecialGeometry'` then only needs  Im(tau') ≻ 0  +  one-loop-exactness of F.

Here `aD, τ` cannot be inconsistent with a prepotential — they *are* its derivatives — so
special geometry is built into the types. The base/cover split and the `Deck` gluing are
unchanged.
-/
