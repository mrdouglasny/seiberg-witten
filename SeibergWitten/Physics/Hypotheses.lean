/-
# The physical hypotheses behind the Seiberg–Witten solution

The rigorous spine of this repo proves *implications* `A,B,C ⇒ X,Y,Z` (given the curve and
the period geometry, then `τ = τᵀ`, `Im τ ≻ 0`, …). What singled out *this* curve is
**physical lore** — codified here as a small set of explicit, named hypotheses, so the
residual trust collapses onto them (`#print axioms`). See
`docs/foundations-for-physical-reasoning.md`.

## The real foundational axiom: H0

The genuine input is **H0 — on the Coulomb branch the IR theory is an N=2 `U(1)^{N-1}` gauge
theory** (the non-abelian `SU(N)` is Higgsed to its Cartan). Everything else is structure on
that EFT, and the carrier *is* its data:

* the rank `r = N − 1` is the rank of `U(1)^{N-1}`;
* the gauge-invariant moduli `u ∈ ℂ^r` (Casimirs / coefficients of the characteristic
  polynomial, **not** the eigenvalues) are the **base**, with singular locus `Δ` (the curve
  discriminant) and smooth part `U`;
* the multivalued special coordinates `a, a_D` and coupling `τ` are single-valued only on
  simply-connected **sheets** `V ⊆ U`. (`τ` cannot be globally single-valued holomorphic — it
  would be constant by Liouville, a free theory. The eigenvalues are the weak-coupling limit of
  `a`; the Weyl `S_N` ambiguity and the quantum monodromy are the gluing of sheets.)

## The structural hypotheses

1. **H1 — special geometry** (`Sheet.SpecialGeometry`): a holomorphic prepotential `F` with
   `a_D = ∂F/∂a`, `τ = ∂²F/∂a²`.
2. **H2 — exact singularity structure** (`Sheet.SingularitiesAreBPS`): massive at smooth points
   (`Z_n ≠ 0`); every boundary point in `Δ` is where some BPS charge becomes massless
   (`Z_n → 0`).
3. **H3 — Picard–Lefschetz** (`PicardLefschetzAtGenericStratum`): the local monodromy is the
   reflection `v ↦ v + ⟨v,n⟩ n` in the **same vanishing charge `n`** of H2.
4. **H4 — electric–magnetic duality** (`Deck`): sheets glue by a Dirac-pairing-preserving
   (= `Sp(2r,ℤ)`) charge action with covariant central charge; mass and metric descend.
5. **H5 — R-symmetry** (`RSymmetry`): a `ℤ_{2N}` action on the moduli fixing the positions of
   `Δ`.
6. **H6 — asymptotic matching / non-renormalization** (`Sheet.MatchesAsymptotics`, `Instantonic`):
   `F` matches the weak-coupling one-loop form, the remainder purely instantonic.

The headline implications (existence; uniqueness up to `Sp(2r,ℤ)`) are *mathematical
consequences*, stated as **goals** (`theorem … := sorry`), not axioms. Argyres–Douglas points
are **derived** (`ArgyresDouglasLocus`). Tracked in `AXIOM_AUDIT.md`.

References: Seiberg–Witten, *Nucl. Phys.* B426 (1994) [hep-th/9407087]; B431 (1994); KLYT,
*Phys. Lett.* B344 (1995); Argyres–Faraggi, *PRL* 74 (1995); Argyres–Douglas, *Nucl. Phys.*
B448 (1995); Lerche, hep-th/9611190.
-/
import SeibergWitten.Curve
import Jacobians.Axioms.RiemannBilinear
import Mathlib

open Complex Filter Topology Jacobians.AbelianVariety

namespace SeibergWitten.Physics

variable {r : ℕ}

/-! ## Charge lattice and Dirac pairing -/

/-- The lattice of electric–magnetic charges `(nₑ, n_m) ∈ ℤ^r × ℤ^r` of the low-energy
`U(1)^r` gauge theory (`r = N − 1`). Over `U = ℂ^r ∖ Δ` it is the fibre of a local system. -/
abbrev ChargeLattice (r : ℕ) : Type := (Fin r → ℤ) × (Fin r → ℤ)

/-- **Dirac–Schwinger–Zwanziger pairing** `⟨(eₐ,mₐ),(e_b,m_b)⟩ = eₐ·m_b − mₐ·e_b`. Two charges
are **mutually non-local** iff this is nonzero. The antisymmetric form preserved by `Sp(2r,ℤ)`. -/
def diracPairing {r : ℕ} (n n' : ChargeLattice r) : ℤ :=
  (∑ i, n.1 i * n'.2 i) - (∑ i, n.2 i * n'.1 i)

/-! ## Prepotential derivatives -/

/-- `∂F/∂xᵢ` at `x`, for a holomorphic prepotential `F : ℂ^r → ℂ`. -/
noncomputable def partialDeriv (F : (Fin r → ℂ) → ℂ) (i : Fin r) (x : Fin r → ℂ) : ℂ :=
  fderiv ℂ F x (Pi.single i 1)

/-- `∂²F/∂xᵢ∂xⱼ` at `x`. -/
noncomputable def partialDeriv2 (F : (Fin r → ℂ) → ℂ) (i j : Fin r) (x : Fin r → ℂ) : ℂ :=
  partialDeriv (fun y => partialDeriv F i y) j x

/-! ## H6 — one-loop prepotential and the non-renormalization input -/

/-- **One-loop prepotential** — the charged W-boson contributions
`F₁(a) = (i/8π) ∑_{i≠j} (aᵢ−aⱼ)² log((aᵢ−aⱼ)²/Λ²)`. Its Hessian is the one-loop running of the
`U(1)^{N-1}` couplings. -/
noncomputable def oneLoopPrepotential (Λ : ℂ) (a : Fin r → ℂ) : ℂ :=
  (Complex.I / (8 * (Real.pi : ℂ))) *
    ∑ i, ∑ j, if i = j then 0 else (a i - a j) ^ 2 * Complex.log ((a i - a j) ^ 2 / Λ ^ 2)

/-- **Asymptotic matching (weak form).** `F − (F_cl + F₁) → 0` as `|a| → ∞` — the instanton
corrections vanish at weak coupling. -/
def AsymptoticMatch (Λ : ℂ) (Fcl F : (Fin r → ℂ) → ℂ) : Prop :=
  Tendsto (fun a => F a - (Fcl a + oneLoopPrepotential Λ a))
    (Filter.cocompact (Fin r → ℂ)) (𝓝 0)

/-- **H6 — non-renormalization (sharp form).** The deviation of `F` from classical + one-loop is
**purely instantonic**: a power series in the instanton factor `Λ^{2N}` with no higher-loop
logarithms. This is N=2 one-loop-exactness; it strengthens `AsymptoticMatch` (its `|a|→∞`
consequence). -/
def Instantonic (Λ : ℂ) (N : ℕ) (Fcl F : (Fin r → ℂ) → ℂ) : Prop :=
  ∃ c : ℕ → (Fin r → ℂ) → ℂ, ∀ a : Fin r → ℂ,
    F a - Fcl a - oneLoopPrepotential Λ a = ∑' k : ℕ, c (k + 1) a * (Λ ^ (2 * N)) ^ (k + 1)

/-! ## H0 — the carrier: an N=2 `U(1)^{N-1}` EFT over the Coulomb branch -/

/-- **The base** (H0). The Coulomb branch in gauge-invariant moduli `u ∈ ℂ^r` (Casimirs), with
singular locus `Δ` (the curve discriminant) and smooth part `U`. This *is* the statement that
the IR is a rank-`r` abelian N=2 theory: `Δ`, the metric, and BPS masses live here. -/
structure CoulombBase (r : ℕ) where
  Δ : Set (Fin r → ℂ)
  U : Set (Fin r → ℂ)
  hUopen : IsOpen U
  hUsmooth : U ⊆ Δᶜ

/-- **A sheet** of the cover over a simply-connected open `V ⊆ U`, carrying the single-valued
holomorphic special coordinates `a, a_D` and coupling `τ` of the `U(1)^{N-1}` EFT. -/
structure Sheet (B : CoulombBase r) where
  V : Set (Fin r → ℂ)
  hVopen : IsOpen V
  hVsub : V ⊆ B.U
  hVsc : SimplyConnectedSpace V
  a : (Fin r → ℂ) → (Fin r → ℂ)
  ha : DifferentiableOn ℂ a V
  aD : (Fin r → ℂ) → (Fin r → ℂ)
  haD : DifferentiableOn ℂ aD V
  tau : (Fin r → ℂ) → SiegelUpperHalfSpace r

namespace Sheet

variable {B : CoulombBase r} (s : Sheet B)

/-- **Central charge** `Z_n(u) = nₑ·a(u) + n_m·a_D(u)` — holomorphic on the sheet. -/
noncomputable def centralCharge (u : Fin r → ℂ) (n : ChargeLattice r) : ℂ :=
  (∑ i, (n.1 i : ℂ) * s.a u i) + (∑ i, (n.2 i : ℂ) * s.aD u i)

/-- **BPS mass** `M_n(u) = √2 ‖Z_n(u)‖`. -/
noncomputable def bpsMass (u : Fin r → ℂ) (n : ChargeLattice r) : ℝ :=
  Real.sqrt 2 * ‖s.centralCharge u n‖

/-- **H1 — special geometry.** A holomorphic prepotential `F` with `a_{D,i} = ∂F/∂aᵢ` and
`τ_{ij} = ∂²F/∂aᵢ∂aⱼ` — the full special-Kähler structure in one statement. -/
def SpecialGeometry : Prop :=
  ∃ F : (Fin r → ℂ) → ℂ, DifferentiableOn ℂ F (s.a '' s.V) ∧
    (∀ u ∈ s.V, ∀ i, s.aD u i = partialDeriv F i (s.a u)) ∧
    (∀ u ∈ s.V, ∀ i j, (s.tau u).val i j = partialDeriv2 F i j (s.a u))

/-- **H2 — masslessness.** Charge `n` becomes massless at `u₀ ∈ Δ` iff `Z_n → 0` within the
sheet. -/
def BecomesMasslessAt (u₀ : Fin r → ℂ) (n : ChargeLattice r) : Prop :=
  Tendsto (fun u => s.centralCharge u n) (𝓝[s.V] u₀) (𝓝 0)

/-- **H2 — exact singularity structure.** Massive at smooth points; every chart-boundary point
in `Δ` is where some nonzero charge becomes massless. -/
def SingularitiesAreBPS : Prop :=
  (∀ u ∈ s.V, ∀ n : ChargeLattice r, n ≠ 0 → s.centralCharge u n ≠ 0) ∧
  (∀ u₀ ∈ closure s.V ∩ B.Δ, ∃ n : ChargeLattice r, n ≠ 0 ∧ s.BecomesMasslessAt u₀ n)

/-- **Argyres–Douglas locus (derived).** Boundary points where two *mutually non-local* charges
become massless together. -/
def ArgyresDouglasLocus : Set (Fin r → ℂ) :=
  { u₀ | ∃ n n' : ChargeLattice r, n ≠ 0 ∧ n' ≠ 0 ∧ diracPairing n n' ≠ 0 ∧
        s.BecomesMasslessAt u₀ n ∧ s.BecomesMasslessAt u₀ n' }

/-- **H6 — asymptotic matching, bundled with H1.** The prepotential of H1 has the
non-renormalized weak-coupling form (`Instantonic`); this upgrades "a special-Kähler structure"
to "*the* SW prepotential". -/
def MatchesAsymptotics (Λ : ℂ) (N : ℕ) : Prop :=
  ∃ F Fcl : (Fin r → ℂ) → ℂ, DifferentiableOn ℂ F (s.a '' s.V) ∧
    (∀ u ∈ s.V, ∀ i, s.aD u i = partialDeriv F i (s.a u)) ∧
    (∀ u ∈ s.V, ∀ i j, (s.tau u).val i j = partialDeriv2 F i j (s.a u)) ∧
    Instantonic Λ N Fcl F

end Sheet

/-! ## H3 — Picard–Lefschetz, H4 — duality gluing, H5 — R-symmetry -/

/-- The Picard–Lefschetz reflection in a vanishing charge `n`: `v ↦ v + ⟨v,n⟩ n`. -/
def plReflection (n v : ChargeLattice r) : ChargeLattice r :=
  v + (diracPairing v n) • n

/-- **H3 — Picard–Lefschetz at the generic stratum.** At a generic component of `Δ` the deck
monodromy acts on charges as the reflection in the **vanishing charge** `n` of H2 — so H3 shares
the vanishing `n` with H2. (Skeleton: the family/local-system layer makes the deck action
concrete.) -/
def PicardLefschetzAtGenericStratum {B : CoulombBase r} (s : Sheet B) : Prop :=
  ∀ u₀ ∈ closure s.V ∩ B.Δ, ∀ n : ChargeLattice r,
    s.BecomesMasslessAt u₀ n → ∃ g : ChargeLattice r → ChargeLattice r, g = plReflection n

/-- **H4 — the cover gluing / electric–magnetic duality.** Overlapping sheets differ by a charge
map `g` preserving the Dirac pairing (= `Sp(2r,ℤ)`) under which the central charge is covariant;
hence `|Z|` (mass) and the metric descend to the base. -/
structure Deck {B : CoulombBase r} (s s' : Sheet B) where
  g : ChargeLattice r → ChargeLattice r
  symplectic : ∀ n n', diracPairing (g n) (g n') = diracPairing n n'
  covariant : ∀ u ∈ s.V ∩ s'.V, ∀ n, s'.centralCharge u (g n) = s.centralCharge u n

/-- **BPS mass descends to the base.** A `Deck` gluing makes the mass sheet-independent. -/
theorem Deck.bpsMass_eq {B : CoulombBase r} {s s' : Sheet B} (D : Deck s s')
    {u : Fin r → ℂ} (hu : u ∈ s.V ∩ s'.V) (n : ChargeLattice r) :
    s'.bpsMass u (D.g n) = s.bpsMass u n := by
  unfold Sheet.bpsMass; rw [D.covariant u hu n]

/-- **H5 — R-symmetry.** A `ℤ_{2N}` action on the moduli preserving `Δ`. Skeleton predicate. -/
def RSymmetry (B : CoulombBase r) (N : ℕ) : Prop :=
  ∃ ω : (Fin r → ℂ) → (Fin r → ℂ), (∀ u, ω^[2 * N] u = u) ∧ ω '' B.Δ = B.Δ

/-! ## The N=2 `U(1)^{N-1}` effective theory, and the headline goals -/

/-- **A Seiberg–Witten effective theory** on a sheet: H1 (special geometry), H2 (singularities),
H3 (Picard–Lefschetz), H6 (matching) on the sheet, and H5 (R-symmetry) on the base. H4 (duality)
relates sheets. -/
structure IsSWEffectiveTheory {B : CoulombBase r} (s : Sheet B) (Λ : ℂ) (N : ℕ) : Prop where
  specialGeometry : s.SpecialGeometry
  singularities : s.SingularitiesAreBPS
  picardLefschetz : PicardLefschetzAtGenericStratum s
  matching : s.MatchesAsymptotics Λ N
  rSymmetry : RSymmetry B N

/-- **(3) — classical Coulomb branch.** A regular adjoint vev of `SU(N)` breaks the gauge group
to its maximal torus `U(1)^{N-1}` and the classical Coulomb branch is the Cartan mod Weyl, of
complex dimension `N − 1`. The genuine content is the centralizer theorem (regular semisimple
element ⇒ maximal torus), *derivable* from the classical scalar potential; here we record only
the dimension/rank fact `dim_ℂ ℂ^{N-1} = N − 1`, with the full Higgsing derivation a future
Lie-theory item. (The quantum corrections — the metric, `Δ` as the discriminant — are the
separate headline goal.) -/
theorem coulombBranch_classical (N : ℕ) :
    Module.finrank ℂ (Fin (N - 1) → ℂ) = N - 1 := by
  rw [Module.finrank_pi, Fintype.card_fin]

/-- **GOAL — uniqueness up to duality** (period-map rigidity; *not* an axiom). Two SW effective
theories over the same base are related by an `Sp(2r,ℤ)` duality `Deck`. A *consequence* of
H1–H6, hence a goal to prove. **Proved for SU(2)** in `sw_su2_unique`; general rank open. -/
theorem sw_effective_theory_unique_up_to_duality {B : CoulombBase r} (s s' : Sheet B)
    {Λ : ℂ} {N : ℕ} (h : IsSWEffectiveTheory s Λ N) (h' : IsSWEffectiveTheory s' Λ N) :
    Nonempty (Deck s s') := by
  sorry

/-- **GOAL — existence.** The SW curve `y² = P_N² − Λ^{2N}`, via its period geometry, furnishes
a sheet satisfying the six hypotheses. A goal to prove (the data is the periods of the curve —
Phase 2); the `τ ∈ Siegel` half is already a theorem (`sw_coupling_mem_siegel`). -/
theorem sw_curve_admits_effective_theory {N : ℕ} (P : Polynomial ℂ) (Λ : ℂ)
    (hPdeg : P.natDegree = N) (hN : 2 ≤ N)
    (hsf : Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * N)))) :
    ∃ (B : CoulombBase (N - 1)) (s : Sheet B), IsSWEffectiveTheory s Λ N := by
  sorry

end SeibergWitten.Physics
