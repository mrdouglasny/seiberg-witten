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

/-! ### Dirac-pairing algebra and the Picard–Lefschetz transvection

These live here (with `diracPairing`) so that H3 and the family/monodromy layer share **one**
`transvection`, and H3's reflection is provably symplectic. -/

theorem diracPairing_self (v : ChargeLattice r) : diracPairing v v = 0 := by
  unfold diracPairing
  rw [sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem diracPairing_antisymm (a b : ChargeLattice r) :
    diracPairing a b = -diracPairing b a := by
  unfold diracPairing
  have h1 : ∑ i, a.1 i * b.2 i = ∑ i, b.2 i * a.1 i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : ∑ i, a.2 i * b.1 i = ∑ i, b.1 i * a.2 i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1, h2]; ring

theorem diracPairing_add_left (a b c : ChargeLattice r) :
    diracPairing (a + b) c = diracPairing a c + diracPairing b c := by
  simp only [diracPairing, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

theorem diracPairing_smul_left (c : ℤ) (a b : ChargeLattice r) :
    diracPairing (c • a) b = c * diracPairing a b := by
  simp only [diracPairing, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub]

theorem diracPairing_add_right (a b c : ChargeLattice r) :
    diracPairing a (b + c) = diracPairing a b + diracPairing a c := by
  rw [diracPairing_antisymm a (b + c), diracPairing_add_left,
      diracPairing_antisymm b a, diracPairing_antisymm c a]; ring

theorem diracPairing_smul_right (c : ℤ) (a b : ChargeLattice r) :
    diracPairing a (c • b) = c * diracPairing a b := by
  rw [diracPairing_antisymm a (c • b), diracPairing_smul_left, diracPairing_antisymm a b]
  ring

/-- A charge-lattice map is **symplectic** if it preserves the Dirac pairing (lands in
`Sp(2r,ℤ)`). -/
def IsSymplectic (f : ChargeLattice r → ChargeLattice r) : Prop :=
  ∀ v w, diracPairing (f v) (f w) = diracPairing v w

/-- **Picard–Lefschetz transvection** of a vanishing charge `γ`: `T_γ v = v + ⟨v,γ⟩ γ` — the
local monodromy on the charge lattice around a singularity where `γ` goes massless. This is the
reflection used in H3 and in the family monodromy layer (`Monodromy.lean`). -/
def transvection (γ v : ChargeLattice r) : ChargeLattice r :=
  v + diracPairing v γ • γ

/-- A Picard–Lefschetz transvection preserves the Dirac pairing. -/
theorem transvection_diracPairing (γ v w : ChargeLattice r) :
    diracPairing (transvection γ v) (transvection γ w) = diracPairing v w := by
  simp only [transvection, diracPairing_add_left, diracPairing_add_right,
    diracPairing_smul_left, diracPairing_smul_right, diracPairing_self, mul_zero, add_zero]
  rw [diracPairing_antisymm γ w]; ring

/-- Every Picard–Lefschetz transvection is symplectic — so H3's monodromy reflection lands in
`Sp(2r,ℤ)`. -/
theorem transvection_isSymplectic (γ : ChargeLattice r) :
    IsSymplectic (transvection γ) :=
  fun v w => transvection_diracPairing γ v w

/-! ## Prepotential derivatives -/

/-- `∂F/∂xᵢ` at `x`, for a holomorphic prepotential `F : ℂ^r → ℂ`. -/
noncomputable def partialDeriv (F : (Fin r → ℂ) → ℂ) (i : Fin r) (x : Fin r → ℂ) : ℂ :=
  fderiv ℂ F x (Pi.single i 1)

/-- `∂²F/∂xᵢ∂xⱼ` at `x`. -/
noncomputable def partialDeriv2 (F : (Fin r → ℂ) → ℂ) (i j : Fin r) (x : Fin r → ℂ) : ℂ :=
  partialDeriv (fun y => partialDeriv F i y) j x

/-! ## H6 — one-loop prepotential and the non-renormalization input -/

/-- The `N = r+1` eigenvalues of the adjoint scalar, reconstructed traceless from the `r`
special coordinates: `(a₀, …, a_{r-1}, −∑ aᵢ)`. The W-bosons run over their *differences* (the
roots), which is why the one-loop sum below is over `Fin (r+1)` and is nonzero already for
SU(2) (`r = 1`: the single root `a₀ − (−a₀) = 2a₀`). -/
noncomputable def eigenvalues (a : Fin r → ℂ) : Fin (r + 1) → ℂ :=
  Fin.snoc a (-(∑ i, a i))

/-- **One-loop prepotential** — the charged W-boson contributions, summed over the **roots**
`αᵢⱼ·a = eᵢ − eⱼ` (differences of eigenvalues):
`F₁(a) = (i/8π) ∑_{i≠j} (eᵢ−eⱼ)² log((eᵢ−eⱼ)²/Λ²)`. Its Hessian is the one-loop running of the
`U(1)^{N-1}` couplings. (Nonzero for SU(2), unlike a sum over the `r` coordinates alone.) -/
noncomputable def oneLoopPrepotential (Λ : ℂ) (a : Fin r → ℂ) : ℂ :=
  (Complex.I / (8 * (Real.pi : ℂ))) *
    ∑ i, ∑ j, if i = j then 0 else
      (eigenvalues a i - eigenvalues a j) ^ 2 *
        Complex.log ((eigenvalues a i - eigenvalues a j) ^ 2 / Λ ^ 2)

/-- Classical prepotential `F_cl(a) = ½ ∑ aᵢ²` (up to the bare coupling `τ₀`). -/
noncomputable def classicalPrepotential (a : Fin r → ℂ) : ℂ := (1 / 2) * ∑ i, (a i) ^ 2

/-- **Asymptotic matching (weak form).** `F − (F_cl + F₁) → 0` as `|a| → ∞` — the instanton
corrections vanish at weak coupling. The classical part is *fixed* (`classicalPrepotential`). -/
def AsymptoticMatch (Λ : ℂ) (F : (Fin r → ℂ) → ℂ) : Prop :=
  Tendsto (fun a => F a - (classicalPrepotential a + oneLoopPrepotential Λ a))
    (Filter.cocompact (Fin r → ℂ)) (𝓝 0)

/-- **H6 — non-renormalization (sharp form).** With the classical part *fixed* and `Λ ≠ 0`, the
deviation of `F` from classical + one-loop is **purely instantonic**: a power series in the
instanton factor `Λ^{2N}` with **holomorphic** coefficients and no higher-loop logarithms. The
fixed `F_cl` and the holomorphy of the coefficients are what keep this from being vacuous (a
free `F_cl`/coefficient could absorb any `F`). N=2 one-loop-exactness; strengthens
`AsymptoticMatch`. -/
def Instantonic (Λ : ℂ) (N : ℕ) (F : (Fin r → ℂ) → ℂ) : Prop :=
  Λ ≠ 0 ∧ ∃ c : ℕ → (Fin r → ℂ) → ℂ, (∀ k, Differentiable ℂ (c k)) ∧
    ∀ a : Fin r → ℂ,
      F a - classicalPrepotential a - oneLoopPrepotential Λ a
        = ∑' k : ℕ, c (k + 1) a * (Λ ^ (2 * N)) ^ (k + 1)

/-! ## H0 — the carrier: an N=2 `U(1)^{N-1}` EFT over the Coulomb branch -/

/-- **The base** (H0). The Coulomb branch in gauge-invariant moduli `u ∈ ℂ^r` (Casimirs), with
singular locus `Δ` (the curve discriminant) and smooth part `U`. This *is* the statement that
the IR is a rank-`r` abelian N=2 theory: `Δ`, the metric, and BPS masses live here. -/
structure CoulombBase (r : ℕ) where
  Δ : Set (Fin r → ℂ)
  U : Set (Fin r → ℂ)
  hUopen : IsOpen U
  /-- the smooth locus is *exactly* the complement of the singular locus (so `Δ` is closed). -/
  hUsmooth : U = Δᶜ

/-- **A sheet** of the cover over a simply-connected open `V ⊆ U`, carrying the single-valued
holomorphic special coordinates `a, a_D` and coupling `τ` of the `U(1)^{N-1}` EFT. -/
structure Sheet (B : CoulombBase r) where
  V : Set (Fin r → ℂ)
  hVopen : IsOpen V
  hVsub : V ⊆ B.U
  hVsc : SimplyConnectedSpace V
  a : (Fin r → ℂ) → (Fin r → ℂ)
  ha : DifferentiableOn ℂ a V
  /-- `a` is a local biholomorphism (good coordinates): injective on the chart, so with
  holomorphy the inverse is holomorphic and `∂/∂a` is well-defined. -/
  haInj : Set.InjOn a V
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
  ∃ F : (Fin r → ℂ) → ℂ, ContDiffOn ℂ 2 F (s.a '' s.V) ∧
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
  { u₀ | u₀ ∈ closure s.V ∩ B.Δ ∧ ∃ n n' : ChargeLattice r, n ≠ 0 ∧ n' ≠ 0 ∧
        diracPairing n n' ≠ 0 ∧ s.BecomesMasslessAt u₀ n ∧ s.BecomesMasslessAt u₀ n' }

/-- **H6 — asymptotic matching, bundled with H1.** The prepotential of H1 has the
non-renormalized weak-coupling form (`Instantonic`); this upgrades "a special-Kähler structure"
to "*the* SW prepotential". -/
def MatchesAsymptotics (Λ : ℂ) (N : ℕ) : Prop :=
  ∃ F : (Fin r → ℂ) → ℂ, ContDiffOn ℂ 2 F (s.a '' s.V) ∧
    (∀ u ∈ s.V, ∀ i, s.aD u i = partialDeriv F i (s.a u)) ∧
    (∀ u ∈ s.V, ∀ i j, (s.tau u).val i j = partialDeriv2 F i j (s.a u)) ∧
    Instantonic Λ N F

end Sheet

/-! ## H3 — Picard–Lefschetz, H4 — duality gluing, H5 — R-symmetry -/

/-- **H4 — the cover gluing / electric–magnetic duality.** Overlapping sheets differ by a
duality frame change `g`: a **ℤ-linear automorphism of the charge lattice** preserving the Dirac
pairing (i.e. an element of `Sp(2r,ℤ)`), under which the central charge is covariant. Hence
`|Z|` (mass) and the metric descend to the base. -/
structure Deck {B : CoulombBase r} (s s' : Sheet B) where
  g : ChargeLattice r ≃ₗ[ℤ] ChargeLattice r
  symplectic : ∀ n n', diracPairing (g n) (g n') = diracPairing n n'
  covariant : ∀ u ∈ s.V ∩ s'.V, ∀ n, s'.centralCharge u (g n) = s.centralCharge u n

/-- **BPS mass descends to the base.** A `Deck` gluing makes the mass sheet-independent. -/
theorem Deck.bpsMass_eq {B : CoulombBase r} {s s' : Sheet B} (D : Deck s s')
    {u : Fin r → ℂ} (hu : u ∈ s.V ∩ s'.V) (n : ChargeLattice r) :
    s'.bpsMass u (D.g n) = s.bpsMass u n := by
  unfold Sheet.bpsMass; rw [D.covariant u hu n]

/-- **H3 — Picard–Lefschetz at the generic stratum.** At a generic component of `Δ` the
monodromy around it — realized as an *actual* deck transformation `D : Deck s s'` to an adjacent
sheet — acts on the charge lattice as the reflection in the **vanishing charge** `n` of H2. This
forces the reflection to be symplectic (it is) and the central charge to transform covariantly
(a real constraint on the periods), unlike a vacuous `∃ g, g = transvection n`. The reflection
is the shared `transvection` (proved symplectic, `transvection_isSymplectic`). -/
def PicardLefschetzAtGenericStratum {B : CoulombBase r} (s : Sheet B) : Prop :=
  ∀ u₀ ∈ closure s.V ∩ B.Δ, ∀ n : ChargeLattice r, n ≠ 0 → s.BecomesMasslessAt u₀ n →
    ∃ (s' : Sheet B) (D : Deck s s'), ⇑D.g = transvection n

/-- **H5 — R-symmetry.** A `ℤ_{2N}` action on the moduli: a bijection of **exact order `2N`**
(not the identity) preserving `Δ` — the anomalous `U(1)_R → ℤ_{2N}` fixing the positions of the
singularities. Order-exactly-`2N` rules out the vacuous `ω = id`. -/
def RSymmetry (B : CoulombBase r) (N : ℕ) : Prop :=
  ∃ ω : (Fin r → ℂ) → (Fin r → ℂ), Function.Bijective ω ∧ ω^[2 * N] = id ∧
    (∀ k, 0 < k → k < 2 * N → ω^[k] ≠ id) ∧ ω '' B.Δ = B.Δ

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

/-- **An atlas for an SW effective theory** (this is where H4 lives). A family of sheets
**covering** the smooth base `B.U`, each a single-sheet effective theory, with overlapping
sheets **glued** by an `Sp(2r,ℤ)` deck transformation. The global object the physics describes —
the duality gluing (H4) is *part of the theory*, not merely a relation between two isolated
sheets. -/
structure SWAtlas (B : CoulombBase r) (Λ : ℂ) (N : ℕ) where
  ι : Type
  sheets : ι → Sheet B
  covers : B.U ⊆ ⋃ i, (sheets i).V
  isSW : ∀ i, IsSWEffectiveTheory (sheets i) Λ N
  glued : ∀ i j, ((sheets i).V ∩ (sheets j).V).Nonempty → Nonempty (Deck (sheets i) (sheets j))

/-- **(3) — classical Coulomb branch.** A regular adjoint vev of `SU(N)` breaks the gauge group
to its maximal torus `U(1)^{N-1}` and the classical Coulomb branch is the Cartan mod Weyl, of
complex dimension `N − 1`. The genuine content is the centralizer theorem (regular semisimple
element ⇒ maximal torus), *derivable* from the classical scalar potential; here we record only
the dimension/rank fact `dim_ℂ ℂ^{N-1} = N − 1`, with the full Higgsing derivation a future
Lie-theory item. (The quantum corrections — the metric, `Δ` as the discriminant — are the
separate headline goal.) -/
theorem coulombBranchDim (N : ℕ) :
    Module.finrank ℂ (Fin (N - 1) → ℂ) = N - 1 := by
  rw [Module.finrank_pi, Fintype.card_fin]

/-! **Headline — uniqueness up to duality (sheet- and atlas-level).** A mathematical *consequence*
of H1–H6, not an axiom. Stated and **proved** (no `sorry`) in `Physics/PeriodLayer.lean` as
`sw_effective_theory_unique_up_to_duality` / `sw_unique_up_to_duality`, from the physics postulates
plus the period-level math axiom `swPeriodLayer` (on a *connected* chart overlap). The rank-1 case
is `SU2.sw_su2_unique`, resting only on the `B.2` covering/lift axioms + the monodromy input. -/

/-- The monic degree-`N` polynomial with subleading coefficients the moduli `u` (the traceless
`SU(N)` Casimirs): `X^N + ∑_{i<N-1} uᵢ Xⁱ`. -/
noncomputable def swModuliPoly (N : ℕ) (u : Fin (N - 1) → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ N + ∑ i : Fin (N - 1), Polynomial.C (u i) * Polynomial.X ^ (i : ℕ)

/-- The SW curve polynomial `swModuliPoly² − Λ^{2N}` at modulus `u`. -/
noncomputable def swCurvePoly (N : ℕ) (Λ : ℂ) (u : Fin (N - 1) → ℂ) : Polynomial ℂ :=
  swModuliPoly N u ^ 2 - Polynomial.C (Λ ^ (2 * N))

/-- The modulus point of a polynomial `P` — its subleading coefficients. -/
noncomputable def swModulus (N : ℕ) (P : Polynomial ℂ) : Fin (N - 1) → ℂ := fun i => P.coeff i

/-! **Headline — existence (tied to the curve `P`).** That the SW curve `y² = P² − Λ^{2N}` realizes
an effective theory whose singular locus is exactly the discriminant locus
`{u | ¬ Squarefree (swCurvePoly N Λ u)}`. Stated and **proved** (no `sorry`) as
`sw_curve_admits_effective_theory` in `Physics/PeriodLayer.lean`, from the physics postulates +
`swPeriodLayer` (with `P` monic, degree `N`, trace-free — the `SU(N)` slice). -/

end SeibergWitten.Physics
