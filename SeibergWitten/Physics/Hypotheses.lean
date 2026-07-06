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

1. **H1 — special geometry** (`PeriodChart.SpecialGeometry`): a holomorphic prepotential `F` with
   `a_D = ∂F/∂a`, `τ = ∂²F/∂a²`.
2. **H2 — exact singularity structure** (`PeriodChart.PeriodsDegenerateOnBoundary`): massive at
   smooth points
   (`Z_n ≠ 0`); every boundary point in `Δ` is where some BPS charge becomes massless
   (`Z_n → 0`).
3. **H3 — Picard–Lefschetz** (`PicardLefschetzAtGenericStratum`): the local monodromy is the
   reflection `v ↦ v + ⟨v,n⟩ n` in the **same vanishing charge `n`** of H2.
4. **H4 — electric–magnetic duality** (`SymplecticReframing`): sheets glue by a
   Dirac-pairing-preserving
   (= `Sp(2r,ℤ)`) charge action with covariant central charge; mass and metric descend.
5. **H5 — R-symmetry** (`HasFiniteOrderAutomorphism`): a `ℤ_{2N}` action on the moduli fixing
   the positions of
   `Δ`.
6. **H6 — asymptotic matching / non-renormalization**
   (`PeriodChart.HasPrescribedAsymptotics`, `Instantonic`):
   `F` matches the weak-coupling one-loop form, the remainder purely instantonic.

The headline implications (existence; uniqueness up to `Sp(2r,ℤ)`) are *mathematical
consequences*, stated as **goals** (`theorem … := sorry`), not axioms. Argyres–Douglas points
are **derived** (`NonLocalDegenerationLocus`). Tracked in `AXIOM_AUDIT.md`.

References: Seiberg–Witten, *Nucl. Phys.* B426 (1994) [hep-th/9407087]; B431 (1994); KLYT,
*Phys. Lett.* B344 (1995); Argyres–Faraggi, *PRL* 74 (1995); Argyres–Douglas, *Nucl. Phys.*
B448 (1995); Lerche, hep-th/9611190.
-/
import Mathlib

open Complex Filter Topology

namespace SeibergWitten.Physics

variable {r : ℕ}

/-! ## Charge lattice and Dirac pairing -/

/-- The lattice of electric–magnetic charges `(nₑ, n_m) ∈ ℤ^r × ℤ^r` of the low-energy
`U(1)^r` gauge theory (`r = N − 1`). Over `U = ℂ^r ∖ Δ` it is the fibre of a local system. -/
abbrev CycleLattice (r : ℕ) : Type := (Fin r → ℤ) × (Fin r → ℤ)

/-- **Dirac–Schwinger–Zwanziger pairing** `⟨(eₐ,mₐ),(e_b,m_b)⟩ = eₐ·m_b − mₐ·e_b`. Two charges
are **mutually non-local** iff this is nonzero. The antisymmetric form preserved by `Sp(2r,ℤ)`. -/
def intersectionForm {r : ℕ} (n n' : CycleLattice r) : ℤ :=
  (∑ i, n.1 i * n'.2 i) - (∑ i, n.2 i * n'.1 i)

/-! ### Dirac-pairing algebra and the Picard–Lefschetz transvection

These live here (with `intersectionForm`) so that H3 and the family/monodromy layer share **one**
`transvection`, and H3's reflection is provably symplectic. -/

theorem intersectionForm_self (v : CycleLattice r) : intersectionForm v v = 0 := by
  unfold intersectionForm
  rw [sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem intersectionForm_antisymm (a b : CycleLattice r) :
    intersectionForm a b = -intersectionForm b a := by
  unfold intersectionForm
  have h1 : ∑ i, a.1 i * b.2 i = ∑ i, b.2 i * a.1 i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : ∑ i, a.2 i * b.1 i = ∑ i, b.1 i * a.2 i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1, h2]; ring

theorem intersectionForm_add_left (a b c : CycleLattice r) :
    intersectionForm (a + b) c = intersectionForm a c + intersectionForm b c := by
  simp only [intersectionForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

theorem intersectionForm_smul_left (c : ℤ) (a b : CycleLattice r) :
    intersectionForm (c • a) b = c * intersectionForm a b := by
  simp only [intersectionForm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub]

theorem intersectionForm_add_right (a b c : CycleLattice r) :
    intersectionForm a (b + c) = intersectionForm a b + intersectionForm a c := by
  rw [intersectionForm_antisymm a (b + c), intersectionForm_add_left,
      intersectionForm_antisymm b a, intersectionForm_antisymm c a]; ring

theorem intersectionForm_smul_right (c : ℤ) (a b : CycleLattice r) :
    intersectionForm a (c • b) = c * intersectionForm a b := by
  rw [intersectionForm_antisymm a (c • b), intersectionForm_smul_left,
    intersectionForm_antisymm a b]
  ring

/-- A charge-lattice map is **symplectic** if it preserves the Dirac pairing (lands in
`Sp(2r,ℤ)`). -/
def IsSymplectic (f : CycleLattice r → CycleLattice r) : Prop :=
  ∀ v w, intersectionForm (f v) (f w) = intersectionForm v w

/-- **Picard–Lefschetz transvection** of a vanishing charge `γ`: `T_γ v = v + ⟨v,γ⟩ γ` — the
local monodromy on the charge lattice around a singularity where `γ` goes massless. This is the
reflection used in H3 and in the family monodromy layer (`Monodromy.lean`). -/
def transvection (γ v : CycleLattice r) : CycleLattice r :=
  v + intersectionForm v γ • γ

/-- A Picard–Lefschetz transvection preserves the Dirac pairing. -/
theorem transvection_diracPairing (γ v w : CycleLattice r) :
    intersectionForm (transvection γ v) (transvection γ w) = intersectionForm v w := by
  simp only [transvection, intersectionForm_add_left, intersectionForm_add_right,
    intersectionForm_smul_left, intersectionForm_smul_right, intersectionForm_self, mul_zero,
    add_zero]
  rw [intersectionForm_antisymm γ w]; ring

/-- Every Picard–Lefschetz transvection is symplectic — so H3's monodromy reflection lands in
`Sp(2r,ℤ)`. -/
theorem transvection_isSymplectic (γ : CycleLattice r) :
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
instanton factor `Λ^{2N}` whose coefficients are holomorphic and **homogeneous of the scaling
weight `2 − 2Nk`** in `a`.

**Correction (2026-07-05, author-caught vacuity — `DIFFICULT_POINTS.md` B6).** An earlier form
omitted the homogeneity clause, and was *vacuous*: at fixed `Λ` the single coefficient
`c₁(a) := (F(a) − F_cl(a) − F₁(Λ,a))/Λ^{2N}` absorbs **any** differentiable `F` — holomorphy of
the coefficients constrains nothing, because at fixed `Λ` "the coefficients do not depend on
`Λ`" has no content unless expressed differently. The scale covariance of the family
(`a ↦ ta`, `Λ ↦ tΛ`, `F ↦ t²F`) converts `Λ`-independence of the `k`-instanton coefficient into
the **weighted homogeneity** `c_k(t·a) = t^{2−2Nk}·c_k(a)` — a fixed-`Λ` statement, and a
genuinely restrictive one: only remainders decomposing into homogeneous pieces of the discrete
degrees `2 − 2Nk` qualify (e.g. an `a³` deviation at `N = 2` fits no `k`). N=2
one-loop-exactness; strengthens `AsymptoticMatch`. -/
def Instantonic (Λ : ℂ) (N : ℕ) (F : (Fin r → ℂ) → ℂ) : Prop :=
  Λ ≠ 0 ∧ ∃ c : ℕ → (Fin r → ℂ) → ℂ, (∀ k, Differentiable ℂ (c k)) ∧
    (∀ k : ℕ, ∀ t : ℂ, t ≠ 0 → ∀ a : Fin r → ℂ,
      c k (t • a) = t ^ ((2 : ℤ) - 2 * (N : ℤ) * (k : ℤ)) * c k a) ∧
    ∀ a : Fin r → ℂ,
      F a - classicalPrepotential a - oneLoopPrepotential Λ a
        = ∑' k : ℕ, c (k + 1) a * (Λ ^ (2 * N)) ^ (k + 1)

/-! ## H7 — spurionic `U(1)_R` covariance of the `Λ`-family

H0–H6 constrain the effective theory at FIXED `Λ`. H7 is the family-level statement
tying different `Λ` together — dimensional transmutation plus θ-angle periodicity
realized through the anomaly — of which H5 and H6's homogeneity clause are the
fixed-`Λ` shadows, and `RSpurionCovariant` (SingularityCount.lean) is the curve-level
shadow (pending the curve-reconstruction bridge, like all the transcriptions):

* **scale**: `Λ` is the only scale, so rescaling it is an RG transformation —
  `F(tΛ)(t·a) = t²·F(Λ)(a)` (mass dimensions `[a] = 1`, `[F] = 2`);
* **theta_shift**: for any `2N`-th root of unity `ζ`, `Λ ↦ ζΛ` preserves the instanton
  factor `Λ^{2N}` — for the primitive root this is the θ-angle shift `θ ↦ θ + 2π`
  (`arg Λ^{2N} = θ`), a symmetry by instanton-number quantization, with the anomaly
  coefficient one-loop exact (Adler–Bardeen). At the prepotential level it holds **up
  to an integer electric–magnetic frame shift** (the Witten effect): `F` shifts by a
  quadratic form `½ aᵀBa` with `B` an **integer symmetric matrix, constant across the
  family** — the existential sits OUTSIDE the `Λ, a` quantifiers (the B6 lesson: a
  per-`Λ` shift could absorb anything; a fixed integer matrix cannot). The
  weak-coupling-regularity face of the family is already carried by H6
  (`Instantonic`'s series form).

Consequences proved here: the instanton remainder `F − F_cl − F₁` is weighted-
homogeneous ACROSS the family (`instanton_remainder_covariant`) — H6's homogeneity
clause is the fixed-`Λ` shadow of this; the classical and one-loop pieces are exactly
covariant (`classicalPrepotential_smul`, `oneLoopPrepotential_smul` — the log enters
through the scale-invariant ratio `(eᵢ−eⱼ)²/Λ²`, so no branch issues). -/

/-- The classical prepotential is quadratic: exact scale covariance. -/
theorem classicalPrepotential_smul (t : ℂ) (a : Fin r → ℂ) :
    classicalPrepotential (t • a) = t ^ 2 * classicalPrepotential a := by
  simp only [classicalPrepotential, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum]
  ring

/-- Eigenvalues are linear in the Cartan coordinates. -/
theorem eigenvalues_smul (t : ℂ) (a : Fin r → ℂ) :
    eigenvalues (t • a) = t • eigenvalues a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [eigenvalues, Fin.snoc_last, Finset.mul_sum, mul_neg]
  · simp [eigenvalues, Fin.snoc_castSucc]

/-- The one-loop prepotential is exactly scale covariant: the logarithm enters only
through the scale-invariant ratio `(eᵢ−eⱼ)²/Λ²`. -/
theorem oneLoopPrepotential_smul {t : ℂ} (ht : t ≠ 0) (Λ : ℂ) (a : Fin r → ℂ) :
    oneLoopPrepotential (t * Λ) (t • a) = t ^ 2 * oneLoopPrepotential Λ a := by
  have hlog : ∀ x : ℂ, (t * x) ^ 2 / (t * Λ) ^ 2 = x ^ 2 / Λ ^ 2 := by
    intro x
    rw [mul_pow, mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 ht)]
  simp only [oneLoopPrepotential, eigenvalues_smul, Pi.smul_apply, smul_eq_mul,
    ← mul_sub]
  simp only [hlog]
  simp only [mul_pow, Finset.mul_sum, mul_ite, mul_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · ring

/-- **H7 — spurionic `U(1)_R` covariance of the `Λ`-family** (*dimensional
transmutation + θ-angle periodicity through the anomaly; the Witten-effect frame shift
is an integer symmetric matrix constant across the family*). See the section header for
the physics; H5 and H6's homogeneity clause are its fixed-`Λ` shadows, and
`RSpurionCovariant` is its curve-level shadow. -/
structure SpurionCovariantFamily (N : ℕ) (F : ℂ → (Fin r → ℂ) → ℂ) : Prop where
  scale : ∀ (t Λ : ℂ), t ≠ 0 → ∀ a : Fin r → ℂ, F (t * Λ) (t • a) = t ^ 2 * F Λ a
  theta_shift : ∀ ζ : ℂ, ζ ^ (2 * N) = 1 →
    ∃ B : Matrix (Fin r) (Fin r) ℤ, B.IsSymm ∧
      ∀ (Λ : ℂ) (a : Fin r → ℂ),
        F (ζ * Λ) a = F Λ a + (1 / 2) * ∑ i, ∑ j, (B i j : ℂ) * a i * a j

/-- **H6's homogeneity clause is H7's shadow**: for a spurion-covariant family the
instanton remainder `F − F_cl − F₁` is weighted-homogeneous across the family. -/
theorem instanton_remainder_covariant {N : ℕ} {F : ℂ → (Fin r → ℂ) → ℂ}
    (h : SpurionCovariantFamily N F) {t : ℂ} (ht : t ≠ 0) (Λ : ℂ) (a : Fin r → ℂ) :
    F (t * Λ) (t • a) - classicalPrepotential (t • a)
        - oneLoopPrepotential (t * Λ) (t • a)
      = t ^ 2 * (F Λ a - classicalPrepotential a - oneLoopPrepotential Λ a) := by
  rw [h.scale t Λ ht a, classicalPrepotential_smul, oneLoopPrepotential_smul ht]
  ring

/-- Non-vacuity: the classical family satisfies H7 (with zero frame shift). -/
theorem spurionCovariantFamily_classical (N : ℕ) :
    SpurionCovariantFamily (r := r) N (fun _ a => classicalPrepotential a) where
  scale t Λ ht a := by rw [classicalPrepotential_smul]
  theta_shift ζ _ :=
    ⟨0, by simp [Matrix.IsSymm], fun Λ a => by simp⟩

/-! ## H0 — the carrier: an N=2 `U(1)^{N-1}` EFT over the Coulomb branch -/

/-- **The base** (H0). The Coulomb branch in gauge-invariant moduli `u ∈ ℂ^r` (Casimirs), with
singular locus `Δ` (the curve discriminant) and smooth part `U`. This *is* the statement that
the IR is a rank-`r` abelian N=2 theory: `Δ`, the metric, and BPS masses live here. -/
structure PeriodBase (r : ℕ) where
  Δ : Set (Fin r → ℂ)
  U : Set (Fin r → ℂ)
  hUopen : IsOpen U
  /-- the smooth locus is *exactly* the complement of the singular locus (so `Δ` is closed). -/
  hUsmooth : U = Δᶜ

/-- **The Siegel upper half space** of genus `g`: symmetric complex `g×g` matrices with
positive-definite imaginary part — the codomain of the effective coupling `τ`. (Inlined
from the former `jacobian-challenge` dependency, 2026-07-06; the higher-genus
Riemann-surface layer that consumed the rest of that library now lives, unbuilt, in
`HigherGenus/`.) -/
def SiegelUpperHalfSpace (g : ℕ) : Type :=
  { τ : Matrix (Fin g) (Fin g) ℂ // τ.IsSymm ∧ (τ.map Complex.im).PosDef }

namespace SiegelUpperHalfSpace

theorem isSymm {g : ℕ} (τ : SiegelUpperHalfSpace g) : τ.val.IsSymm := τ.2.1

theorem imPosDef {g : ℕ} (τ : SiegelUpperHalfSpace g) :
    (τ.val.map Complex.im).PosDef := τ.2.2

theorem ext {g : ℕ} {τ τ' : SiegelUpperHalfSpace g} (h : τ.val = τ'.val) : τ = τ' :=
  Subtype.ext h

end SiegelUpperHalfSpace

/-- **A sheet** of the cover over a simply-connected open `V ⊆ U`, carrying the single-valued
holomorphic special coordinates `a, a_D` and coupling `τ` of the `U(1)^{N-1}` EFT. -/
structure PeriodChart (B : PeriodBase r) where
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

namespace PeriodChart

variable {B : PeriodBase r} (s : PeriodChart B)

/-- **Central charge** `Z_n(u) = nₑ·a(u) + n_m·a_D(u)` — holomorphic on the sheet. -/
noncomputable def periodCombination (u : Fin r → ℂ) (n : CycleLattice r) : ℂ :=
  (∑ i, (n.1 i : ℂ) * s.a u i) + (∑ i, (n.2 i : ℂ) * s.aD u i)

/-- **BPS mass** `M_n(u) = √2 ‖Z_n(u)‖`. -/
noncomputable def periodNorm (u : Fin r → ℂ) (n : CycleLattice r) : ℝ :=
  Real.sqrt 2 * ‖s.periodCombination u n‖

/-- **H1 — special geometry.** A holomorphic prepotential `F` with `a_{D,i} = ∂F/∂aᵢ` and
`τ_{ij} = ∂²F/∂aᵢ∂aⱼ` — the full special-Kähler structure in one statement. -/
def SpecialGeometry : Prop :=
  ∃ F : (Fin r → ℂ) → ℂ, ContDiffOn ℂ 2 F (s.a '' s.V) ∧
    (∀ u ∈ s.V, ∀ i, s.aD u i = partialDeriv F i (s.a u)) ∧
    (∀ u ∈ s.V, ∀ i j, (s.tau u).val i j = partialDeriv2 F i j (s.a u))

/-- **H2 — masslessness.** Charge `n` becomes massless at `u₀ ∈ Δ` iff `Z_n → 0` within the
sheet. -/
def PeriodVanishesAt (u₀ : Fin r → ℂ) (n : CycleLattice r) : Prop :=
  Tendsto (fun u => s.periodCombination u n) (𝓝[s.V] u₀) (𝓝 0)

/-- **H2 — exact singularity structure.** Massive at smooth points; every chart-boundary point
in `Δ` is where some nonzero charge becomes massless. -/
def PeriodsDegenerateOnBoundary : Prop :=
  (∀ u ∈ s.V, ∀ n : CycleLattice r, n ≠ 0 → s.periodCombination u n ≠ 0) ∧
  (∀ u₀ ∈ closure s.V ∩ B.Δ, ∃ n : CycleLattice r, n ≠ 0 ∧ s.PeriodVanishesAt u₀ n)

/-- **Argyres–Douglas locus (derived).** Boundary points where two *mutually non-local* charges
become massless together. -/
def NonLocalDegenerationLocus : Set (Fin r → ℂ) :=
  { u₀ | u₀ ∈ closure s.V ∩ B.Δ ∧ ∃ n n' : CycleLattice r, n ≠ 0 ∧ n' ≠ 0 ∧
        intersectionForm n n' ≠ 0 ∧ s.PeriodVanishesAt u₀ n ∧ s.PeriodVanishesAt u₀ n' }

/-- **H6 — asymptotic matching, bundled with H1.** The prepotential of H1 has the
non-renormalized weak-coupling form (`Instantonic`); this upgrades "a special-Kähler structure"
to "*the* SW prepotential". -/
def HasPrescribedAsymptotics (Λ : ℂ) (N : ℕ) : Prop :=
  ∃ F : (Fin r → ℂ) → ℂ, ContDiffOn ℂ 2 F (s.a '' s.V) ∧
    (∀ u ∈ s.V, ∀ i, s.aD u i = partialDeriv F i (s.a u)) ∧
    (∀ u ∈ s.V, ∀ i j, (s.tau u).val i j = partialDeriv2 F i j (s.a u)) ∧
    Instantonic Λ N F

end PeriodChart

/-! ## H3 — Picard–Lefschetz, H4 — duality gluing, H5 — R-symmetry -/

/-- **H4 — the cover gluing / electric–magnetic duality.** Overlapping sheets differ by a
duality frame change `g`: a **ℤ-linear automorphism of the charge lattice** preserving the Dirac
pairing (i.e. an element of `Sp(2r,ℤ)`), under which the central charge is covariant. Hence
`|Z|` (mass) and the metric descend to the base. -/
structure SymplecticReframing {B : PeriodBase r} (s s' : PeriodChart B) where
  g : CycleLattice r ≃ₗ[ℤ] CycleLattice r
  symplectic : ∀ n n', intersectionForm (g n) (g n') = intersectionForm n n'
  covariant : ∀ u ∈ s.V ∩ s'.V, ∀ n, s'.periodCombination u (g n) = s.periodCombination u n

/-- **BPS mass descends to the base.** A `SymplecticReframing` gluing makes the mass
sheet-independent. -/
theorem SymplecticReframing.periodNorm_eq {B : PeriodBase r} {s s' : PeriodChart B}
    (D : SymplecticReframing s s')
    {u : Fin r → ℂ} (hu : u ∈ s.V ∩ s'.V) (n : CycleLattice r) :
    s'.periodNorm u (D.g n) = s.periodNorm u n := by
  unfold PeriodChart.periodNorm; rw [D.covariant u hu n]

/-- **H3 — Picard–Lefschetz at the generic stratum.** At a generic component of `Δ` the
monodromy around it — realized as an *actual* deck transformation
`D : SymplecticReframing s s'` to an adjacent
sheet — acts on the charge lattice as the reflection in the **vanishing charge** `n` of H2. This
forces the reflection to be symplectic (it is) and the central charge to transform covariantly
(a real constraint on the periods), unlike a vacuous `∃ g, g = transvection n`. The reflection
is the shared `transvection` (proved symplectic, `transvection_isSymplectic`). -/
def PicardLefschetzAtGenericStratum {B : PeriodBase r} (s : PeriodChart B) : Prop :=
  ∀ u₀ ∈ closure s.V ∩ B.Δ, ∀ n : CycleLattice r, n ≠ 0 → s.PeriodVanishesAt u₀ n →
    ∃ (s' : PeriodChart B) (D : SymplecticReframing s s'), ⇑D.g = transvection n

/-- **H5 — R-symmetry.** The anomalous `U(1)_R` leaves a discrete symmetry acting on the moduli:
a **nontrivial `ℂ`-linear automorphism of finite order dividing `2N`** preserving the
singular locus
`Δ` (permuting the singularities). `ℂ`-linearity rules out set-theoretic junk; `ω ≠ id` rules
out the
vacuous identity. (The *physical* `ℤ_{2N}` descends to the moduli with smaller order — to `N` on the
`SU(2)` coordinate `u ~ φ²` — so pinning the order to *exactly* `2N` is unsatisfiable on the moduli;
this faithful form records "order divides `2N`, nontrivial" without that over-claim, and is provably
non-vacuous — `hasFiniteOrderAutomorphism_of_neg_invariant`.) -/
def HasFiniteOrderAutomorphism (B : PeriodBase r) (N : ℕ) : Prop :=
  ∃ ω : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ), ω ≠ LinearMap.id ∧
    (∃ k, 0 < k ∧ k ∣ 2 * N ∧ (⇑ω)^[k] = id) ∧ (⇑ω) '' B.Δ = B.Δ

/-- **H5 is non-vacuous and faithful.** On any base whose singular locus is invariant under the
reflection `u ↦ -u`, the negation is a nontrivial `ℂ`-linear automorphism of order `2 ∣ 2N`
preserving `Δ` — the physical `ℤ₂ ⊂ ℤ_{2N}` symmetry, not set-theoretic junk. (For `SU(2)` this is
`u ↦ -u`, exchanging the two singularities `±Λ²`.) -/
theorem hasFiniteOrderAutomorphism_of_neg_invariant {r : ℕ} [NeZero r] {B : PeriodBase r}
    {N : ℕ} (hΔ : (fun x : Fin r → ℂ => -x) '' B.Δ = B.Δ) :
    HasFiniteOrderAutomorphism B N := by
  have hcoe : ⇑(-LinearMap.id : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ)) = fun x => -x := by
    funext x; simp
  refine ⟨-LinearMap.id, ?_, ⟨2, by norm_num, ⟨N, by ring⟩, ?_⟩, ?_⟩
  · intro h
    have hx := congrArg (fun f : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) => f (fun _ => 1)) h
    have hi := congrFun hx (⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩ : Fin r)
    simp at hi
    exact absurd hi (by norm_num)
  · rw [hcoe]; funext x; simp
  · rw [hcoe]; exact hΔ

/-! ## The N=2 `U(1)^{N-1}` effective theory, and the headline goals -/

/-- **A Seiberg–Witten effective theory** on a sheet: H1 (special geometry), H2 (singularities),
H3 (Picard–Lefschetz), H6 (matching) on the sheet, and H5 (R-symmetry) on the base. H4 (duality)
relates sheets. -/
structure IsPolarizedPeriodChart {B : PeriodBase r} (s : PeriodChart B) (Λ : ℂ) (N : ℕ) : Prop where
  specialGeometry : s.SpecialGeometry
  singularities : s.PeriodsDegenerateOnBoundary
  picardLefschetz : PicardLefschetzAtGenericStratum s
  matching : s.HasPrescribedAsymptotics Λ N
  rSymmetry : HasFiniteOrderAutomorphism B N

/-- **An atlas for an SW effective theory** (this is where H4 lives). A family of sheets
**covering** the smooth base `B.U`, each a single-sheet effective theory, with overlapping
sheets **glued** by an `Sp(2r,ℤ)` deck transformation. The global object the physics describes —
the duality gluing (H4) is *part of the theory*, not merely a relation between two isolated
sheets. -/
structure PeriodAtlas (B : PeriodBase r) (Λ : ℂ) (N : ℕ) where
  ι : Type
  sheets : ι → PeriodChart B
  covers : B.U ⊆ ⋃ i, (sheets i).V
  isSW : ∀ i, IsPolarizedPeriodChart (sheets i) Λ N
  glued : ∀ i j, ((sheets i).V ∩ (sheets j).V).Nonempty →
    Nonempty (SymplecticReframing (sheets i) (sheets j))

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
plus the period-level math axiom `periodRigidityAxiom` (on a *connected* chart overlap). The
rank-1 case
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
`periodRigidityAxiom` (with `P` monic, degree `N`, trace-free — the `SU(N)` slice). -/

end SeibergWitten.Physics
