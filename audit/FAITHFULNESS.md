# Faithfulness digest — informal claim next to formal statement

*The human-checkable crosswalk (convention:
[`formalization-assurance/FIDELITY_REVIEW.md`](https://github.com/math-commons/formalization-assurance/blob/main/FIDELITY_REVIEW.md),
"reviewer-facing affordances"). **Composition rule:** this file contains only
(1) claims verified by algorithm — every ```lean block below is checked **verbatim
against the source file** by [`check_faithfulness.py`](check_faithfulness.py), and
every axiom footprint is read from the machine-generated
[`axiom-report.txt`](axiom-report.txt) — and (2) side-by-side pairings a reviewer
checks directly on this page. No testimony ("X reviewed it") is load-bearing here.*

**Numbering.** Part I covers the physics hypotheses **H0–H6** (paper §4.2,
Appendix A) — the *inputs* whose faithfulness matters most, since a vacuous
hypothesis makes the headlines assert less and a too-strong one assumes the answer.
Part II covers the **mathematical axioms** (paper Appendix B) — here the statement
*is* the entire content, since nothing is proved about an axiom. Part III covers
the proved statements **E1–E11** (paper §4.3, §4.5, Appendix B), cross-referenced
to the paper's numbering. NB the paper's Appendix A abridges the Lean for
readability (e.g. H6 elides the H1 clauses); **this file is the verbatim record**.

*To check an entry: read the informal claim (with its citation), read the Lean
under it, judge whether the second says the first; the per-entry "check that" line
names the specific place misformalization could hide. Run
`python3 audit/check_faithfulness.py` to confirm every Lean quote matches the repo.
The recurring failure classes behind the "check that" lines — and the ones this
page-level review does NOT cover (fitness-for-purpose: can the target theorems
actually be derived from these statements?) — are catalogued in
[`DIFFICULT_POINTS.md`](DIFFICULT_POINTS.md); walk that register too.*

Citations: SW1 = Seiberg–Witten hep-th/9407087; SW2 = hep-th/9408099;
KLYT = hep-th/9411048; AF = hep-th/9411057; APSW = hep-th/9511154;
Lerche = hep-th/9611190.

---

# Part I — The physics hypotheses H0–H6 (paper §4.2, Appendix A)

These are *predicates* carried in theorem statements (bundled as
`IsPolarizedPeriodChart`), never global axioms — they appear in a theorem's type,
not its `#print axioms`. All are in `SeibergWitten/Physics/Hypotheses.lean`.

## H0 — the carrier: an N=2 U(1)^{N−1} EFT on the covered Coulomb branch

**Informal** (SW1 §2; N=2 SUSY + Coulomb-phase Higgsing): the low-energy data —
special coordinates `a, a_D`, coupling `τ`, charge lattice with Dirac pairing —
live on sheets over the moduli space minus its singular locus.

**Formal** (`SeibergWitten/Physics/Hypotheses.lean`):
```lean
structure PeriodBase (r : ℕ) where
  Δ : Set (Fin r → ℂ)
  U : Set (Fin r → ℂ)
  hUopen : IsOpen U
  /-- the smooth locus is *exactly* the complement of the singular locus (so `Δ` is closed). -/
  hUsmooth : U = Δᶜ
```
```lean
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
```
```lean
noncomputable def periodCombination (u : Fin r → ℂ) (n : CycleLattice r) : ℂ :=
  (∑ i, (n.1 i : ℂ) * s.a u i) + (∑ i, (n.2 i : ℂ) * s.aD u i)
```
**Check that:** the sheet `V` is **simply connected** (the universal-cover fix of
paper §4.4 — no global single-valued `τ`); `τ` is typed in `SiegelUpperHalfSpace`
(so `Im τ ≻ 0` is carried by the *type*); `a` is injective-holomorphic on the
chart (good coordinates); the central charge is the standard
`Z_n = n_e·a + n_m·a_D`.

## H1 — special geometry (one prepotential)

**Informal** (SW1 §2; rigid special Kähler from eight supercharges): one
holomorphic prepotential `F` with `a_D = ∂F/∂a` and `τ = ∂²F/∂a²`.

**Formal** (`SeibergWitten/Physics/Hypotheses.lean`):
```lean
def SpecialGeometry : Prop :=
  ∃ F : (Fin r → ℂ) → ℂ, ContDiffOn ℂ 2 F (s.a '' s.V) ∧
    (∀ u ∈ s.V, ∀ i, s.aD u i = partialDeriv F i (s.a u)) ∧
    (∀ u ∈ s.V, ∀ i j, (s.tau u).val i j = partialDeriv2 F i j (s.a u))
```
**Check that:** *one* `F` serves both clauses (not separate potentials for `a_D`
and `τ`); derivatives are in the `a`-coordinates (`partialDeriv` is `fderiv` along
`Pi.single`); regularity is `C²` on the image `a '' V`.

## H2 — BPS singularity structure

**Informal** (SW1 §3; the central-charge bound): massive (`Z_n ≠ 0`) for every
nonzero charge at smooth points; every singular boundary point is where some
*nonzero* charge becomes massless.

**Formal** (`SeibergWitten/Physics/Hypotheses.lean`):
```lean
def PeriodVanishesAt (u₀ : Fin r → ℂ) (n : CycleLattice r) : Prop :=
  Tendsto (fun u => s.periodCombination u n) (𝓝[s.V] u₀) (𝓝 0)
```
```lean
def PeriodsDegenerateOnBoundary : Prop :=
  (∀ u ∈ s.V, ∀ n : CycleLattice r, n ≠ 0 → s.periodCombination u n ≠ 0) ∧
  (∀ u₀ ∈ closure s.V ∩ B.Δ, ∃ n : CycleLattice r, n ≠ 0 ∧ s.PeriodVanishesAt u₀ n)
```
**Check that:** both clauses demand `n ≠ 0` (the anti-vacuity hardening of paper
§4.4 — `Z_0 = 0` may not witness anything); masslessness is a *limit within the
sheet* (`𝓝[s.V]`), correct on the universal cover.

## H3 — monodromy from massless charged states (Picard–Lefschetz)

**Informal** (SW1 §3–4; one-loop running + Witten effect): encircling a point
where charge `n` goes massless, the periods undergo the symplectic transvection
in `n`.

**Formal** (`SeibergWitten/Physics/Hypotheses.lean`):
```lean
def PicardLefschetzAtGenericStratum {B : PeriodBase r} (s : PeriodChart B) : Prop :=
  ∀ u₀ ∈ closure s.V ∩ B.Δ, ∀ n : CycleLattice r, n ≠ 0 → s.PeriodVanishesAt u₀ n →
    ∃ (s' : PeriodChart B) (D : SymplecticReframing s s'), ⇑D.g = transvection n
```
**Check that:** it demands an **actual adjacent sheet and reframing** whose lattice
map *is* the transvection in the *same* `n` that went massless — not the vacuous
`∃ g, g = transvection n` (paper §4.4). "Generic stratum": the AD strata are
deliberately excluded (they are the derived `NonLocalDegenerationLocus`, E9).

## H4 — electric–magnetic duality (the gluing)

**Informal** (SW1 §3; Sp(2r,ℤ) duality): overlapping sheets differ by an integral
symplectic change of duality frame under which the central charge is covariant.

**Formal** (`SeibergWitten/Physics/Hypotheses.lean`):
```lean
structure SymplecticReframing {B : PeriodBase r} (s s' : PeriodChart B) where
  g : CycleLattice r ≃ₗ[ℤ] CycleLattice r
  symplectic : ∀ n n', intersectionForm (g n) (g n') = intersectionForm n n'
  covariant : ∀ u ∈ s.V ∩ s'.V, ∀ n, s'.periodCombination u (g n) = s.periodCombination u n
```
**Check that:** `g` is ℤ-linear and pairing-preserving (that *is* `Sp(2r,ℤ)`);
covariance ties the two sheets' physics together on the overlap (this is what
makes the BPS mass sheet-independent, `SymplecticReframing.periodNorm_eq`). H4 is
*not* a field of the H-bundle below: it lives at the atlas level and in the
conclusions of E5/E7.

## H5 — discrete R-symmetry

**Informal** (SW1 §3; the anomalous U(1)_R): a nontrivial discrete linear symmetry
of the moduli, of order dividing 2N, permuting the singularities.

**Formal** (`SeibergWitten/Physics/Hypotheses.lean`):
```lean
def HasFiniteOrderAutomorphism (B : PeriodBase r) (N : ℕ) : Prop :=
  ∃ ω : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ), ω ≠ LinearMap.id ∧
    (∃ k, 0 < k ∧ k ∣ 2 * N ∧ (⇑ω)^[k] = id) ∧ (⇑ω) '' B.Δ = B.Δ
```
**Check that:** "order **dividing** 2N", not "exactly 2N" — the faithful statement
on the moduli (paper §4.4: the ℤ_{4N} on the fields acts through ℤ_{2N} on `φ` and
through a possibly smaller quotient on the Casimirs; "exactly 2N" is false at rank
1). `ℂ`-linearity and `ω ≠ id` block set-theoretic junk and the trivial witness;
non-vacuity is proved (`hasFiniteOrderAutomorphism_of_neg_invariant`, E-free).

## H6 — weak-coupling asymptotics (nonrenormalization)

**Informal** (SW1 §2; one-loop exactness + asymptotic freedom): the prepotential
is classical + one-loop + an instanton tail in powers of `Λ^{2N}`.

**Formal** (`SeibergWitten/Physics/Hypotheses.lean`):
```lean
def Instantonic (Λ : ℂ) (N : ℕ) (F : (Fin r → ℂ) → ℂ) : Prop :=
  Λ ≠ 0 ∧ ∃ c : ℕ → (Fin r → ℂ) → ℂ, (∀ k, Differentiable ℂ (c k)) ∧
    (∀ k : ℕ, ∀ t : ℂ, t ≠ 0 → ∀ a : Fin r → ℂ,
      c k (t • a) = t ^ ((2 : ℤ) - 2 * (N : ℤ) * (k : ℤ)) * c k a) ∧
    ∀ a : Fin r → ℂ,
      F a - classicalPrepotential a - oneLoopPrepotential Λ a
        = ∑' k : ℕ, c (k + 1) a * (Λ ^ (2 * N)) ^ (k + 1)
```
```lean
def HasPrescribedAsymptotics (Λ : ℂ) (N : ℕ) : Prop :=
  ∃ F : (Fin r → ℂ) → ℂ, ContDiffOn ℂ 2 F (s.a '' s.V) ∧
    (∀ u ∈ s.V, ∀ i, s.aD u i = partialDeriv F i (s.a u)) ∧
    (∀ u ∈ s.V, ∀ i j, (s.tau u).val i j = partialDeriv2 F i j (s.a u)) ∧
    Instantonic Λ N F
```
**Check that:** the tail starts at `k+1` (no `k=0` constant absorbing the one-loop
term); the coefficients carry the **weighted-homogeneity clause**
`c_k(t·a) = t^{2−2Nk}·c_k(a)` — this is `Λ`-independence of the instanton
coefficients expressed at fixed `Λ` (via the family's scale covariance), and it is
what makes the definition non-vacuous: **an earlier form without it fit any
differentiable `F`** (author-caught 2026-07-05; `DIFFICULT_POINTS.md` B6 — the
single coefficient `c₁ := remainder/Λ^{2N}` absorbed everything);
`HasPrescribedAsymptotics` **repeats the H1 clauses for the same `F`** — the
non-renormalized form constrains H1's prepotential, not some other function; check
`classicalPrepotential`/`oneLoopPrepotential` (same file) for the normalization.

## The bundle

**Formal** (`SeibergWitten/Physics/Hypotheses.lean`):
```lean
structure IsPolarizedPeriodChart {B : PeriodBase r} (s : PeriodChart B) (Λ : ℂ) (N : ℕ) : Prop where
  specialGeometry : s.SpecialGeometry
  singularities : s.PeriodsDegenerateOnBoundary
  picardLefschetz : PicardLefschetzAtGenericStratum s
  matching : s.HasPrescribedAsymptotics Λ N
  rSymmetry : HasFiniteOrderAutomorphism B N
```
**Check that:** exactly five fields — H1, H2, H3, H6, H5; H0 is the carrier types
themselves and H4 is the atlas gluing. This bundle is the full physics input to
E5/E6; nothing else physical enters their statements.

---

# Part II — The mathematical axioms (paper Appendix B)

For an axiom, faithfulness *is the whole game*: nothing is proved about it, so a
reviewer must check that each assumes **only** the named classical fact — nothing
smuggled. Footprints/consumers are in [`axiom-report.txt`](axiom-report.txt) and
[`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md).

## B.1 — `periodRigidityAxiom` (the consolidated period geometry)

**Informal claim it codifies** (classical Gauss–Manin / Picard–Fuchs theory for
the family `y² = P² − Λ^{2N}`; not yet in any prover's library): the period
geometry of the SW curve family exists and is rigid.

**Formal** (`SeibergWitten/Physics/PeriodLayer.lean`) — the axiom and the head of
the structure it asserts:
```lean
axiom periodRigidityAxiom (N : ℕ) (Λ : ℂ) (hN : 2 ≤ N) : PeriodRigidity N Λ
```
```lean
structure PeriodRigidity (N : ℕ) (Λ : ℂ) where
  /-- `SU(N)` needs `N ≥ 2` (guards the `N − 1` truncated subtraction: `N ≤ 1 ⇒` rank 0). -/
  hN : 2 ≤ N
  /-- Higher-genus period-map rigidity: two SW theories over a common base, on a connected
  (nonempty) overlap, are duality-related (`Sp(2(N−1),ℤ)`). -/
  rigidity : ∀ {B : PeriodBase (N - 1)} (s s' : PeriodChart B), IsConnected (s.V ∩ s'.V) →
      IsPolarizedPeriodChart s Λ N → IsPolarizedPeriodChart s' Λ N → Nonempty (SymplecticReframing s s')
  /-- Existence: the genus-`(N−1)` SW curve `y² = P² − Λ^{2N}` realizes a theory; `P` monic,
  degree `N`, **trace-free** (`coeff (N−1) = 0`) — the SU(N) slice of U(N). -/
  realize : ∀ P : Polynomial ℂ, P.Monic → P.natDegree = N → P.coeff (N - 1) = 0 →
      Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * N))) →
      ∃ (B : PeriodBase (N - 1)) (s : PeriodChart B), IsPolarizedPeriodChart s Λ N ∧
        B.Δ = {u | ¬ Squarefree (swCurvePoly N Λ u)} ∧ swModulus N P ∈ s.V
```
**Check that — the honest reading:** this is a **coarse** package (paper B.1 says
so): comparing with Part III, the `rigidity` field **is** the statement of E5 and
`realize` **is** E6, quantified over the H-bundle. So E5/E6 are *thin corollaries*
— their mathematical content currently **resides in this axiom**, and the paper's
claim is the *separation* (physics in H0–H6, math here), not that the math is done.
The discharge plan is [`PERIOD_LAYER_DISCHARGE.md`](PERIOD_LAYER_DISCHARGE.md).

## B.1′ — `matterPeriodRigidityAxiom`: **DISCHARGED 2026-07-06**

The former axiom was replaced, at its consumed instantiation, by a constructed
theorem — the first `PeriodChart` instance in the development.
**Formal** (`SeibergWitten/Physics/MatterChart.lean`):
```lean
theorem matterPeriodRigidity_nf1_ad (Λ : ℂ) (hΛ : Λ ≠ 0) :
    ∃ (B : PeriodBase 1) (s : PeriodChart B),
      IsMatterPolarizedPeriodChart s 1 Λ ![-(3 / 4) * Λ]
        ∧ MatterPeriodRigidityData s 1 Λ ![-(3 / 4) * Λ] :=
  ⟨matterADBase Λ, matterADChart Λ hΛ,
    matterADChart_polarized Λ hΛ, matterADChart_rigidityData Λ hΛ⟩
```
**Check that — the disclosure (B4-class, deliberate):** the witness is a **non-SQCD
inhabitant** (`a = u − u_AD`, `a_D = i·a`, constant `τ ≡ i`, `F = (i/2)z²`) on a
ball tangent to the AD point inside the explicit two-point singular locus
(`Δ = {3Λ²/4, −15Λ²/16}`, from the exact discriminant factorization
`−Λ⁶(u−3Λ²/4)²(u+15Λ²/16)`). The discharge is legitimate w.r.t. the *statement*
and simultaneously makes formal that `IsMatterPolarizedPeriodChart` (H1 + Δ-tie
only) does not pin the genuine theory — previously a docstring concession, now an
explicit inhabitant. Strengthening the predicate (matter H6 / period-tie) plus the
genuine quartic-period construction is Stage B of `MPRA_DISCHARGE_PLAN.md` (archived, local `history/audit/`). The
general-`(Nf, m)` axiom form is gone (narrowing to the consumed instantiation,
per the 2026-07-05 discipline).

## B.2 — the classical-mathematics axioms (rank-1 route)

**`SameSWMonodromy`** — **demoted from axiom to definition (2026-07-04)**; kept here
because Part II readers will look for the former axiom.
**Formal** (`SeibergWitten/Physics/SU2Rigidity.lean`):
```lean
def IsSWDevelopingMap (Λ : ℂ) (D : Set ℂ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f D ∧ (∀ u ∈ D, 0 < (f u).im) ∧ DevelopsSWCrossRatio Λ D f
```
```lean
def SameSWMonodromy (Λ : ℂ) (D : Set ℂ) (f g : ℂ → ℂ) : Prop :=
  IsSWDevelopingMap Λ D f ∧ IsSWDevelopingMap Λ D g
```
**Check that:** the former uninterpreted predicate is now **both maps are developing
maps** — holomorphic, ℍ-valued, developing the pinned `swCrossRatio` (per the C-route
review's Q11). **All three clauses are load-bearing**: dropping analyticity admits
choice-built discontinuous lifts (via the proved `τ ↦ τ+2`), and dropping ℍ-valuedness
admits junk-value inhabitants at `Λ = 0` (off `ℍ` the θ-series are junk and `λ ≡ 0`) —
both refute the lift-uniqueness axiom, both caught in self-review
(`DIFFICULT_POINTS.md` B4). E7 is now rigidity relative to a *contentful* hypothesis,
and no physics axiom remains on its kernel footprint.

**`AX_thrice_punctured_uniformization`** — the Γ(2) covering.
**Formal** (`SeibergWitten/Physics/ModularLambda.lean`):
```lean
structure ThricePuncturedUniformization where
  /-- the developing/covering map `λ : ℍ → ℂ∖{0,1}`. -/
  cover : UpperHalfPlane → {v : ℂ // v ∉ ({0, 1} : Set ℂ)}
  /-- `λ` is invariant under the deck group `Γ(2)`. -/
  gamma2_invariant : ∀ γ ∈ Gamma2, ∀ τ, cover (γ • τ) = cover τ
  /-- `λ` is onto `ℂ∖{0,1}` (rules out trivial models — this is the uniformization). -/
  surjective : Function.Surjective cover
  /-- the fibres of `λ` are exactly the `Γ(2)`-orbits (the covering property). -/
  fiber : ∀ τ τ', cover τ = cover τ' ↔ ∃ γ ∈ Gamma2, γ • τ = τ'
```
```lean
axiom AX_thrice_punctured_uniformization : Nonempty ThricePuncturedUniformization
```
**Check that:** the fields are exactly the classical content — a map
`ℍ → ℂ∖{0,1}`, Γ(2)-invariant, **surjective**, with **fibres = Γ(2)-orbits** — no
extra properties. The invariance half is separately *proved* for the concrete
`λ = θ₂⁴/θ₃⁴` (E11); surjectivity + fibres remain the classical debt (Ahlfors).

**`AX_developing_map_rigidity`** — lift uniqueness (Forster).
**Formal** (`SeibergWitten/Physics/SU2Rigidity.lean`):
```lean
axiom AX_developing_map_rigidity
    {D : Set ℂ} {u₀ : ℂ} {f g : ℂ → ℂ}
    (U : ThricePuncturedUniformization)
    (hD : IsOpen D) (hu₀ : u₀ ∈ D)
    (hf : AnalyticOnNhd ℂ f D) (hfH : ∀ u ∈ D, 0 < (f u).im)
    (hg : AnalyticOnNhd ℂ g D) (hgH : ∀ u ∈ D, 0 < (g u).im)
    (hbase : ∀ u ∈ D, modularLambdaFn (f u) = modularLambdaFn (g u)) :
    ∃ γ ∈ Gamma2, f =ᶠ[𝓝 u₀] fun u => moebiusOn γ (g u)
```
**Check that:** with `SameSWMonodromy` now *defined* (as: both maps are genuine
developing maps — holomorphic, ℍ-valued, developing the pinned modulus), this is
classical lift-uniqueness — two lifts of the **same** base map through the covering
agree up to a deck/frame change. The strength of the hypotheses is exactly what makes
the axiom true: **three** weaker candidate forms were refutable — pointwise-only,
missing ℍ-valuedness, and unconstrained germ point (`D = ∅`, `D = {u₀}`) — see the
`SameSWMonodromy` entry above and `DIFFICULT_POINTS.md` B4; `IsOpen D` + `u₀ ∈ D`
put the developing data on a genuine neighborhood of the germ point. The conclusion is
a **`Γ(2)` deck transformation** acting by `moebiusOn` (strengthened per external review
round 2, 2026-07-04: the earlier `∃ m : ℂ → ℂ` abandoned the group structure — the
unused covering argument was the tell); `analyticOnNhd_moebius_comp` (proved, with the
denominator-nonvanishing lemma on ℍ) is what lets the identity theorem consume it. The conclusion is a
*germ* equality at `u₀` plus analyticity of the reframed map on `D` — global
agreement on `D` is then **proved** (identity theorem, `holo_eqOn_of_germ`,
axiom-free), the right division of labor between axiom and theorem.

**`AX_jacobi_quartic`, `AX_theta3_ne_zero`** — θ identities (Jacobi triple product).
**Formal** (`SeibergWitten/Physics/ThetaLambda.lean`):
```lean
axiom AX_jacobi_quartic (τ : UpperHalfPlane) :
    theta3 (τ : ℂ) ^ 4 = theta2 (τ : ℂ) ^ 4 + theta4 (τ : ℂ) ^ 4
```
```lean
axiom AX_theta3_ne_zero (τ : UpperHalfPlane) : theta3 (τ : ℂ) ≠ 0
```
**Check that:** these are the only two θ facts assumed, both restricted to `ℍ`
(where the θ series converge — an earlier draft stated the quartic on all of `ℂ`,
relating junk values off `ℍ`; caught by this review and restricted). Both are
**independently machine-checked** — exact integer q-series identity to order 200
and grid non-vanishing (`theta_identities_cas_check.py`), plus the 40-digit oracle
(`numerical/validate_lambda.py`).

**`localMonodromy`, `AX_picard_lefschetz_local`** — the local-system gap.
**Formal** (`SeibergWitten/Physics/Monodromy.lean`):
```lean
axiom localMonodromy : ∀ {r : ℕ}, CycleLattice r → (CycleLattice r → CycleLattice r)
```
```lean
axiom AX_picard_lefschetz_local {r : ℕ} (γ : CycleLattice r) :
    localMonodromy γ = transvection γ
```
**Check that:** the first axiom *declares data* (an uninterpreted function — the
family's local monodromy, pending the Gauss–Manin layer); the second identifies it
with the transvection. Together they say nothing beyond "the local monodromy is
Picard–Lefschetz"; that the transvection is symplectic is *proved* (E4).

**`periodRatio_logDeriv_asymptotic`** — weak-coupling running (off the headline
footprint). **DISCHARGED 2026-07-05, with a fidelity finding
(`DIFFICULT_POINTS.md` D3):**
**Formal** (`SeibergWitten/Physics/BetaFunction.lean`):
```lean
theorem periodRatio_logDeriv_asymptotic (Nf : ℕ) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      Tendsto (fun s : ℝ => (s : ℂ) * deriv F (s : ℂ)) atTop
        (nhds ((4 - (Nf : ℂ)) / (2 * (Real.pi : ℂ) * I)))
```
**Check that:** the statement is purely **existential** — no clause ties `F` to the
curve's period integrals, which is exactly why it is now a *theorem* (explicit
entire witness, the `Ein` primitive; footprint standard-3). E10 inherits the same
existential character: its content is "some entire log-running `F` has one-loop
beta", with the identification of `F` as *the* period ratio living in the
dictionary, not the kernel. The faithful strengthening (the asymptotic for
`i·K(1−m)/K(m)` at the curve's modulus) is the R4 target. The constant is
`(4 − N_f)/(2πi)`; E10 converts it to `β → −b₀/(πi)` (factor 2 from `Λ ∂_Λ` vs
`s ∂_s`, `s = u/Λ²`). Used **only** by E10.

## B.3 — the C-route elliptic axioms (rank-1 program; **not yet consumed by any theorem**)

Milestone C0 of `GENUS1_PERIODS_PLAN.md` (archived, local `history/audit/`): classical elliptic-integral axioms that will
replace `periodRigidityAxiom` at rank 1. Landed after two vetting gates — numeric
(84/84 at 40 digits, `numerical/validate_elliptic.py`) and adversarial review
(GR 2026-07-04, v1 NO-GO → v2). All in `SeibergWitten/Physics/EllipticIntegrals.lean`.

**The definitions** — honest integrals on the cut plane:

**Formal** (`SeibergWitten/Physics/EllipticIntegrals.lean`):
```lean
def EllipticParamDomain : Set ℂ := {m | ¬ (m.im = 0 ∧ (m.re ≤ 0 ∨ 1 ≤ m.re))}
```
```lean
noncomputable def ellipticKm (m : ℂ) : ℂ :=
  ∫ θ in (0:ℝ)..(Real.pi / 2), ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1/2) : ℂ)
```
```lean
noncomputable def ellipticEm (m : ℂ) : ℂ :=
  ∫ θ in (0:ℝ)..(Real.pi / 2), ((1 : ℂ) - m * (Real.sin θ : ℂ) ^ 2) ^ ((1/2) : ℂ)
```
**Check that:** the parameter is `m = k²` (mpmath's convention, D0-checked to residual
`0.0`); principal-branch `cpow`; the `m ↦ 1−m` symmetry of the domain is **proved**
(`one_sub_mem_ellipticParamDomain`, standard-3), as is nonemptiness.

**C1 — Jacobi inversion / θ-bridge** (WW §§21–22):
**Formal** (`SeibergWitten/Physics/EllipticIntegrals.lean`):
```lean
axiom AX_elliptic_inversion (m : ℂ) (hm : m ∈ EllipticParamDomain) :
    ellipticKm m ≠ 0 ∧
    ∃ τ : UpperHalfPlane, modularLambdaFn (τ : ℂ) = m ∧
      ellipticKm m = (Real.pi / 2 : ℂ) * theta3 (τ : ℂ) ^ 2 ∧
      (τ : ℂ) = Complex.I * ellipticKm (1 - m) / ellipticKm m
```
**Check that:** `K ≠ 0` is explicit (review catch: don't hide an assertion in Lean's
`x/0 = 0`); the `∃τ` is *a* preimage — the analytic structure rigidity needs is
**C1h, now proved**: `ellipticKm_differentiableOn` / `ellipticEm_differentiableOn`
(**standard-3**, via the slit-plane lemma + dominated differentiation) and
`tau_ratio_differentiableOn` (standard-3 + this axiom only) — see the golden trace.

**C2 — Legendre relation** (WW §22.737) — **DISCHARGED (2026-07-04, the discharge
loop): the axiom is deleted; C2 is now the theorem** `legendre_relation`:
**Formal** (`SeibergWitten/Physics/EllipticIntegrals.lean`):
```lean
theorem legendre_relation (m : ℂ) (hm : m ∈ EllipticParamDomain) :
    ellipticEm m * ellipticKm (1 - m) + ellipticEm (1 - m) * ellipticKm m
      - ellipticKm m * ellipticKm (1 - m) = (Real.pi / 2 : ℂ)
```
**Check that:** proved, not assumed — the two Legendre ODEs (via the C1h engine and the
formalized IBP), constancy on the star-shaped cut plane (segment MVT), and the `m → 0`
cusp limit (the quantitative `‖E−K‖` rate against `m·log m → 0`). Footprint:
**standard-3 only** (2026-07-05: the last input, the C3 cusp clause, was itself
discharged — see below).

**C3 — cusp limits** (WW §22.7): **FULLY DISCHARGED 2026-07-05** — the axiom is
deleted; C3 is now the theorem `elliptic_cusp_limit`:
**Formal** (`SeibergWitten/Physics/EllipticIntegrals.lean`):
```lean
theorem elliptic_cusp_limit :
    Tendsto (fun m : ℂ => ellipticKm (1 - m) + (1/2 : ℂ) * Complex.log m)
      realCuspApproach (𝓝 ((2 * Real.log 2 : ℝ) : ℂ))
```
```lean
def realCuspApproach : Filter ℂ := Filter.map (fun x : ℝ => (x : ℂ)) (𝓝[>] (0:ℝ))
```
**Check that:** footprint **standard-3** (`#print axioms` in the golden trace). The
discharge history (all 2026-07-04/05, the loop): the `K, E → π/2` and `E(1−m) → 1`
clauses fell first; the filter was weakened to the positive-real ray (legitimate — the
sole consumer pins a proved-constant function); then the remaining log clause was
proved by the model-comparison route — `K(1−x)` realized as the reflected real
integral, the elementary model `∫(φ²+x)^{−1/2} = log(π/2+√(π²/4+x)) − log√x` carrying
the entire divergence (honest FTC), the difference dominated by the *constant* `π²`
and converging to `∫₀^{π/2}(1/sinφ − 1/φ) = log(4/π)` (ε-endpoint FTC with
antiderivative `log(tan(φ/2)) − log φ`), and `log(4/π) + log π = 2log2`. With C3 gone,
`legendre_relation` (former C2) is **axiom-free**, and the C-route's remaining
trusted base is C1 + C4 + the θ pair + the covering pair.

**C4 — cusp labeling** (the review's sharpest catch — `DIFFICULT_POINTS.md` C1).
**DEMOTED from axiom to an unasserted named statement (2026-07-05):** the golden
trace showed `AX_tau_cusp_zero` was consumed by *no* theorem, and an unconsumed
axiom is pure trusted-base pollution. The spec survives as a `Prop`-valued
definition; a future consumer must prove it or reintroduce a tracked axiom:
**Formal** (`SeibergWitten/Physics/EllipticIntegrals.lean`):
```lean
def TauCuspLabelZero : Prop :=
  ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ ∀ᶠ m in 𝓝[EllipticParamDomain] 0,
    Complex.I * ellipticKm (1 - m) / ellipticKm m
      = -(Complex.I / (Real.pi : ℂ)) * Complex.log (m / 16) + h m
```
**Check that:** the log-remainder form encodes "the loop about `m = 0` is exactly `T²`"
with no analytic-continuation vocabulary; the `m = 1` label (`ST²S⁻¹`) then follows from
the `m ↔ 1−m` involution and the *proved* `λ` S-law; both jumps verified numerically
(`+2` jump; `τ ↦ τ/(1−2τ)` at `m = 1`; remainder single-valued to `3e-9`).
**Disposition (review round 2):** an external review claimed `h` cannot be `AnalyticAt 0`
because `K(1−m)` has `O(m log m)` terms. **Rejected with proof**: the `m log m` terms
live in `K(1−m)` alone (which is why C3 is a *limit*), but cancel in the ratio
`τ = iK′/K` — from `λ(τ) = 16q·B̃(q)` invertible, `q(m) = (m/16)B(m)` is analytic, so
`h = −(i/π)log B(m)` is analytic at `0`. Numerically: the arithmetic-stencil second
difference `|d2|/m² → 0.1293134` (bounded ⟺ analytic; an `m log m` term would grow
`~0.523|c|/m`), and `|h₁| = 1/(2π)` to nine digits, exactly the nome-series prediction
(oracle, 86/86).

**The SW modulus `swCrossRatio` (pinned by computation, 2026-07-04)** — a *definition*,
listed here because its faithfulness was an open pin, resolved numerically:
**Formal** (`SeibergWitten/Physics/EllipticIntegrals.lean`):
```lean
noncomputable def swCrossRatio (Λ u : ℂ) : ℂ := 2 * Λ ^ 2 / (u + Λ ^ 2)
```
```lean
def DevelopsSWCrossRatio (Λ : ℂ) (D : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ u ∈ D, modularLambdaFn (f u) = swCrossRatio Λ u
```
**Check that:** the Möbius map was **determined, not chosen** — branch-tracked contour
quadrature of the actual curve periods, `λ(τ_curve(u))` against all six anharmonic
candidates, unique winner at every sample (`numerical/validate_swcrossratio.py`,
16/16, residuals ≲ 1e-31; the `τ(3)=i` anchor caught a factor-2 cycle-normalization
error in the first attempt). Singularities map monopole `↦ 1`, dyon `↦ ∞`, weak
coupling `↦ 0`; the monopole value is **proved** (`swCrossRatio_monopole`,
standard-3), as is scale covariance in `u/Λ²` (`swCrossRatio_scale`). The
`DevelopsSWCrossRatio` form is **chart-relative** (`∀ u ∈ D`), refining the plan's
global `∀ u` (junk values off-chart carry no claim).

## Inherited — `AX_PeriodCycleBasis` (jacobian-challenge)

**Formal** (`../jacobian-challenge/Jacobians/Axioms/PeriodCycleBasis.lean`;
requires the sibling checkout, cf. `BUILD.md`):
```lean
axiom AX_PeriodCycleBasis {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    Nonempty (PeriodCycleBasis X x₀)
```
**Check that:** it asserts a symplectic cycle basis with the Riemann-bilinear
package for a compact Riemann surface (read `PeriodCycleBasis` in that file) —
classical (Griffiths–Harris); it enters only E3's footprint here. Its vetting
history lives in jacobian-challenge's own audit.

---

# Part III — The proved statements E1–E11

## E1. The curve and its genus

**Paper:** §4.3 (bullet and status table); dictionary §4.1.

**Informal** (KLYT; AF): the SU(N) curve `y² = P_N(x)² − Λ^{2N}`, `P_N` of degree
`N`, is a hyperelliptic Riemann surface of genus `N − 1`.

**Formal** (`HigherGenus/Curve.lean`):
```lean
theorem genus_swCurve {N : ℕ} (P : Polynomial ℂ) (Λ : ℂ)
    (hPdeg : P.natDegree = N) (hN : 2 ≤ N)
    (hsf : Squarefree (P ^ 2 - C (Λ ^ (2 * N)))) :
    Jacobians.RiemannSurface.genus
      (HyperellipticEvenProj (swData P Λ hPdeg hN hsf)) = N - 1
```
**Check that:** `genus` is jacobian-challenge's genus of the projective
hyperelliptic model; smoothness is carried honestly as `Squarefree` (not glossed);
`2 ≤ N` is the SU(N) range. Footprint: standard-3 (axiom-free).

## E2. SU(2) singularities: exactly the monopole and dyon points

**Paper:** §4.3; the worked instance of H2's "singular exactly where a BPS state
goes massless".

**Informal** (SW1 §4): the SU(2) curve `y² = (x²−u)² − Λ⁴` is singular at
`u = ±Λ²` — and nowhere else.

**Formal** (`SeibergWitten/Physics/SU2Singularities.lean`):
```lean
theorem su2_singular_locus {u Λ : ℂ} (hΛ : Λ ≠ 0) :
    ¬ Squarefree (((X : ℂ[X]) ^ 2 - C u) ^ 2 - C (Λ ^ 4)) ↔ u = Λ ^ 2 ∨ u = -Λ ^ 2
```
**Check that:** it is an **iff** (the "nowhere else" is the hard direction);
`Λ ≠ 0` is a real hypothesis (at `Λ = 0` every `u` is singular).
Footprint: standard-3 (axiom-free).

## E3. Special-Kähler positivity

**Paper:** §4.3 (bullet and status table); H1's no-ghost gloss in §4.2.

**Informal** (SW1 §2; Lerche §2): the effective coupling `τ` is symmetric with
`Im τ ≻ 0` — the special-Kähler metric is positive (no ghosts).

**Formal** (`HigherGenus/SpecialGeometry.lean`):
```lean
theorem sw_metric_posDef {N : ℕ} (P : Polynomial ℂ) (Λ : ℂ)
    (hPdeg : P.natDegree = N) (hN : 2 ≤ N)
    (hsf : Squarefree (P ^ 2 - C (Λ ^ (2 * N))))
    (x₀ : HyperellipticEvenProj (swData P Λ hPdeg hN hsf)) :
    ∃ τ : SiegelUpperHalfSpace (N - 1), (τ.val.map Complex.im).PosDef
```
**Check that:** the statement is **existential** — it produces the curve's period
matrix in the Siegel space (symmetry is in the `SiegelUpperHalfSpace` type,
positivity is entrywise-`im` `PosDef`); it does **not** yet assert `τ` as a
function of `u` (that is the period-variation debt, paper B.3). Footprint:
standard-3 + inherited `AX_PeriodCycleBasis` (Part II).

## E4. Picard–Lefschetz monodromy is symplectic

**Paper:** §4.3; why H3's monodromy lands in H4's group.

**Informal** (SW1 §3; classical): the monodromy transvection
`v ↦ v + ⟨v,γ⟩γ` in a vanishing cycle `γ` preserves the (Dirac) intersection
pairing — monodromy lands in `Sp(2r,ℤ)`.

**Formal** (`SeibergWitten/Physics/Hypotheses.lean`):
```lean
theorem transvection_isSymplectic (γ : CycleLattice r) :
    IsSymplectic (transvection γ)
```
**Check that:** `IsSymplectic f` unfolds to `∀ v w, ⟨f v, f w⟩ = ⟨v, w⟩` with
`⟨·,·⟩` the `intersectionForm`/Dirac pairing, and `transvection` is the
Picard–Lefschetz reflection. Footprint: standard-3 (axiom-free).

## E5. Headline uniqueness up to electric–magnetic duality

**Paper:** §4.3 headline; Appendix B.1. Consumes the full H-bundle (Part I); the
conclusion is H4's reframing.

**Informal** (SW1 §5–6; KLYT; AF): the hypotheses H0–H6 determine the low-energy
theory uniquely up to `Sp(2(N−1),ℤ)` duality.

**Formal** (`SeibergWitten/Physics/PeriodLayer.lean`):
```lean
theorem sw_effective_theory_unique_up_to_duality {N : ℕ} {Λ : ℂ} (hN : 2 ≤ N)
    {B : PeriodBase (N - 1)} (s s' : PeriodChart B) (hconn : IsConnected (s.V ∩ s'.V))
    (h : IsPolarizedPeriodChart s Λ N) (h' : IsPolarizedPeriodChart s' Λ N) :
    Nonempty (SymplecticReframing s s')
```
**Check that:** the physics enters **only** through the two
`IsPolarizedPeriodChart` hypotheses; the overlap must be `IsConnected` (the frame
is only locally constant); the conclusion is "unique up to duality", not "equal".
Footprint: standard-3 + `periodRigidityAxiom` — and per Part II B.1, the
mathematical content currently resides in that axiom; the theorem's value is the
machine-checked *separation*.

## E6. Headline existence: the SW curve realizes the theory

**Paper:** §4.3 headline; Appendix B.1.

**Informal** (SW1; KLYT; AF): the curve family realizes an effective theory
satisfying H0–H6, with singular locus the discriminant of the curve.

**Formal** (`SeibergWitten/Physics/PeriodLayer.lean`):
```lean
theorem sw_curve_admits_effective_theory {N : ℕ} {Λ : ℂ} (hN : 2 ≤ N) (P : Polynomial ℂ)
    (hPm : P.Monic) (hPdeg : P.natDegree = N) (hPtr : P.coeff (N - 1) = 0)
    (hsf : Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * N)))) :
    ∃ (B : PeriodBase (N - 1)) (s : PeriodChart B), IsPolarizedPeriodChart s Λ N ∧
      B.Δ = {u | ¬ Squarefree (swCurvePoly N Λ u)} ∧ swModulus N P ∈ s.V
```
**Check that:** `Monic` + vanishing subleading coefficient is the **SU(N)** (not
U(N)) family; the singular locus is **literally** the discriminant set; the given
curve's modulus lies in the chart. Footprint: standard-3 + `periodRigidityAxiom`
(same caveat as E5).

## E7. Rank-1 (SU(2)) rigidity, finer footprint

**Paper:** §4.3 (the finer SU(2) footprint); Appendix B.2–B.3.

**Informal** (SW1 §6): two candidate period maps with the same `Sp(2,ℤ)` monodromy
around `±Λ²` agree up to a duality frame — the SU(2) solution is rigid.

**Formal** (`SeibergWitten/Physics/SU2Rigidity.lean`):
```lean
theorem sw_su2_unique
    {Λ : ℂ} {D : Set ℂ} (hDo : IsOpen D) (hD : IsPreconnected D)
    {u₀ : ℂ} (hu₀ : u₀ ∈ D) {f g : ℂ → ℂ}
    (hmono : SameSWMonodromy Λ D f g) :
    ∃ γ ∈ Gamma2, Set.EqOn f (fun u => moebiusOn γ (g u)) D
```
**Check that:** `SameSWMonodromy` is now the **defined** pinned developing property
(Part II) — both maps develop the curve's modulus `swCrossRatio` — so the theorem's
physics is a contentful hypothesis in its type; the analytic propagation from germ
to all of `D` is the proved, axiom-free part. Footprint: standard-3 +
`AX_thrice_punctured_uniformization` + `AX_developing_map_rigidity` — **no physics
axiom**.

## E8. Argyres–Douglas cusp with matter; none for pure SU(2)

**Paper:** §4.5.

**Informal** (APSW; curve from SW2): SU(2) `N_f = 1` SQCD has a superconformal
point where the curve degenerates to a cusp; the pure SU(2) curve never does.

**Formal** (`SeibergWitten/Physics/SU2Matter.lean`) — the cusp notion, the
`N_f = 1` factorization, and the pure no-go:
```lean
def IsCuspOf (Nf : ℕ) (Λ : ℂ) (m : Fin Nf → ℂ) (u₀ : Fin 1 → ℂ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ swCurveMatter Nf Λ m (u₀ 0) = (X - C a) ^ 3 * (X - C b)
```
```lean
theorem swCurveMatter_nf1_ad (Λ : ℂ) :
    swCurveMatter 1 Λ ![-(3 / 4) * Λ] ((3 / 4) * Λ ^ 2)
      = (X + C ((1 / 2) * Λ)) ^ 3 * (X - C ((3 / 2) * Λ))
```
```lean
theorem not_isCuspOf_nf0 (Λ u : ℂ) (m : Fin 0 → ℂ) : ¬ IsCuspOf 0 Λ m ![u]
```
**Check that:** a "cusp" is a triple root **with a distinct** simple root
(`a ≠ b`, strict `A₂`) — this is why the no-go holds for *all* `Λ, u` including
`Λ = 0` (quadruple root, type `A₃`, not a cusp); the factorization is exact
polynomial algebra (closed by `ring`). Footprints: both standard-3 (axiom-free).

## E9. The AD locus is nonempty with matter

**Paper:** §4.5; Appendix B.1′. The locus itself is the *derived* definition
`NonLocalDegenerationLocus` (§4.4, "a surprise comes out derived").

**Informal** (APSW): at the tuned point, two mutually non-local states go massless
together — the derived AD locus is nonempty.

**Formal** (`SeibergWitten/Physics/MatterChart.lean`):
```lean
theorem matter_argyresDouglasLocus_nonempty (Λ : ℂ) (hΛ : Λ ≠ 0) :
    ∃ (B : PeriodBase 1) (s : PeriodChart B),
      IsMatterPolarizedPeriodChart s 1 Λ ![-(3 / 4) * Λ]
        ∧ s.NonLocalDegenerationLocus.Nonempty
```
**Check that:** `IsMatterPolarizedPeriodChart` is the weaker matter bundle (Part
II B.1′) — the theorem exhibits *a* matter theory with a nonempty AD locus, not
yet *the unique* SQCD theory; the constructed witness (2026-07-06) makes that
under-specification a formal fact. Footprint: **standard-3** (was
`+ matterPeriodRigidityAxiom`, DISCHARGED — see B.1′ in Part II).

## E10. The one-loop beta function

**Paper:** §2 (the worked math↔physics instance); Appendix B.2 (its one axiom).
Uses the dictionary's `betaFunction`/`oneLoopCoefficient` (§4.1).

**Informal** (asymptotic freedom at one loop; SW1 §2): at weak coupling the
effective coupling runs with `b₀ = 2N − N_f` (here `N = 2`: `b₀ = 4 − N_f`),
vanishing at `N_f = 4`.

**Formal** (`SeibergWitten/Physics/BetaFunction.lean`); the dictionary value is
```lean
def oneLoopCoefficient (Nf : ℕ) : ℂ := 4 - Nf
```
```lean
theorem betaFunction_weakCoupling (Nf : ℕ) (Λ : ℂ) (hΛ : Λ ≠ 0) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      Tendsto (fun t : ℝ => betaFunction F ((t : ℂ) * Λ ^ 2) Λ) atTop
        (nhds (-(oneLoopCoefficient Nf) / ((Real.pi : ℂ) * I)))
```
**Check that:** `betaFunction` is `Λ ∂_Λ` of the effective coupling along the
weak-coupling ray `u = t·Λ²`; the limit `−b₀/(πi)` versus the axiom's
`(4−N_f)/(2πi)` differ by the factor 2 from `Λ ∂_Λ` vs `s ∂_s` (E10 proves that
conversion). Footprint: **standard-3** (the log-running input was discharged
2026-07-05 — see its entry and `DIFFICULT_POINTS.md` D3 for the existential caveat);
**not** on the headline footprint.

## E11. The modular λ layer (supporting machinery)

**Paper:** §4.3 (the λ bullet); the proved half of Appendix B.2's covering axiom.

**Informal** (classical; rank-1 role in SW via Bilal): `λ = θ₂⁴/θ₃⁴` is
`Γ(2)`-invariant (`Γ(2) = ⟨T², ST²S⁻¹⟩`), with `S : λ ↦ 1−λ`.

**Formal** (`SeibergWitten/Physics/ThetaLambda.lean`):
```lean
noncomputable def modularLambdaFn (τ : ℂ) : ℂ := theta2 τ ^ 4 / theta3 τ ^ 4
```
```lean
theorem modularLambda_add_two (τ : ℂ) : modularLambdaFn (τ + 2) = modularLambdaFn τ
```
```lean
theorem modularLambda_S (τ : UpperHalfPlane) :
    modularLambdaFn (-1 / (τ : ℂ)) = 1 - modularLambdaFn (τ : ℂ)
```
```lean
theorem modularLambda_ST2S (τ : UpperHalfPlane) :
    modularLambdaFn (-1 / (-1 / (τ : ℂ) + 2)) = modularLambdaFn (τ : ℂ)
```
**Check that:** the two theorems for the generators, plus `S`, are invariance of
the *concrete* θ-quotient (Mathlib `jacobiTheta₂` conventions; the oracle pins
`λ(i) = ½`); what is **not** proved is surjectivity/fibres — that remains
`AX_thrice_punctured_uniformization` (Part II). Footprints: `_add_two` standard-3;
`_S` and `_ST2S` standard-3 + the two θ axioms.

## E12. The SU(2) coupling: existence and uniqueness on classical axioms (C-route closure)

**Paper:** §7 (the rank-1 restructuring); the coupling-level half of the headline.

**Informal** (SW1 §§3–6, the τ-level solution): the SU(2) effective coupling exists —
explicitly, `τ(u) = i·K′/K` at the curve's modulus — and is unique up to a `Γ(2)`
duality frame.

**Formal** (`SeibergWitten/Physics/SU2Rigidity.lean`):
```lean
noncomputable def swTau (Λ : ℂ) (u : ℂ) : ℂ :=
  Complex.I * ellipticKm (1 - swCrossRatio Λ u) / ellipticKm (swCrossRatio Λ u)
```
```lean
theorem su2_coupling_exists {Λ : ℂ} (hΛ : Λ ≠ 0) :
    IsSWDevelopingMap Λ (swCrossRatio Λ ⁻¹' EllipticParamDomain) (swTau Λ) ∧
      IsOpen (swCrossRatio Λ ⁻¹' EllipticParamDomain) ∧
      3 * Λ ^ 2 ∈ swCrossRatio Λ ⁻¹' EllipticParamDomain
```
```lean
theorem su2_coupling_canonical {Λ : ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hD : IsPreconnected D) {u₀ : ℂ} (hu₀ : u₀ ∈ D)
    (hsub : D ⊆ swCrossRatio Λ ⁻¹' EllipticParamDomain)
    {f : ℂ → ℂ} (hf : IsSWDevelopingMap Λ D f) :
    ∃ γ ∈ Gamma2, Set.EqOn f (fun u => moebiusOn γ (swTau Λ u)) D
```
**Check that:** existence is **constructive** (the coupling is the C1 witness formula at
the pinned modulus — not an abstract `∃`), on an open chart proved nonempty via the
self-dual anchor `u = 3Λ²` (`m = ½`, `τ = i`); uniqueness is **canonical** (every
developing map agrees with `swTau` up to a literal `Γ(2)` Möbius frame). Footprints
(golden trace): existence = standard-3 + `AX_elliptic_inversion`; uniqueness = that +
the covering pair — **classical axioms only, no bespoke axiom, no physics axiom**. What
this does *not* yet close: the special coordinates `a, a_D`, the prepotential, and
H2/H3/H6 — the `IsPolarizedPeriodChart`-level realize (C2/C3/C4 are reserved for it).

## E13. The special coordinates and H2 at the monopole (milestone S0)

**Paper:** §7 (the special-coordinate layer); H2's `PeriodVanishesAt` shape (§4.2).

**Informal** (SW1 §§2–4; closed forms as in the standard reviews): the special
coordinates of the SU(2) theory are `a = (√2/π)√(u+Λ²)E(m)`,
`a_D = i(√2/π)√(u+Λ²)(K(1−m)−E(1−m))`, and the monopole's central charge `a_D`
vanishes as `u → Λ²`.

**Formal** (`SeibergWitten/Physics/SU2Rigidity.lean`):
```lean
noncomputable def swA (Λ : ℂ) (u : ℂ) : ℂ :=
  ((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ)
    * ellipticEm (swCrossRatio Λ u)
```
```lean
noncomputable def swAD (Λ : ℂ) (u : ℂ) : ℂ :=
  ((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * Complex.I * (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ)
    * (ellipticKm (1 - swCrossRatio Λ u) - ellipticEm (1 - swCrossRatio Λ u))
```
```lean
theorem swAD_tendsto_zero_monopole {Λ : ℂ} (hΛ : Λ ≠ 0) :
    Tendsto (swAD Λ) (𝓝[swCrossRatio Λ ⁻¹' EllipticParamDomain] (Λ ^ 2)) (𝓝 0)
```
**Check that:** the closed forms were **pinned by computation**
(`numerical/validate_specialcoords.py`, 14/14: the `K−E` bracket is the unique
candidate matching the B-period, ratio exactly `½`; `da_D/da = swTau` to `1e−15`; the
`√2/π` prefactor fixed by weak-coupling `a ~ √(u/2)`); the vanishing theorem is stated
in exactly H2's `PeriodVanishesAt` filter shape (limit **within the chart**), footprint
now **standard-3 — axiom-free** (the needed cusp limits were discharged into theorems
by the loop's first iteration). What S0 does *not* yet prove: the H6 asymptotics.
The H1 relation `da_D/da = τ` is now **proved** — milestone S1, entry E14.

---

## E14. Special geometry on the chart: `da_D/da = τ` (milestone S1)

**Paper:** §7 (the special-coordinate layer); H1's special-geometry shape (§4.2).

**Informal** (SW1 §§2–4; standard reviews): the special coordinates satisfy the
defining relation of special geometry, `da_D/da = τ`; explicitly, on the coupling
chart `da/du = (√2/2π)·K(m)/√(u+Λ²)` and `da_D/du = i(√2/2π)·K(1−m)/√(u+Λ²)`, whose
ratio is `τ = i·K(1−m)/K(m)`.

**Formal** (`SeibergWitten/Physics/SU2Rigidity.lean`; both derivative theorems are
**standard-3 — axiom-free**, the ratio consumes only C1's `K ≠ 0` clause):
```lean
theorem swA_hasDerivAt {Λ u : ℂ} (hm : swCrossRatio Λ u ∈ EllipticParamDomain)
    (hslit : u + Λ ^ 2 ∈ Complex.slitPlane) :
    HasDerivAt (swA Λ)
      (((Real.sqrt 2 / Real.pi : ℝ) : ℂ) / 2
        * (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - 1)
        * ellipticKm (swCrossRatio Λ u)) u
```
```lean
theorem swAD_hasDerivAt {Λ u : ℂ} (hm : swCrossRatio Λ u ∈ EllipticParamDomain)
    (hslit : u + Λ ^ 2 ∈ Complex.slitPlane) :
    HasDerivAt (swAD Λ)
      (((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * Complex.I / 2
        * (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - 1)
        * ellipticKm (1 - swCrossRatio Λ u)) u
```
```lean
theorem swAD_deriv_eq_swTau_mul_swA_deriv {Λ u : ℂ}
    (hm : swCrossRatio Λ u ∈ EllipticParamDomain)
    (hslit : u + Λ ^ 2 ∈ Complex.slitPlane) :
    HasDerivAt (swAD Λ)
      (swTau Λ u
        * (((Real.sqrt 2 / Real.pi : ℝ) : ℂ) / 2
          * (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - 1)
          * ellipticKm (swCrossRatio Λ u))) u
```
**Check that:** `X^{↑(1/2)−1}` (`X = u+Λ²`) is the honest principal-branch
`1/√(u+Λ²)` up to the branch bookkeeping — the hypotheses restrict to the slit-plane
regime where `cpow` is the classical function (same convention as E13's closed
forms, which were numerically pinned; `da_D/da = swTau` itself was pinned to
`1e−15` in `numerical/validate_specialcoords.py` **before** these proofs); the
ratio statement is the chain-rule form — `HasDerivAt (swAD Λ) (swTau·(da/du)) u` —
i.e. `a_D` has derivative `τ·a′(u)`, which is `da_D/da = τ` wherever `a′ ≠ 0`,
stated without division to avoid junk values. The derivatives come from the
**proved** Legendre ODEs (the C2-discharge machinery), not from new axioms: the
only non-logical axiom anywhere in E14 is `AX_elliptic_inversion` supplying
`K(m) ≠ 0` for the ratio.

---

## E15. The τ-derivative layer: Wronskian, closed-form `dτ/du`, one-loop running

**Paper:** §7 (rank-1 restructuring); H6's one-loop shape (§4.2); the D3 remedy.

**Informal** (WW §22.7 / SW1 §3): the period ratio satisfies the Wronskian identity
`dτ/dm = −iπ/(4m(1−m)K²)` (a corollary of the Legendre relation); at the curve's
modulus this gives `dτ/du = iπ/(4(u+Λ²)(1−m)K²)`; and at weak coupling the coupling
runs logarithmically, `u·dτ/du → i/π` (λ-normalization `τ ≈ (i/π)log u`), and
`a ≈ √(u/2)`.

**Formal** (footprints: standard-3 + `AX_elliptic_inversion` (its `K ≠ 0` clause)
for the first three, standard-3 alone for the last).
**Formal** (`SeibergWitten/Physics/EllipticIntegrals.lean`):
```lean
theorem tau_ratio_hasDerivAt {m : ℂ} (hm : m ∈ EllipticParamDomain) :
    HasDerivAt (fun m : ℂ => Complex.I * ellipticKm (1 - m) / ellipticKm m)
      (-(Complex.I * (Real.pi : ℂ)) / (4 * m * (1 - m) * ellipticKm m ^ 2)) m
```
**Formal** (`SeibergWitten/Physics/SU2Rigidity.lean`):
```lean
theorem swTau_hasDerivAt {Λ u : ℂ} (hm : swCrossRatio Λ u ∈ EllipticParamDomain) :
    HasDerivAt (swTau Λ)
      (Complex.I * (Real.pi : ℂ)
        / (4 * (u + Λ ^ 2) * (1 - swCrossRatio Λ u)
          * ellipticKm (swCrossRatio Λ u) ^ 2)) u
```
```lean
theorem swTau_logDeriv_weakCoupling (Λ : ℂ) :
    Tendsto (fun u : ℂ => u * deriv (swTau Λ) u)
      (Bornology.cobounded ℂ ⊓ Filter.principal (swCrossRatio Λ ⁻¹' EllipticParamDomain))
      (𝓝 (Complex.I / (Real.pi : ℂ)))
```
```lean
theorem swA_weakCoupling (Λ : ℂ) :
    Tendsto (fun u : ℂ => swA Λ u / (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ))
      (Bornology.cobounded ℂ ⊓ Filter.principal (swCrossRatio Λ ⁻¹' EllipticParamDomain))
      (𝓝 ((Real.sqrt 2 / 2 : ℝ) : ℂ))
```
**Check that:** the Wronskian's numerator is collapsed by the *proved*
`legendre_relation` (this is where C2's content does real work); the weak-coupling
filter is `cobounded ⊓ 𝓟(chart)` — large `|u|` *within* the coupling chart, the
honest reading of `u → ∞` on the universal-cover carrier; the log-running constant
is `i/π` in the **λ-convention** (`swTau = i·K′/K` with `λ(τ) = m`), and the
conversion to the physics `b₀` normalization is a *documented dictionary factor*,
not a silent identification — this is the curve-tied statement whose absence in the
old axiom was the D3 finding. All four closed forms and constants are
oracle-checked (`numerical/validate_taulayer.py`, 21/21 at 40 digits, including the
`O(1/u)` rate).

---

## E16. Matter (N_f > 0): the j-anchored layer and coupling rigidity

**Paper:** §4.5 (the matter worked example); `MATTER_CLASSICAL_PLAN.md` (archived, local `history/audit/`).

**Informal** (SW2; APSW): the `N_f` coupling develops the matter curve's modular
data; two couplings with the same development agree up to a duality frame; the
Argyres–Douglas point is where the curve's Weierstrass invariants vanish.

**Formal** (`SeibergWitten/Physics/MatterInvariants.lean`):
```lean
def DevelopsMatterJ (Nf : ℕ) (Λ : ℂ) (m : Fin Nf → ℂ) (D : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ u ∈ D, jLambda (modularLambdaFn (2 * f u)) = quarticJ (swCurveMatter Nf Λ m u)
```
```lean
theorem matter_coupling_rigidity {Nf : ℕ} {Λ : ℂ} {m : Fin Nf → ℂ}
    {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    {u₀ : ℂ} (hu₀ : u₀ ∈ D) {f g : ℂ → ℂ}
    (hmono : SameMatterMonodromy Nf Λ m D f g)
    (hreg : ∀ u ∈ D, AnharmonicRegular (modularLambdaFn (2 * f u)))
    (hcusp : ∀ u ∈ D,
      modularLambdaFn (2 * g u) ≠ 0 ∧ modularLambdaFn (2 * g u) ≠ 1) :
    ∃ i : Fin 6, ∃ γ ∈ Gamma2,
      Set.EqOn (fun u => 2 * g u)
        (fun u => SU2.moebiusOn γ (anharmonicWord i (2 * f u))) D
```
```lean
theorem matter_nf1_ad_invariants (Λ : ℂ) :
    quarticG2 (swCurveMatter 1 Λ ![-(3 / 4) * Λ] ((3 / 4) * Λ ^ 2)) = 0 ∧
    quarticG3 (swCurveMatter 1 Λ ![-(3 / 4) * Λ] ((3 / 4) * Λ ^ 2)) = 0
```
**Check that:** the developing condition anchors `λ(2·f)` — the **doubling is the
Landen dictionary item** (the quartic's intrinsic modulus is `2τ_SW`; caught by the
numeric gate before formalization) — through two proved layers (`jLambda` with its
proved anharmonic invariances; `quarticJ` off `Polynomial.coeff`); the rigidity
footprint is **the θ pair + the covering pair only** (`#print axioms` in the golden
trace — no matter-specific axiom, no elliptic axiom), with the frame `Γ(2)` times
one explicit anharmonic word at the doubled level; the regularity hypotheses are
honest (the θ axioms do not exclude `λ = 1` globally) and **numerically witnessed
satisfiable** (`validate_matterj.py` check F, margins `~0.06`); the AD invariant
statement is proved by two independent routes. What remains on
`matterPeriodRigidityAxiom` is **existence only** (the period chart's `realize`
debt, same species as `periodRigidityAxiom`) — its rigidity role is retired.

---

## E17. The singularity count: why exactly one monopole–dyon pair

**Paper:** the informal uniqueness argument (§4.3); `SINGULARITY_COUNT_PLAN.md` (archived, local `history/audit/`).

**Informal** (SW1 §4; Kodaira's table; Seiberg holomorphy): SW *assume* the u-plane
has exactly two strong-coupling singularities. The count is pinned conditionally, by
hypotheses carried in the theorem statement (audit labels (P1)–(P3) — file-local,
deliberately NOT added to the H-roster): (P1) each finite singularity is a Kodaira `I_k` fiber (k mutually local
massless BPS states — monodromy `~ Tᵏ`); (P2) the weak-coupling fiber at infinity is
`I*_m` (one-loop monodromy `M∞ = −Tᵐ`; `m = 4` for pure SU(2), the −1 from `a ~ √u`);
(P3) holomorphy in Λ + mass dimensions + ℤ₈ anomaly quantization put
`g₂ ∈ span{u², Λ⁴}`, i.e. `deg_u g₂ ≤ 2`. Then the Euler-type counting
`#singularities = 12l − (m+6)` (which ALONE only gives `n ≡ 1 mod 6` — the K3
loophole at `l = 2` with fourteen `I₁`s is real, witnessed numerically) collapses
at `l = 1` to exactly one pair.

**Formal** (`SeibergWitten/Physics/SingularityCount.lean`):
```lean
def IsKodairaI (g₂ g₃ : ℂ[X]) (k : ℕ) (u₀ : ℂ) : Prop :=
  rootMultiplicity u₀ (wDisc g₂ g₃) = k ∧ g₂.eval u₀ ≠ 0
```
```lean
def InftyIStar (g₂ g₃ : ℂ[X]) (l m : ℕ) : Prop :=
  wDisc g₂ g₃ ≠ 0 ∧
  g₂.natDegree + 2 = 4 * l ∧ g₃.natDegree + 3 = 6 * l ∧
  (wDisc g₂ g₃).natDegree + (m + 6) = 12 * l
```
```lean
def AnomalyGraded (g₂ : ℂ[X]) : Prop :=
  g₂.natDegree ≤ 2 ∧ g₂.coeff 1 = 0
```
```lean
theorem singularity_count_pinch {g₂ g₃ : ℂ[X]} {l k m : ℕ} (hk : k ≠ 0)
    (hdeg : AnomalyGraded g₂)
    (hinf : InftyIStar g₂ g₃ l m)
    (hfib : ∀ u₀ ∈ (wDisc g₂ g₃).roots, IsKodairaI g₂ g₃ k u₀)
    (hkm : 2 * k + m = 6) :
    (wDisc g₂ g₃).roots.toFinset.card = 2
```
**Check that:** (i) the Kodaira transcriptions are the standard valuation triples
(`I_k`: `v(Δ) = k, v(g₂) = 0`; `I*_m`: `(2, 3, m+6)` in the twist-`l` chart, stated
additively — no ℕ-subtraction traps); the dictionary valuations ⟷ monodromy classes
is Kodaira's table, **cited not formalized** — no Lean statement mentions monodromy,
so the physics enters only through the postulate names. (ii) `InftyIStar` carries
`wDisc ≠ 0` explicitly and `g₂ = 0 / g₃ = 0` are arithmetically self-excluded
(`natDegree 0 = 0` cannot satisfy `2 = 4l` or `3 = 6l`) — no zero-polynomial
degree lies. (iii) The gloss "n pairs ⇒ n = 1" is delivered as
`toFinset.card = 2`; the ℤ₂ pairing (that the two points are `±w`) is NOT smuggled
into the abstract statement — it comes only from the instantiation
(`sw_singular_values`: the pair is exactly `{Λ², −Λ²}`, matching
`su2_singular_locus`). (iv) `AnomalyGraded` — formerly the one **non-manifest** physical input, now a
THEOREM from the R-spurion covariance of the curve family — the curve-level shadow of
**H7** (`SpurionCovariantFamily`, Hypotheses.lean: spurionic `U(1)_R` covariance of the
`Λ`-family; the Witten-effect frame shift an integer symmetric matrix constant across
the family; H5 and H6's homogeneity clause are its fixed-`Λ` shadows, the latter proved
as `instanton_remainder_covariant`):
```lean
structure RSpurionCovariant (G₂ : ℂ → ℂ[X]) : Prop where
  scale : ∀ (t Λ : ℂ), t ≠ 0 → ∀ u : ℂ,
    (G₂ (t * Λ)).eval (t ^ 2 * u) = t ^ 4 * (G₂ Λ).eval u
  quantized : ∀ Λ : ℂ, G₂ (Complex.I * Λ) = G₂ Λ
  regular : ∀ j : ℕ, ∃ L : ℂ,
    Filter.Tendsto (fun Λ => (G₂ Λ).coeff j) (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds L)
```
— three manifestly physical clauses (mass dimensions; the anomalous `U(1)_R` exact with
the instanton factor `Λ⁴` as spurion, one-loop exact by Adler–Bardeen; Seiberg
holomorphy/weak-coupling regularity), from which
`anomalyGraded_of_rSpurionCovariant` derives the grading: odd coefficients die
algebraically (`t = i` scaling vs. quantization — the half-instanton argument), higher
coefficients would blow up at `Λ → 0`. Both SW frames satisfy the covariance
(`rSpurionCovariant_swG2`, `'`). The fixed-Λ `AnomalyGraded` still states the faithful grading
(`deg ≤ 2` AND `coeff 1 = 0`: a `u¹` term would need a weight-2 `Λ²`, anomaly-forbidden),
not just the consumed degree bound; both frames satisfy the full clause
(`sw_anomalyGraded`, `'`). (v) Non-vacuity both ways: the repo curve instantiates every
hypothesis in both frames (`sw_exactly_two_singularities`, `'`); dropping ONLY
`hdeg` admits the explicit K3 witness (`validate_singcount.py` §D: deg 6/9/14, all
fourteen roots simple) — so (P3) is necessary, not decorative. Scope: the count is
pinned within the algebraic Weierstrass ansatz class (`g₂, g₃` polynomial in `u`);
the ansatz-free statement is the ALLM rank-1 classification, out of scope.


## E18. The developing base derived: qualitative cusp data ⟹ the pinned formula

**Paper:** §4.2 (the exhaustive hypothesis list); `DEVELOPING_BASE_PLAN.md` (archived, local `history/audit/`).

**Informal** (SW1 §§3–4): the effective coupling has the SW monodromy — around the
monopole/dyon points the specific `Γ(2)`-conjugate parabolics, at infinity the one-loop
`−T⁴` — and this forces it to track the curve's modulus. The formalization previously
carried the conclusion as the pinned developing formula `λ(τ(u)) = 2Λ²/(u+Λ²)`; this
layer derives the formula from qualitative data only, so the strong-looking clause is a
theorem, not a postulate.

**Formal** (`SeibergWitten/Physics/DevelopingBase.lean`):
```lean
structure SWModulusData (Λ : ℂ) (J : ℂ → ℂ) : Prop where
  diff : ∀ u : ℂ, u ≠ Λ ^ 2 → u ≠ -Λ ^ 2 → DifferentiableAt ℂ J u
  ne_zero : ∀ u : ℂ, u ≠ Λ ^ 2 → u ≠ -Λ ^ 2 → J u ≠ 0
  ne_one : ∀ u : ℂ, u ≠ Λ ^ 2 → u ≠ -Λ ^ 2 → J u ≠ 1
  monopole : Tendsto J (𝓝[≠] (Λ ^ 2)) (𝓝 1)
  dyon : Tendsto (fun u => (J u)⁻¹) (𝓝[≠] (-Λ ^ 2)) (𝓝 0)
  weak : Tendsto J (cocompact ℂ) (𝓝 0)
```
```lean
theorem swModulusData_eq_crossRatio {Λ : ℂ} (hΛ : Λ ≠ 0) {J : ℂ → ℂ}
    (h : SWModulusData Λ J) :
    ∀ u : ℂ, u ≠ Λ ^ 2 → u ≠ -Λ ^ 2 → J u = swCrossRatio Λ u
```
**Check that:** (i) the hypotheses are genuinely *qualitative* — three limits and two
omitted values; no rates, no coefficients. The degree (`p = 1`), the cusp rates, and the
normalization `2Λ²` are all conclusions (proof chain: Riemann removability → entire
reciprocal → finite vanishing order + factorization → polynomial-growth Liouville
(`entire_polynomial_of_growth`, dslope induction) → nonvanishing polynomial is constant →
`p`-th-root distinctness pinches `p = 1`, and the single 1-point pins `c₀ = 2Λ²`).
(ii) What is NOT derived, stated honestly: single-valuedness of `J` on the full punctured
plane is the H3+H4 residue (SW monodromies ⊂ `Γ(2)·{±1}`); the cusp assignments are H2's
which-state-where; the two-puncture domain is the count (E17). These are the surviving
physical inputs, all qualitative. (iii) Footprints: the derivation and the non-vacuity
witness (`swModulusData_swCrossRatio`) are **standard-3 — no axioms at all**; the
decomposed headline `sw_su2_unique_of_modulusData` adds exactly the covering pair,
identical to `sw_su2_unique`. (iv) Non-vacuity both ways (`validate_devbase.py`, 13/13):
the cross-ratio satisfies the data; the `p = 2` candidate `4Λ⁴/(u+Λ²)²` passes every cusp
clause and fails ONLY omit-1, at the smooth point `u = −3Λ²` — an extra would-be
singularity, so the killing clause is physics.

## E19. The cusp data derived: atlas + genuine cusp lifts ⟹ `SWModulusData`

**Paper:** §4.2 (the cusp-data bullet, closing sentence); `CUSP_DATA_PLAN.md` (archived, local `history/audit/`).

**Informal** (SW1 §§3–4): the coupling is a multivalued function on the punctured
u-plane, glued across sheets by electric–magnetic duality (H4); around each puncture it
has the parabolic monodromy of the state that goes massless there (H2+H3), and it
genuinely degenerates — the monopole/dyon points because a state goes massless, infinity
by asymptotic freedom. From this qualitative data the whole cusp structure of the
modulus observable follows.

**Formal** (`SeibergWitten/Physics/CuspData.lean`):
```lean
structure IsGenuineCuspLift (k : ℕ) (T : ℂ → ℂ) : Prop where
  one_le : 1 ≤ k
  diff : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ T w
  im_pos : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, 0 < (T w).im
  equivariant : ∀ w : ℂ, T (w + 1) = T w + k
  genuine : ¬ ∃ M : ℝ, ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop, (T w).im ≤ M
```
```lean
theorem swModulusData_of_atlas_and_lifts {Λ : ℂ} {ι : Type*} {chart : ι → Set ℂ}
    {τloc : ι → ℂ → ℂ}
    (h : IsSWCouplingAtlas {u : ℂ | u ≠ Λ ^ 2 ∧ u ≠ -Λ ^ 2} chart τloc)
    {kw km kd : ℕ} {Tw Tm Td : ℂ → ℂ}
    (hTw : IsGenuineCuspLift kw Tw) (hTm : IsGenuineCuspLift km Tm)
    (hTd : IsGenuineCuspLift kd Td)
    (hJw : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop,
      atlasModulus chart τloc ((Function.Periodic.qParam 1 w)⁻¹)
        = modularLambdaFn (Tw w))
    (hJm : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop,
      atlasModulus chart τloc (Λ ^ 2 + Function.Periodic.qParam 1 w)
        = 1 - modularLambdaFn (Tm w))
    (hJd : ∀ᶠ w : ℂ in Filter.comap Complex.im Filter.atTop,
      atlasModulus chart τloc (-Λ ^ 2 + Function.Periodic.qParam 1 w)
        = (modularLambdaFn (Td w) - 1) / modularLambdaFn (Td w)) :
    SWModulusData Λ (atlasModulus chart τloc)
```
**Check that:** (i) `IsGenuineCuspLift` is the honest per-puncture input — parabolic
equivariance is H3's `Tᵏ` (with `k` free, not hard-wired to 2), and `genuine` is
NON-EXTENSION (`Im T` unbounded), not a rate or a limit: the dichotomy supplies the
limit, so nothing about the conclusion is smuggled into the hypothesis (the D3 trap the
plan flagged). (ii) The three frame composites (`λ`, `1 − λ`, `(λ−1)/λ`) are forced by
which cusp each proved-parabolic monodromy fixes (`i∞`, `0`, `1` — `swM*_trace` and the
oracle's fixed-cusp checks; the v1 hyperbolic slip is DIFFICULT_POINTS B7). (iii) The
transport is onto: the cover maps send `comap im atTop` ONTO `𝓝[≠] u₀` and onto
`cocompact ℂ` (`nhdsNE_le_map_qParam`, `cocompact_le_map_inv_qParam`), so no directional
weakening sneaks in. (iv) Footprints: `cusp_dichotomy` and the transport are
**standard-3**; the λ-layer (invariance, D2 estimate, endgame) is θ-pair only; the
covering pair enters solely at the final rigidity step, unchanged. (v) The residual
assumed content after this layer: the atlas structure (H4 as definition), the parabolic
classes with point assignments (H2+H3), the two non-extension clauses (H2, H6-qual),
the count (E17), and the classical covering axioms — all qualitative.

## Deliberate design choices (check equivalent, don't flag)

- **Universal-cover carrier.** `a, a_D, τ` live on simply-connected charts
  (`PeriodChart`, `hVsc`), never as global functions of `u` — global
  single-valuedness is *false* (Liouville + removable singularities; paper §4.4).
  Multivaluedness is the atlas, glued by `SymplecticReframing`.
- **Existential-phase statements.** E3 asserts existence of the period matrix in
  Siegel space, not yet its variation over moduli; the variation is the named debt
  (`periodRigidityAxiom`), not a hidden gloss.
- **Typed positivity.** `Im τ ≻ 0` and `τ = τᵀ` are carried by the
  `SiegelUpperHalfSpace` type, so several statements need no separate positivity
  clause — read the type, not only the conclusion.
- **SU(N) slice.** `Monic` + `coeff (N−1) = 0` (trace-free) is the SU(N) family;
  an earlier draft quantified over U(N) and was corrected (adversarial review).
- **Nat-subtraction guards.** `2 ≤ N` and (matter) `N_f ≤ 3`, `Λ ≠ 0` prevent
  `N − 1` / `4 − N_f` truncation artifacts; they are soundness guards, not
  physical restrictions.
- **H5 order convention.** "Order dividing 2N" (not "exactly 2N") — the faithful
  statement on the moduli; see `../AXIOM_AUDIT.md` (resolved 2026-06-30) and paper
  §4.4.
- **Math-primary naming.** Statements use mathematical vocabulary; the physics
  names are machine-linked `abbrev`s in `Physics/Dictionary.lean` (paper §4.1) —
  check the dictionary once, not per theorem.
- **Uninterpreted placeholders are labeled as such.** `localMonodromy` (a function
  with no definition) declares an *interface* for the pending Gauss–Manin layer.
  (`SameSWMonodromy`, formerly the other placeholder, was demoted to a definition
  2026-07-04 — see Part II.) They are listed in Part II, not hidden.
