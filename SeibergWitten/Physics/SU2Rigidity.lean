/-
# SU(2) period-map rigidity — scoping skeleton (Phase 1b)

Target: demote the headline `sw_effective_theory_unique_up_to_duality`
(`Physics/Hypotheses.lean`) from a physical axiom to a **theorem**, for the rank-1
(SU(2)) case. Proving the implication moves a *mathematical* claim out of the physics
axiom list, leaving only the genuinely-physical inputs — see
`docs/reasoning-from-physics-axioms.md`.

## The argument (SU(2))

The SU(2) Coulomb branch is the `u`-plane; the curve `y² = (x²−u)² − Λ⁴` degenerates at
`u = ±Λ²` (monopole / dyon points) and `u = ∞` (semiclassical region). So the smooth
base is the **thrice-punctured sphere** `ℙ¹ ∖ {Λ², −Λ², ∞} ≅ ℂ ∖ {±Λ²}`. The effective
coupling `τ(u)` is a holomorphic map from (the universal cover of) this base to the
upper half plane `ℍ ≅ SiegelUpperHalfSpace 1`, multivalued with `Sp(2,ℤ)` monodromy
around the punctures.

Rigidity: *any* holomorphic period map with the SW monodromy and the prescribed
semiclassical asymptotics equals the SW one, **up to an `Sp(2,ℤ) = SL(2,ℤ)` frame
change**. The argument has two pieces:

1. **Uniformization (the wall).** The thrice-punctured base is uniformized by `ℍ`
   (the modular `λ`-function / a `Γ(2)` Hauptmodul). This pins the developing map up to
   the deck group; matching the monodromy and one cusp fixes the `SL(2,ℤ)` frame. *Not
   in Mathlib* — no `λ`/`j`, no uniformization, no `Sp(2,ℤ)`-action-on-`ℍ` layer.
   Split into two named **classical-math** axioms: the `Γ(2)` covering
   `AX_thrice_punctured_uniformization` (ModularLambda) and the lift-uniqueness step
   `AX_developing_map_rigidity`; the bespoke `AX_su2_modular_frame_alignment` is retired,
   `su2_frame_alignment` now deriving it from those two.
2. **Propagation (reachable today).** Once two solutions are put in a common frame near
   the semiclassical cusp, the **identity theorem** for holomorphic functions forces
   them to agree on the whole connected base. This is `holo_eqOn_of_germ` below, proved
   from Mathlib's `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.

## Reachability (this file)

| Piece | Status |
|---|---|
| Analytic propagation (identity theorem) | **proved** (`holo_eqOn_of_germ`) |
| Elliptic periods / `τ ∈ SiegelUpperHalfSpace 1` | in `jacobian-challenge` (axiom-free) |
| Modular-`λ` uniformization | **math axioms** — `Γ(2)` covering + lift-uniqueness |
| monodromy input | **definition** — `SameSWMonodromy` (demoted from an axiom 2026-07-04) |

So `sw_su2_unique` is a **theorem** whose kernel footprint is the *classical-math*
covering + lift-uniqueness axioms only; the physics enters as a contentful hypothesis in
its type (the pinned developing property), no longer as an axiom. The analytic core is
proved. Discharging the covering upstream (Schwarz reflection ⇒ Riemann mapping ⇒ the `Γ(2)`
cover — the conformal-mapping programme) and the lift-uniqueness step removes the math debt.

References: Seiberg–Witten, hep-th/9407087 §3–4 (SU(2) monodromy, `u`-plane);
Lerche, hep-th/9611190 §3; for uniformization: the modular `λ`-function / `Γ(2)`.
-/
import SeibergWitten.Physics.Hypotheses
import SeibergWitten.Physics.ModularLambda
import SeibergWitten.Physics.EllipticIntegrals
import Mathlib.Analysis.Analytic.Uniqueness

open Complex Filter Topology

namespace SeibergWitten.Physics.SU2

/-- **Analytic propagation (the reachable core).** Two holomorphic functions on a
preconnected open set that agree on a neighbourhood of one point agree everywhere on it.
This is the identity theorem; it is what makes period maps *rigid once the duality frame
is fixed*. Proved from Mathlib. -/
theorem holo_eqOn_of_germ {D : Set ℂ} (hD : IsPreconnected D) {u₀ : ℂ} (hu₀ : u₀ ∈ D)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) (hg : AnalyticOnNhd ℂ g D)
    (hfg : f =ᶠ[𝓝 u₀] g) : Set.EqOn f g D :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg hD hu₀ hfg

/-- The SU(2) singular locus on the `u`-plane: the monopole and dyon points `u = ±Λ²`.
(The third puncture, `u = ∞`, is the semiclassical region.) A holomorphic period map
lives on a connected chart of the complement `(singularSet Λ)ᶜ`. -/
def singularSet (Λ : ℂ) : Set ℂ := {Λ ^ 2, -Λ ^ 2}

/-- **Same SW monodromy — now a `def`, demoted from an uninterpreted axiom (2026-07-04).**
Both candidate couplings develop the curve's pinned modulus `swCrossRatio Λ` on the chart
`D` — they are two lifts of the *same* base map through the `λ`-covering. Anchored to the
geometry per the C-route review (Q11: pinning both maps to the cross-ratio beats comparing
them to each other, which is conjugacy-ambiguous); the modulus itself was pinned
numerically against the actual curve periods
(`audit/numerical/validate_swcrossratio.py`). With this, the rank-1 rigidity theorem
carries its physics as a **contentful hypothesis in its type**, and no physics axiom
remains on its kernel footprint. -/
def IsSWDevelopingMap (Λ : ℂ) (D : Set ℂ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f D ∧ (∀ u ∈ D, 0 < (f u).im) ∧ DevelopsSWCrossRatio Λ D f

/-- Two candidate couplings carry the same SW monodromy iff **both are developing maps**
of the pinned modulus. All three clauses of `IsSWDevelopingMap` are load-bearing:
analyticity and ℍ-valuedness rule out the choice-built and junk-value inhabitants that
would refute the lift-uniqueness axiom below (a pointwise `λ∘f = λ∘g` alone admits
discontinuous lifts via the proved `τ ↦ τ+2`, and off `ℍ` the θ-series are junk, so at
`Λ = 0` lower-half-plane maps satisfy the developing equation vacuously — both found in
self-review; `audit/DIFFICULT_POINTS.md` B4). -/
def SameSWMonodromy (Λ : ℂ) (D : Set ℂ) (f g : ℂ → ℂ) : Prop :=
  IsSWDevelopingMap Λ D f ∧ IsSWDevelopingMap Λ D g

/-- The Möbius action of an integral `SL(2,ℤ)` matrix on `ℂ` (junk where the denominator
vanishes — which never happens on `ℍ`: `moebius_denom_ne_zero`). This is the concrete form
of the deck/duality frame change acting on coupling values. -/
noncomputable def moebiusOn (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : ℂ) : ℂ :=
  ((γ.1 0 0 : ℤ) * z + (γ.1 0 1 : ℤ)) / ((γ.1 1 0 : ℤ) * z + (γ.1 1 1 : ℤ))

/-- On the upper half-plane the Möbius denominator never vanishes: for `c, d` the bottom
row of an `SL(2,ℤ)` matrix and `Im z > 0`, `c·z + d ≠ 0` (if `c = 0` then `d = ±1`; if
`c ≠ 0` the imaginary part is `c·Im z ≠ 0`). -/
theorem moebius_denom_ne_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {z : ℂ}
    (hz : 0 < z.im) : ((γ.1 1 0 : ℤ) : ℂ) * z + ((γ.1 1 1 : ℤ) : ℂ) ≠ 0 := by
  intro h
  rcases eq_or_ne (γ.1 1 0) 0 with hc | hc
  · -- c = 0: the determinant forces d ≠ 0, but the equation says d = 0
    have hdet := γ.2
    rw [Matrix.det_fin_two] at hdet
    rw [hc] at hdet h
    push_cast at h
    simp only [zero_mul, zero_add] at h
    have hd0 : γ.1 1 1 = 0 := by exact_mod_cast h
    rw [hd0] at hdet
    simp at hdet
  · -- c ≠ 0: compare imaginary parts
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.zero_im, zero_mul, add_zero] at him
    have : ((γ.1 1 0 : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.mp him with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hz)
    exact hc (by exact_mod_cast this)

/-- A Möbius frame change composed with an ℍ-valued analytic map is analytic — the
bridge that lets the identity theorem propagate a Γ(2)-frame germ across the chart. -/
theorem analyticOnNhd_moebius_comp {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {g : ℂ → ℂ} {D : Set ℂ} (hg : AnalyticOnNhd ℂ g D) (hgH : ∀ u ∈ D, 0 < (g u).im) :
    AnalyticOnNhd ℂ (fun u => moebiusOn γ (g u)) D := by
  intro u hu
  exact ((analyticAt_const.mul (hg u hu)).add analyticAt_const).div
    ((analyticAt_const.mul (hg u hu)).add analyticAt_const)
    (moebius_denom_ne_zero γ (hgH u hu))

/-- **Classical math axiom — uniqueness of developing maps (lift rigidity).**

    *Given* the thrice-punctured uniformization `U : ThricePuncturedUniformization` (the
    `ℍ → ℂ∖{0,1}` `Γ(2)`-cover), two holomorphic period maps `f, g` on a connected chart
    `D` that develop the *same* base map (`SameSWMonodromy`, now the defined pinned
    developing property) are two lifts of it through the cover, hence differ by a deck
    transformation; matching one cusp. `SameSWMonodromy`'s analyticity and ℍ-valuedness
    clauses are **load-bearing** (see its docstring): a bare pointwise developing
    equation admits choice-built and junk-value inhabitants that refute this axiom —
    the demotion exposed what the old opaque relation silently assumed;
    fixes it to a single **`Γ(2)` deck transformation** `γ` aligning the Möbius image of
    `g` with `f` near `u₀` (strengthened per external review 2026-07-04: the earlier
    `∃ m : ℂ → ℂ` conclusion abandoned the group structure — the unused covering argument
    was the tell). This is the classical monodromy theorem / uniqueness-of-lifts step.

    It is a *mathematical* axiom (true classical analysis), not a physical input, and it
    explicitly **consumes the covering** `AX_thrice_punctured_uniformization`: discharging
    that covering upstream (Schwarz reflection ⇒ Riemann mapping ⇒ the `Γ(2)` cover) leaves
    only this lift-uniqueness step, itself standard. Together they are the math debt behind
    the SU(2) headline; neither is physics.
    **v2, generalized (2026-07-05, the MC3 review's Q3 fix):** the base-map equality is
    now the generic `λ∘f = λ∘g` on `D` rather than the `swCrossRatio`-specialized
    `SameSWMonodromy` bundle — the classical lift-uniqueness statement never depended on
    *which* base map the two lifts share. Scrutiny record for the new signature: the
    analyticity and ℍ-valuedness of BOTH maps are now explicit hypotheses (they block the
    catalogued B4 falsifiers — lower-half-plane junk inhabitants and discontinuous lifts
    through the proved `τ ↦ τ+2` invariance); `λ` omits `{0,1}` on `ℍ` (classical, part
    of the covering content as before); the constant-maps instance is satisfied by
    `γ = 1`. The former specialized statement is recovered at the call site
    (`su2_frame_alignment`) by unpacking `SameSWMonodromy` — footprints unchanged.
    References: Forster, *Lectures on Riemann Surfaces* (monodromy theorem, deck
    transformations); Ahlfors, *Conformal Invariants*; SW hep-th/9407087 §3–4 for the
    `u`-plane monodromy. (NOT VERIFIED.) -/
axiom AX_developing_map_rigidity
    {D : Set ℂ} {u₀ : ℂ} {f g : ℂ → ℂ}
    (U : ThricePuncturedUniformization)
    (hD : IsOpen D) (hu₀ : u₀ ∈ D)
    (hf : AnalyticOnNhd ℂ f D) (hfH : ∀ u ∈ D, 0 < (f u).im)
    (hg : AnalyticOnNhd ℂ g D) (hgH : ∀ u ∈ D, 0 < (g u).im)
    (hbase : ∀ u ∈ D, modularLambdaFn (f u) = modularLambdaFn (g u)) :
    ∃ γ ∈ Gamma2, f =ᶠ[𝓝 u₀] fun u => moebiusOn γ (g u)

/-- **SU(2) modular frame alignment — now derived.** The frame change `m` aligning two
    same-monodromy period maps, obtained from the classical math axioms only: the
    `Γ(2)` covering (`AX_thrice_punctured_uniformization`) supplies the uniformizing cover,
    and `AX_developing_map_rigidity` is the uniqueness-of-lifts step on it. Formerly the
    bespoke axiom `AX_su2_modular_frame_alignment`; it is now a theorem modulo those two
    named classical-math axioms. -/
theorem su2_frame_alignment
    {Λ : ℂ} {D : Set ℂ} {u₀ : ℂ} {f g : ℂ → ℂ}
    (hD : IsOpen D) (hu₀ : u₀ ∈ D)
    (hmono : SameSWMonodromy Λ D f g) :
    ∃ γ ∈ Gamma2, f =ᶠ[𝓝 u₀] fun u => moebiusOn γ (g u) := by
  obtain ⟨⟨hfA, hfH, hfDev⟩, hgA, hgH, hgDev⟩ := hmono
  exact AX_developing_map_rigidity AX_thrice_punctured_uniformization.some hD hu₀
    hfA hfH hgA hgH (fun u hu => by rw [hfDev u hu, hgDev u hu])

/-- **SU(2) period-map rigidity (`sw_su2_unique`).**

    Two holomorphic effective-coupling maps on a connected chart of the punctured SU(2)
    `u`-plane that carry the same SW monodromy coincide **up to an `SL(2,ℤ) = Sp(2,ℤ)`
    frame change** `m`. This is the rank-1 case of
    `sw_effective_theory_unique_up_to_duality`, here *derived* (not assumed) from the
    uniformization input + the analytic identity theorem.

    Kernel footprint: **classical-math axioms only** — the `Γ(2)` covering plus
    lift-uniqueness, via `su2_frame_alignment`. The physics is the *defined* hypothesis
    `SameSWMonodromy` (both maps develop the pinned `swCrossRatio`), visible in the type;
    the propagation is the proved `holo_eqOn_of_germ`. No physics axiom, no bespoke
    placeholder. -/
theorem sw_su2_unique
    {Λ : ℂ} {D : Set ℂ} (hDo : IsOpen D) (hD : IsPreconnected D)
    {u₀ : ℂ} (hu₀ : u₀ ∈ D) {f g : ℂ → ℂ}
    (hmono : SameSWMonodromy Λ D f g) :
    ∃ γ ∈ Gamma2, Set.EqOn f (fun u => moebiusOn γ (g u)) D := by
  obtain ⟨γ, hγ, hfg⟩ := su2_frame_alignment (D := D) (u₀ := u₀) hDo hu₀ hmono
  exact ⟨γ, hγ, holo_eqOn_of_germ hD hu₀ hmono.1.1
    (analyticOnNhd_moebius_comp hmono.2.1 hmono.2.2.1) hfg⟩


/-! ## The C-route closure at the coupling level: the explicit SU(2) SW coupling

`AX_elliptic_inversion` (C1) supplies the coupling itself: `swTau = i·K(1−m)/K(m)` at
`m = swCrossRatio Λ u` is holomorphic, ℍ-valued, and develops the modulus — a genuine
`IsSWDevelopingMap`. With `sw_su2_unique`, the SU(2) effective coupling therefore
**exists and is unique up to a `Γ(2)` duality frame**, on classical axioms only
(standard-3 + C1 + the covering pair) — no bespoke axiom, no physics axiom. -/

/-- **The explicit SU(2) SW coupling**: `τ(u) = i·K(1−m)/K(m)` at the pinned modulus
`m = swCrossRatio Λ u`. -/
noncomputable def swTau (Λ : ℂ) (u : ℂ) : ℂ :=
  Complex.I * ellipticKm (1 - swCrossRatio Λ u) / ellipticKm (swCrossRatio Λ u)

/-- Moduli in the coupling chart avoid the dyon point (where `swCrossRatio` is junk `0`,
which the cut plane excludes). -/
theorem ne_dyon_of_mem_tauDomain {Λ u : ℂ}
    (hu : u ∈ swCrossRatio Λ ⁻¹' EllipticParamDomain) : u ≠ -Λ ^ 2 := by
  rintro rfl
  have h0 : swCrossRatio Λ (-Λ ^ 2) = 0 := by
    simp [swCrossRatio]
  rw [Set.mem_preimage, h0] at hu
  simp [EllipticParamDomain] at hu

/-- The modulus map is analytic away from the dyon point. -/
theorem analyticAt_swCrossRatio {Λ u : ℂ} (hu : u ≠ -Λ ^ 2) :
    AnalyticAt ℂ (swCrossRatio Λ) u := by
  have hden : u + Λ ^ 2 ≠ 0 := fun h => hu (eq_neg_of_add_eq_zero_left h)
  exact analyticAt_const.div (analyticAt_id.add analyticAt_const) hden

/-- **The coupling chart** `{u | swCrossRatio Λ u ∈ the cut plane}` is open. -/
theorem isOpen_tauDomain (Λ : ℂ) :
    IsOpen (swCrossRatio Λ ⁻¹' EllipticParamDomain) := by
  have h : swCrossRatio Λ ⁻¹' EllipticParamDomain
      = ({-Λ ^ 2}ᶜ : Set ℂ) ∩ swCrossRatio Λ ⁻¹' EllipticParamDomain := by
    ext u
    exact ⟨fun hu => ⟨ne_dyon_of_mem_tauDomain hu, hu⟩, fun h => h.2⟩
  rw [h]
  refine ContinuousOn.isOpen_inter_preimage ?_ isOpen_compl_singleton
    isOpen_ellipticParamDomain
  exact fun u hu => (analyticAt_swCrossRatio (Set.mem_compl_singleton_iff.mp hu))
    |>.continuousAt.continuousWithinAt

/-- **`swTau` is a developing map** on any subchart of the coupling chart: holomorphic
(C1h + `swCrossRatio` analyticity), ℍ-valued and modulus-developing (both read off C1's
witness, whose formula `swTau` is). -/
theorem isSWDevelopingMap_swTau {Λ : ℂ} {D : Set ℂ}
    (hsub : D ⊆ swCrossRatio Λ ⁻¹' EllipticParamDomain) :
    IsSWDevelopingMap Λ D (swTau Λ) := by
  have key : ∀ u ∈ D, swTau Λ u ∈ {z : ℂ | 0 < z.im} ∧
      modularLambdaFn (swTau Λ u) = swCrossRatio Λ u := by
    intro u hu
    obtain ⟨-, τ, hlam, -, htau⟩ := AX_elliptic_inversion _ (hsub hu)
    have hval : swTau Λ u = (τ : ℂ) := htau.symm
    exact ⟨by rw [Set.mem_setOf_eq, hval]; exact τ.2, by rw [hval, hlam]⟩
  refine ⟨?_, fun u hu => (key u hu).1, fun u hu => (key u hu).2⟩
  intro u hu
  have hm := hsub hu
  have hratio : AnalyticAt ℂ (fun m => Complex.I * ellipticKm (1 - m) / ellipticKm m)
      (swCrossRatio Λ u) :=
    (tau_ratio_differentiableOn.analyticOnNhd isOpen_ellipticParamDomain) _ hm
  exact hratio.comp (analyticAt_swCrossRatio (ne_dyon_of_mem_tauDomain hm))

/-- The self-dual point `u = 3Λ²` (modulus `1/2`, coupling `τ = i`) witnesses that the
coupling chart is nonempty for every `Λ ≠ 0`. -/
theorem selfDual_mem_tauDomain {Λ : ℂ} (hΛ : Λ ≠ 0) :
    3 * Λ ^ 2 ∈ swCrossRatio Λ ⁻¹' EllipticParamDomain := by
  have h : swCrossRatio Λ (3 * Λ ^ 2) = 1 / 2 := by
    simp only [swCrossRatio]
    rw [show 3 * Λ ^ 2 + Λ ^ 2 = 4 * Λ ^ 2 from by ring,
      div_eq_div_iff (by exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hΛ))
        (by norm_num : (2:ℂ) ≠ 0)]
    ring
  rw [Set.mem_preimage, h]
  exact half_mem_ellipticParamDomain

/-- **SU(2) coupling existence (C-route closure, proved).** For `Λ ≠ 0` the explicit
elliptic coupling `swTau` is a developing map of the SW modulus on the open, nonempty
coupling chart. Footprint: standard-3 + `AX_elliptic_inversion` — one classical axiom. -/
theorem su2_coupling_exists {Λ : ℂ} (hΛ : Λ ≠ 0) :
    IsSWDevelopingMap Λ (swCrossRatio Λ ⁻¹' EllipticParamDomain) (swTau Λ) ∧
      IsOpen (swCrossRatio Λ ⁻¹' EllipticParamDomain) ∧
      3 * Λ ^ 2 ∈ swCrossRatio Λ ⁻¹' EllipticParamDomain :=
  ⟨isSWDevelopingMap_swTau (subset_refl _), isOpen_tauDomain Λ, selfDual_mem_tauDomain hΛ⟩

/-- **SU(2) coupling uniqueness, canonical form (C-route closure, proved).** Every
developing map on a connected open subchart agrees with the explicit `swTau` up to a
`Γ(2)` duality frame. Footprint: standard-3 + `AX_elliptic_inversion` + the covering
pair — classical axioms only; the physics is the developing-map hypothesis in the type. -/
theorem su2_coupling_canonical {Λ : ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hD : IsPreconnected D) {u₀ : ℂ} (hu₀ : u₀ ∈ D)
    (hsub : D ⊆ swCrossRatio Λ ⁻¹' EllipticParamDomain)
    {f : ℂ → ℂ} (hf : IsSWDevelopingMap Λ D f) :
    ∃ γ ∈ Gamma2, Set.EqOn f (fun u => moebiusOn γ (swTau Λ u)) D :=
  sw_su2_unique hDo hD hu₀ ⟨hf, isSWDevelopingMap_swTau hsub⟩


/-! ## The special-coordinate layer, milestone S0: pinned `a, a_D` and H2 at the monopole

Closed forms pinned numerically against `∮ λ_SW = ∮ x²dx/y` quadrature
(`audit/numerical/validate_specialcoords.py`): `√(u+Λ²)·E(m) = ±(i/2)·∮_A x²dx/y` and
`√(u+Λ²)·(K(1−m)−E(1−m)) = ½·∮_B x²dx/y` — the bracket `K−E` is the unique match among
candidates — with `da_D/da = swTau` verified to `1e−19` and the `√2/π` prefactor fixed by
the weak-coupling normalization `a ≈ √(u/2)`. -/

/-- **The SU(2) special coordinate** `a(u) = (√2/π)·√(u+Λ²)·E(m)` at the pinned modulus. -/
noncomputable def swA (Λ : ℂ) (u : ℂ) : ℂ :=
  ((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ)
    * ellipticEm (swCrossRatio Λ u)

/-- **The dual special coordinate** `a_D(u) = i(√2/π)·√(u+Λ²)·(K(1−m) − E(1−m))`. -/
noncomputable def swAD (Λ : ℂ) (u : ℂ) : ℂ :=
  ((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * Complex.I * (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ)
    * (ellipticKm (1 - swCrossRatio Λ u) - ellipticEm (1 - swCrossRatio Λ u))

/-- A square root is norm-dominated: `‖x^{1/2}‖ ≤ max 1 ‖x‖` (junk case `x = 0` included) —
the boundedness that lets vanishing brackets kill the prefactor without branch analysis. -/
theorem norm_cpow_half_le (x : ℂ) : ‖x ^ (((1:ℝ)/2 : ℝ) : ℂ)‖ ≤ max 1 ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Complex.zero_cpow (by norm_num : ((((1:ℝ)/2 : ℝ) : ℂ)) ≠ 0)]
    simp
  · rw [Complex.norm_cpow_of_ne_zero hx]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, Real.exp_zero, div_one]
    rcases le_total ‖x‖ 1 with h | h
    · exact le_max_of_le_left (Real.rpow_le_one (norm_nonneg x) h (by norm_num))
    · refine le_max_of_le_right ?_
      calc ‖x‖ ^ ((1:ℝ)/2) ≤ ‖x‖ ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h (by norm_num)
        _ = ‖x‖ := Real.rpow_one _

/-- **H2 at the monopole (proved).** The dual special coordinate vanishes as `u → Λ²`
within the coupling chart — the monopole's central charge goes massless. Exactly the
`PeriodVanishesAt` shape of H2, derived from C3's cusp limits: the bracket
`K(1−m) − E(1−m) → π/2 − π/2 = 0`, and the `√(u+Λ²)` prefactor is norm-bounded. -/
theorem swAD_tendsto_zero_monopole {Λ : ℂ} (hΛ : Λ ≠ 0) :
    Tendsto (swAD Λ) (𝓝[swCrossRatio Λ ⁻¹' EllipticParamDomain] (Λ ^ 2)) (𝓝 0) := by
  set S := swCrossRatio Λ ⁻¹' EllipticParamDomain with hS
  have hne : (Λ ^ 2 : ℂ) ≠ -Λ ^ 2 := by
    intro h
    have h2 : (2 : ℂ) * Λ ^ 2 = 0 := by linear_combination h
    exact pow_ne_zero 2 hΛ ((mul_eq_zero.mp h2).resolve_left (by norm_num))
  -- the complementary modulus tends to 0 within the cut plane
  have hmc : Tendsto (swCrossRatio Λ) (𝓝[S] (Λ ^ 2)) (𝓝 1) := by
    have hc := (analyticAt_swCrossRatio (Λ := Λ) hne).continuousAt.continuousWithinAt
      (s := S)
    rwa [ContinuousWithinAt, swCrossRatio_monopole hΛ] at hc
  have hs : Tendsto (fun u => 1 - swCrossRatio Λ u) (𝓝[S] (Λ ^ 2))
      (𝓝[EllipticParamDomain] 0) := by
    rw [tendsto_nhdsWithin_iff]
    have h0 : Tendsto (fun u => (1:ℂ) - swCrossRatio Λ u) (𝓝[S] (Λ ^ 2)) (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub hmc
    refine ⟨by simpa using h0, ?_⟩
    exact eventually_nhdsWithin_of_forall fun u hu => one_sub_mem_ellipticParamDomain hu
  -- the bracket vanishes — now from PROVED cusp limits (no axiom)
  have hs' : Tendsto (fun u => 1 - swCrossRatio Λ u) (𝓝[S] (Λ ^ 2)) (𝓝 0) :=
    hs.mono_right nhdsWithin_le_nhds
  have hdiff : Tendsto (fun u => ellipticKm (1 - swCrossRatio Λ u)
      - ellipticEm (1 - swCrossRatio Λ u)) (𝓝[S] (Λ ^ 2)) (𝓝 0) := by
    have h := (ellipticKm_tendsto_zero.comp hs').sub (ellipticEm_tendsto_zero.comp hs')
    simpa using h
  -- the prefactor is norm-bounded near the monopole
  have hbase : Tendsto (fun u : ℂ => ‖u + Λ ^ 2‖) (𝓝[S] (Λ ^ 2)) (𝓝 ‖2 * Λ ^ 2‖) := by
    have h1 : Tendsto (fun u : ℂ => u + Λ ^ 2) (𝓝 (Λ ^ 2)) (𝓝 (Λ ^ 2 + Λ ^ 2)) :=
      (continuous_id.add continuous_const).tendsto _
    have h1' : Tendsto (fun u : ℂ => u + Λ ^ 2) (𝓝[S] (Λ ^ 2)) (𝓝 (Λ ^ 2 + Λ ^ 2)) :=
      h1.mono_left (nhdsWithin_le_nhds : 𝓝[S] (Λ ^ 2) ≤ 𝓝 (Λ ^ 2))
    have h2 := h1'.norm
    rwa [show (Λ ^ 2 + Λ ^ 2 : ℂ) = 2 * Λ ^ 2 from by ring] at h2
  have hev : ∀ᶠ u in 𝓝[S] (Λ ^ 2), ‖u + Λ ^ 2‖ < ‖2 * Λ ^ 2‖ + 1 :=
    hbase.eventually_lt_const (lt_add_one _)
  have hpre : Filter.IsBoundedUnder (· ≤ ·) (𝓝[S] (Λ ^ 2)) (norm ∘ fun u : ℂ =>
      ((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * Complex.I * (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ)) := by
    refine ⟨(Real.sqrt 2 / Real.pi) * max 1 (‖2 * Λ ^ 2‖ + 1), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hev] with u hu
    have hb : ‖(u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ)‖ ≤ max 1 (‖2 * Λ ^ 2‖ + 1) :=
      (norm_cpow_half_le _).trans (max_le_max le_rfl hu.le)
    calc ‖((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * Complex.I
          * (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ)‖
        = (Real.sqrt 2 / Real.pi) * ‖(u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_of_nonneg (by positivity)]
      _ ≤ (Real.sqrt 2 / Real.pi) * max 1 (‖2 * Λ ^ 2‖ + 1) := by
          have h2π : (0:ℝ) ≤ Real.sqrt 2 / Real.pi := by positivity
          exact mul_le_mul_of_nonneg_left hb h2π
  -- assemble: swAD = bracket * prefactor
  have hfun : swAD Λ = fun u =>
      (ellipticKm (1 - swCrossRatio Λ u) - ellipticEm (1 - swCrossRatio Λ u))
      * (((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * Complex.I
          * (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ)) := by
    funext u
    simp only [swAD]
    ring
  rw [hfun]
  exact hdiff.zero_mul_isBoundedUnder_le hpre


/-! ## S1: derivatives of the special coordinates (from the proved Legendre ODEs) -/

/-- **The classical `da/du` (proved):** on the coupling chart, away from the prefactor
cut (`u + Λ² ∈` slit plane), `da/du = (√2/2π)·K(m)/√(u+Λ²)` — the chain rule through
the pinned modulus and the *proved* `E` Legendre ODE; the `Δ`-algebra collapses
`P′E + P·E′·m′` to the classical form. First half of S1 (`da_D/da = swTau`). -/
theorem swA_hasDerivAt {Λ u : ℂ} (hm : swCrossRatio Λ u ∈ EllipticParamDomain)
    (hslit : u + Λ ^ 2 ∈ Complex.slitPlane) :
    HasDerivAt (swA Λ)
      (((Real.sqrt 2 / Real.pi : ℝ) : ℂ) / 2
        * (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - 1)
        * ellipticKm (swCrossRatio Λ u)) u := by
  have hne : u + Λ ^ 2 ≠ 0 := slitPlane_ne_zero' hslit
  have hm0 : swCrossRatio Λ u ≠ 0 := ne_zero_of_mem_ellipticParamDomain hm
  have hΛ2 : (2:ℂ) * Λ ^ 2 ≠ 0 := by
    intro h
    apply hm0
    show 2 * Λ ^ 2 / (u + Λ ^ 2) = 0
    rw [h, zero_div]
  have hden : HasDerivAt (fun u : ℂ => u + Λ ^ 2) 1 u := by
    simpa using (hasDerivAt_id u).add_const (Λ ^ 2)
  have hmder : HasDerivAt (swCrossRatio Λ) (-(2 * Λ ^ 2) / (u + Λ ^ 2) ^ 2) u := by
    have h := (hasDerivAt_const u (2 * Λ ^ 2)).div hden hne
    have hfun : swCrossRatio Λ = fun u : ℂ => 2 * Λ ^ 2 / (u + Λ ^ 2) := rfl
    rw [hfun]
    convert h using 1
    ring
  have hP : HasDerivAt (fun u : ℂ => (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ)))
      (((((1:ℝ)/2 : ℝ) : ℂ)) * (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - 1) * 1) u :=
    HasDerivAt.cpow_const (f := fun u : ℂ => u + Λ ^ 2) hden hslit
  have hEc : HasDerivAt (fun u : ℂ => ellipticEm (swCrossRatio Λ u))
      ((ellipticEm (swCrossRatio Λ u) - ellipticKm (swCrossRatio Λ u))
        / (2 * swCrossRatio Λ u) * (-(2 * Λ ^ 2) / (u + Λ ^ 2) ^ 2)) u := by
    have h := HasDerivAt.comp u (ellipticEm_hasDerivAt hm) hmder
    simpa [Function.comp_def] using h
  have hraw := (hP.const_mul (((Real.sqrt 2 / Real.pi : ℝ) : ℂ))).mul hEc
  convert hraw using 1
  have hmval : swCrossRatio Λ u = 2 * Λ ^ 2 / (u + Λ ^ 2) := rfl
  have hcpow : (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ))
      = (u + Λ ^ 2) * (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - 1) := by
    conv_lhs => rw [show ((((1:ℝ)/2 : ℝ) : ℂ)) = 1 + (((((1:ℝ)/2 : ℝ) : ℂ)) - 1) from by ring]
    rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
  have hΛ0 : Λ ≠ 0 := by
    intro h
    apply hΛ2
    rw [h]
    ring
  rw [hcpow, hmval, show (((1:ℝ)/2 : ℝ) : ℂ) = (1/2 : ℂ) from by norm_num]
  field_simp [hΛ0]
  ring

/-- **The classical `da_D/du` (proved):** on the same chart,
`da_D/du = i(√2/2π)·K(1−m)/√(u+Λ²)` — both proved Legendre ODEs at the complementary
argument `1−m`; the collapse `(K′−E′)(1−m) = E(1−m)/(2m)` composed with `m′ = −m/X`
turns the bracket's derivative into `E(1−m)/(2X)`, and the product rule reassembles
`K(1−m)`. Second half of S1. -/
theorem swAD_hasDerivAt {Λ u : ℂ} (hm : swCrossRatio Λ u ∈ EllipticParamDomain)
    (hslit : u + Λ ^ 2 ∈ Complex.slitPlane) :
    HasDerivAt (swAD Λ)
      (((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * Complex.I / 2
        * (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - 1)
        * ellipticKm (1 - swCrossRatio Λ u)) u := by
  have hne : u + Λ ^ 2 ≠ 0 := slitPlane_ne_zero' hslit
  have hm0 : swCrossRatio Λ u ≠ 0 := ne_zero_of_mem_ellipticParamDomain hm
  have hm1 : (1 : ℂ) - swCrossRatio Λ u ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (ne_one_of_mem_ellipticParamDomain hm))
  have hs : (1 - swCrossRatio Λ u) ∈ EllipticParamDomain :=
    one_sub_mem_ellipticParamDomain hm
  have hden : HasDerivAt (fun u : ℂ => u + Λ ^ 2) 1 u := by
    simpa using (hasDerivAt_id u).add_const (Λ ^ 2)
  have hmder : HasDerivAt (swCrossRatio Λ) (-(2 * Λ ^ 2) / (u + Λ ^ 2) ^ 2) u := by
    have h := (hasDerivAt_const u (2 * Λ ^ 2)).div hden hne
    have hfun : swCrossRatio Λ = fun u : ℂ => 2 * Λ ^ 2 / (u + Λ ^ 2) := rfl
    rw [hfun]
    convert h using 1
    ring
  have hone : HasDerivAt (fun u : ℂ => 1 - swCrossRatio Λ u)
      (2 * Λ ^ 2 / (u + Λ ^ 2) ^ 2) u := by
    have h := hmder.const_sub 1
    convert h using 1
    ring
  have hP : HasDerivAt (fun u : ℂ => (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ)))
      (((((1:ℝ)/2 : ℝ) : ℂ)) * (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - 1) * 1) u :=
    HasDerivAt.cpow_const (f := fun u : ℂ => u + Λ ^ 2) hden hslit
  have hKc : HasDerivAt (fun u : ℂ => ellipticKm (1 - swCrossRatio Λ u))
      ((ellipticEm (1 - swCrossRatio Λ u)
          - swCrossRatio Λ u * ellipticKm (1 - swCrossRatio Λ u))
        / (2 * (1 - swCrossRatio Λ u) * swCrossRatio Λ u)
        * (2 * Λ ^ 2 / (u + Λ ^ 2) ^ 2)) u := by
    have h := HasDerivAt.comp u (ellipticKm_hasDerivAt hs) hone
    simpa only [Function.comp_def, sub_sub_cancel] using h
  have hEc1 : HasDerivAt (fun u : ℂ => ellipticEm (1 - swCrossRatio Λ u))
      ((ellipticEm (1 - swCrossRatio Λ u) - ellipticKm (1 - swCrossRatio Λ u))
        / (2 * (1 - swCrossRatio Λ u))
        * (2 * Λ ^ 2 / (u + Λ ^ 2) ^ 2)) u := by
    have h := HasDerivAt.comp u (ellipticEm_hasDerivAt hs) hone
    simpa only [Function.comp_def] using h
  have hbr := hKc.sub hEc1
  have hraw :=
    (hP.const_mul (((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * Complex.I)).mul hbr
  convert hraw using 1
  have hmX : 2 * Λ ^ 2 = swCrossRatio Λ u * (u + Λ ^ 2) := by
    show 2 * Λ ^ 2 = 2 * Λ ^ 2 / (u + Λ ^ 2) * (u + Λ ^ 2)
    rw [div_mul_cancel₀ _ hne]
  have hcpow : (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ))
      = (u + Λ ^ 2) * (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - 1) := by
    conv_lhs => rw [show ((((1:ℝ)/2 : ℝ) : ℂ)) = 1 + (((((1:ℝ)/2 : ℝ) : ℂ)) - 1) from by ring]
    rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
  rw [hcpow, hmX, show (((1:ℝ)/2 : ℝ) : ℂ) = (1/2 : ℂ) from by norm_num]
  simp only [Pi.sub_apply]
  field_simp [hm0, hm1, hne]
  ring

/-- **S1 complete — special geometry on the chart, `da_D/da = τ`:** the derivative of
`a_D` is `swTau` times the derivative of `a`, at every point of the coupling chart away
from the prefactor cut. This is the chain-rule form of `da_D/da = τ` — the defining
relation of special geometry (H1) for the explicit SU(2) solution — with both sides
*proved* closed forms; only `K(m) ≠ 0` (C1's nonvanishing clause) is consumed.
Footprint: standard-3 + `AX_elliptic_inversion`. -/
theorem swAD_deriv_eq_swTau_mul_swA_deriv {Λ u : ℂ}
    (hm : swCrossRatio Λ u ∈ EllipticParamDomain)
    (hslit : u + Λ ^ 2 ∈ Complex.slitPlane) :
    HasDerivAt (swAD Λ)
      (swTau Λ u
        * (((Real.sqrt 2 / Real.pi : ℝ) : ℂ) / 2
          * (u + Λ ^ 2) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - 1)
          * ellipticKm (swCrossRatio Λ u))) u := by
  have hK0 : ellipticKm (swCrossRatio Λ u) ≠ 0 := (AX_elliptic_inversion _ hm).1
  have h := swAD_hasDerivAt hm hslit
  convert h using 1
  simp only [swTau]
  field_simp

/-- **H6 weak coupling for the explicit solution (proved):** on the coupling chart,
`a(u)/(u+Λ²)^{1/2} → √2/2` as `|u| → ∞` — the weak-coupling normalization `a ≈ √(u/2)`
that fixed the `√2/π` prefactor numerically, now a theorem: the pinned modulus
`m(u) = 2Λ²/(u+Λ²) → 0` at large `|u|` and `E(m) → π/2` (proved, loop iteration 1),
so `a/X^{1/2} = (√2/π)·E(m) → (√2/π)(π/2) = √2/2`. Axiom-free. -/
theorem swA_weakCoupling (Λ : ℂ) :
    Tendsto (fun u : ℂ => swA Λ u / (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ))
      (Bornology.cobounded ℂ ⊓ Filter.principal (swCrossRatio Λ ⁻¹' EllipticParamDomain))
      (𝓝 ((Real.sqrt 2 / 2 : ℝ) : ℂ)) := by
  have hX : Tendsto (fun u : ℂ => ‖u + Λ ^ 2‖) (Bornology.cobounded ℂ) atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-‖Λ ^ 2‖)
      tendsto_norm_cobounded_atTop)
    refine Filter.Eventually.of_forall fun u => ?_
    have h := norm_add_le (u + Λ ^ 2) (-(Λ ^ 2))
    rw [add_neg_cancel_right, norm_neg] at h
    linarith
  have hm0 : Tendsto (swCrossRatio Λ) (Bornology.cobounded ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hfun : (fun u : ℂ => ‖swCrossRatio Λ u‖)
        = fun u : ℂ => ‖2 * Λ ^ 2‖ / ‖u + Λ ^ 2‖ := by
      funext u
      show ‖2 * Λ ^ 2 / (u + Λ ^ 2)‖ = _
      exact norm_div _ _
    rw [hfun]
    exact tendsto_const_nhds.div_atTop hX
  have hE : Tendsto (fun u : ℂ => ((Real.sqrt 2 / Real.pi : ℝ) : ℂ)
        * ellipticEm (swCrossRatio Λ u))
      (Bornology.cobounded ℂ ⊓ Filter.principal (swCrossRatio Λ ⁻¹' EllipticParamDomain))
      (𝓝 (((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * ((Real.pi / 2 : ℝ) : ℂ))) :=
    (ellipticEm_tendsto_zero.comp (hm0.mono_left inf_le_left)).const_mul _
  have heq : (fun u : ℂ => ((Real.sqrt 2 / Real.pi : ℝ) : ℂ)
        * ellipticEm (swCrossRatio Λ u))
      =ᶠ[Bornology.cobounded ℂ ⊓ Filter.principal (swCrossRatio Λ ⁻¹' EllipticParamDomain)]
      fun u : ℂ => swA Λ u / (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ) := by
    refine Filter.eventuallyEq_of_mem
      (Filter.mem_inf_of_right (Filter.mem_principal_self _)) fun u hu => ?_
    have hmem : swCrossRatio Λ u ∈ EllipticParamDomain := hu
    have hXne : u + Λ ^ 2 ≠ 0 := by
      intro h0
      apply zero_notMem_ellipticParamDomain
      have hz : swCrossRatio Λ u = 0 := by
        show 2 * Λ ^ 2 / (u + Λ ^ 2) = 0
        rw [h0, div_zero]
      rwa [hz] at hmem
    have hXe : (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ) ≠ 0 := by
      simp [Complex.cpow_eq_zero_iff, hXne]
    show ((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * ellipticEm (swCrossRatio Λ u)
        = swA Λ u / (u + Λ ^ 2) ^ (((1:ℝ)/2 : ℝ) : ℂ)
    rw [eq_div_iff hXe]
    simp only [swA]
    ring
  have hlim := hE.congr' heq
  have hval : ((Real.sqrt 2 / Real.pi : ℝ) : ℂ) * ((Real.pi / 2 : ℝ) : ℂ)
      = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  rwa [hval] at hlim


/-- **The coupling's derivative in closed form (proved):** on the chart,
`dτ/du = iπ / (4·(u+Λ²)·(1−m)·K(m)²)` — the Wronskian formula `tau_ratio_hasDerivAt`
(the Legendre relation's payoff) composed with the pinned modulus, the `m²` from
`m′ = −m²/(2Λ²)` cancelling one `m` against the Wronskian's `1/m`. Footprint:
standard-3 + `AX_elliptic_inversion` (only its `K ≠ 0` clause). -/
theorem swTau_hasDerivAt {Λ u : ℂ} (hm : swCrossRatio Λ u ∈ EllipticParamDomain) :
    HasDerivAt (swTau Λ)
      (Complex.I * (Real.pi : ℂ)
        / (4 * (u + Λ ^ 2) * (1 - swCrossRatio Λ u)
          * ellipticKm (swCrossRatio Λ u) ^ 2)) u := by
  have hm0 : swCrossRatio Λ u ≠ 0 := ne_zero_of_mem_ellipticParamDomain hm
  have hne : u + Λ ^ 2 ≠ 0 := by
    intro h0
    apply hm0
    show 2 * Λ ^ 2 / (u + Λ ^ 2) = 0
    rw [h0, div_zero]
  have hm1 : (1 : ℂ) - swCrossRatio Λ u ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (ne_one_of_mem_ellipticParamDomain hm))
  have hK0 : ellipticKm (swCrossRatio Λ u) ≠ 0 := (AX_elliptic_inversion _ hm).1
  have hden : HasDerivAt (fun u : ℂ => u + Λ ^ 2) 1 u := by
    simpa using (hasDerivAt_id u).add_const (Λ ^ 2)
  have hmder : HasDerivAt (swCrossRatio Λ) (-(2 * Λ ^ 2) / (u + Λ ^ 2) ^ 2) u := by
    have h := (hasDerivAt_const u (2 * Λ ^ 2)).div hden hne
    have hfun : swCrossRatio Λ = fun u : ℂ => 2 * Λ ^ 2 / (u + Λ ^ 2) := rfl
    rw [hfun]
    convert h using 1
    ring
  have h := HasDerivAt.comp u (tau_ratio_hasDerivAt hm) hmder
  convert h using 1
  have hmX : 2 * Λ ^ 2 = swCrossRatio Λ u * (u + Λ ^ 2) := by
    show 2 * Λ ^ 2 = 2 * Λ ^ 2 / (u + Λ ^ 2) * (u + Λ ^ 2)
    rw [div_mul_cancel₀ _ hne]
  rw [hmX]
  field_simp

/-- **The faithful weak-coupling (one-loop) asymptotic (proved):** for the *actual*
SU(2) coupling, `u·(dτ/du) → i/π` at large `|u|` on the chart — the log-running of
the period ratio, with the constant belonging to the λ-convention normalization of
`swTau = i·K′/K` (`τ ≈ (i/π)·log u`; the physics normalization differs by the
documented Γ(2) factor). This is the curve-tied statement the deleted existential
axiom (`DIFFICULT_POINTS.md` D3) only gestured at: here `τ` *is* the pinned-modulus
coupling. Footprint: standard-3 + `AX_elliptic_inversion`. -/
theorem swTau_logDeriv_weakCoupling (Λ : ℂ) :
    Tendsto (fun u : ℂ => u * deriv (swTau Λ) u)
      (Bornology.cobounded ℂ ⊓ Filter.principal (swCrossRatio Λ ⁻¹' EllipticParamDomain))
      (𝓝 (Complex.I / (Real.pi : ℂ))) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- the modulus tends to 0 at large |u| (as in `swA_weakCoupling`)
  have hX : Tendsto (fun u : ℂ => ‖u + Λ ^ 2‖) (Bornology.cobounded ℂ) atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-‖Λ ^ 2‖)
      tendsto_norm_cobounded_atTop)
    refine Filter.Eventually.of_forall fun u => ?_
    have h := norm_add_le (u + Λ ^ 2) (-(Λ ^ 2))
    rw [add_neg_cancel_right, norm_neg] at h
    linarith
  have hm0 : Tendsto (swCrossRatio Λ) (Bornology.cobounded ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hfun : (fun u : ℂ => ‖swCrossRatio Λ u‖)
        = fun u : ℂ => ‖2 * Λ ^ 2‖ / ‖u + Λ ^ 2‖ := by
      funext u
      show ‖2 * Λ ^ 2 / (u + Λ ^ 2)‖ = _
      exact norm_div _ _
    rw [hfun]
    exact tendsto_const_nhds.div_atTop hX
  set L := Bornology.cobounded ℂ ⊓
    Filter.principal (swCrossRatio Λ ⁻¹' EllipticParamDomain) with hL
  have hmL : Tendsto (swCrossRatio Λ) L (𝓝 0) := hm0.mono_left inf_le_left
  -- the three factors
  have hKf : Tendsto (fun u : ℂ => ellipticKm (swCrossRatio Λ u) ^ 2) L
      (𝓝 (((Real.pi / 2 : ℝ) : ℂ) ^ 2)) :=
    ((ellipticKm_tendsto_zero.comp hmL).pow 2)
  have h1m : Tendsto (fun u : ℂ => (1 : ℂ) - swCrossRatio Λ u) L (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1:ℂ)) (f := L)).sub hmL
    simpa using h
  have hur : Tendsto (fun u : ℂ => u / (u + Λ ^ 2)) L (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1:ℂ)) (f := L)).sub (hmL.div_const 2)
    have hval : (1 : ℂ) - 0 / 2 = 1 := by norm_num
    rw [hval] at h
    refine Filter.Tendsto.congr' ?_ h
    refine Filter.eventuallyEq_of_mem
      (Filter.mem_inf_of_right (Filter.mem_principal_self _)) fun u hu => ?_
    have hm0u : swCrossRatio Λ u ≠ 0 := ne_zero_of_mem_ellipticParamDomain hu
    have hne : u + Λ ^ 2 ≠ 0 := by
      intro h0
      apply hm0u
      show 2 * Λ ^ 2 / (u + Λ ^ 2) = 0
      rw [h0, div_zero]
    show (1 : ℂ) - swCrossRatio Λ u / 2 = u / (u + Λ ^ 2)
    show (1 : ℂ) - 2 * Λ ^ 2 / (u + Λ ^ 2) / 2 = u / (u + Λ ^ 2)
    field_simp
    ring
  -- assemble the product of limits
  have hKne : ((1 : ℂ) * ((Real.pi / 2 : ℝ) : ℂ) ^ 2) ≠ 0 := by
    have : ((Real.pi / 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (Real.pi / 2 : ℝ) ≠ 0)
    simpa using pow_ne_zero 2 this
  have hprod : Tendsto (fun u : ℂ => Complex.I * (Real.pi : ℂ) / 4
        * (u / (u + Λ ^ 2))
        * (((1 - swCrossRatio Λ u) * ellipticKm (swCrossRatio Λ u) ^ 2))⁻¹) L
      (𝓝 (Complex.I * (Real.pi : ℂ) / 4 * 1
        * ((1 * ((Real.pi / 2 : ℝ) : ℂ) ^ 2))⁻¹)) :=
    ((tendsto_const_nhds.mul hur)).mul ((h1m.mul hKf).inv₀ hKne)
  have hval : Complex.I * (Real.pi : ℂ) / 4 * 1
      * ((1 * ((Real.pi / 2 : ℝ) : ℂ) ^ 2))⁻¹ = Complex.I / (Real.pi : ℂ) := by
    push_cast
    field_simp
    ring
  rw [hval] at hprod
  refine Filter.Tendsto.congr' ?_ hprod
  refine Filter.eventuallyEq_of_mem
    (Filter.mem_inf_of_right (Filter.mem_principal_self _)) fun u hu => ?_
  have hm0u : swCrossRatio Λ u ≠ 0 := ne_zero_of_mem_ellipticParamDomain hu
  have hne : u + Λ ^ 2 ≠ 0 := by
    intro h0
    apply hm0u
    show 2 * Λ ^ 2 / (u + Λ ^ 2) = 0
    rw [h0, div_zero]
  have hm1u : (1 : ℂ) - swCrossRatio Λ u ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (ne_one_of_mem_ellipticParamDomain hu))
  have hK0u : ellipticKm (swCrossRatio Λ u) ≠ 0 := (AX_elliptic_inversion _ hu).1
  show Complex.I * (Real.pi : ℂ) / 4 * (u / (u + Λ ^ 2))
      * (((1 - swCrossRatio Λ u) * ellipticKm (swCrossRatio Λ u) ^ 2))⁻¹
    = u * deriv (swTau Λ) u
  rw [(swTau_hasDerivAt hu).deriv]
  field_simp

end SeibergWitten.Physics.SU2
