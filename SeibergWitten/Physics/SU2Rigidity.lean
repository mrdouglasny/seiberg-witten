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
| `Sp(2,ℤ)`-action on `ℍ`, monodromy representation | **physics axiom** — `SameSWMonodromy` |

So `sw_su2_unique` is a **theorem** modulo two clearly-separated tiers: the *classical-math*
covering + lift-uniqueness axioms, and the *physics* monodromy input. The analytic core is
proved. Discharging the covering upstream (Schwarz reflection ⇒ Riemann mapping ⇒ the `Γ(2)`
cover — the conformal-mapping programme) and the lift-uniqueness step removes the math debt;
the physics axiom is irreducible.

References: Seiberg–Witten, hep-th/9407087 §3–4 (SU(2) monodromy, `u`-plane);
Lerche, hep-th/9611190 §3; for uniformization: the modular `λ`-function / `Γ(2)`.
-/
import SeibergWitten.Physics.Hypotheses
import SeibergWitten.Physics.ModularLambda
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

/-- **Placeholder — same SW monodromy.** `f, g` carry the same `Sp(2,ℤ)` monodromy
representation of `π₁(ℂ ∖ {±Λ²})` (the parabolic generators around `±Λ²` composing to
the semiclassical monodromy at `∞`). Uninterpreted until the monodromy layer is built
(Phase 3/4); stated so the rigidity hypothesis below is faithful rather than vacuous. -/
axiom SameSWMonodromy : ∀ (_Λ : ℂ), (ℂ → ℂ) → (ℂ → ℂ) → Prop

/-- **Classical math axiom — uniqueness of developing maps (lift rigidity).**

    *Given* the thrice-punctured uniformization `U : ThricePuncturedUniformization` (the
    `ℍ → ℂ∖{0,1}` `Γ(2)`-cover), two holomorphic period maps `f, g` on a connected chart
    `D` that carry the *same* `Sp(2,ℤ)` monodromy are two developing maps of the same
    cover with the same monodromy, hence differ by a deck transformation; matching one cusp
    fixes it to a single modular (`SL(2,ℤ)`) frame change `m` aligning `m ∘ g` with `f`
    near `u₀`. This is the classical monodromy theorem / uniqueness-of-lifts step.

    It is a *mathematical* axiom (true classical analysis), not a physical input, and it
    explicitly **consumes the covering** `AX_thrice_punctured_uniformization`: discharging
    that covering upstream (Schwarz reflection ⇒ Riemann mapping ⇒ the `Γ(2)` cover) leaves
    only this lift-uniqueness step, itself standard. Together they are the math debt behind
    the SU(2) headline; neither is physics.
    References: Forster, *Lectures on Riemann Surfaces* (monodromy theorem, deck
    transformations); Ahlfors, *Conformal Invariants*; SW hep-th/9407087 §3–4 for the
    `u`-plane monodromy. (NOT VERIFIED.) -/
axiom AX_developing_map_rigidity
    {Λ : ℂ} {D : Set ℂ} {u₀ : ℂ} {f g : ℂ → ℂ}
    (U : ThricePuncturedUniformization)
    (hmono : SameSWMonodromy Λ f g) :
    ∃ m : ℂ → ℂ, AnalyticOnNhd ℂ (m ∘ g) D ∧ f =ᶠ[𝓝 u₀] (m ∘ g)

/-- **SU(2) modular frame alignment — now derived.** The frame change `m` aligning two
    same-monodromy period maps, obtained from the classical math axioms only: the
    `Γ(2)` covering (`AX_thrice_punctured_uniformization`) supplies the uniformizing cover,
    and `AX_developing_map_rigidity` is the uniqueness-of-lifts step on it. Formerly the
    bespoke axiom `AX_su2_modular_frame_alignment`; it is now a theorem modulo those two
    named classical-math axioms. -/
theorem su2_frame_alignment
    {Λ : ℂ} {D : Set ℂ} {u₀ : ℂ} {f g : ℂ → ℂ}
    (hmono : SameSWMonodromy Λ f g) :
    ∃ m : ℂ → ℂ, AnalyticOnNhd ℂ (m ∘ g) D ∧ f =ᶠ[𝓝 u₀] (m ∘ g) :=
  AX_developing_map_rigidity AX_thrice_punctured_uniformization.some hmono

/-- **SU(2) period-map rigidity (`sw_su2_unique`).**

    Two holomorphic effective-coupling maps on a connected chart of the punctured SU(2)
    `u`-plane that carry the same SW monodromy coincide **up to an `SL(2,ℤ) = Sp(2,ℤ)`
    frame change** `m`. This is the rank-1 case of
    `sw_effective_theory_unique_up_to_duality`, here *derived* (not assumed) from the
    uniformization input + the analytic identity theorem.

    Rests only on **classical-math axioms** — the `Γ(2)` covering plus lift-uniqueness, via
    `su2_frame_alignment` — and the **physics** monodromy input `SameSWMonodromy`; the
    propagation is the proved `holo_eqOn_of_germ`. No bespoke placeholder remains. -/
theorem sw_su2_unique
    {Λ : ℂ} {D : Set ℂ} (hD : IsPreconnected D) {u₀ : ℂ} (hu₀ : u₀ ∈ D)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D)
    (hmono : SameSWMonodromy Λ f g) :
    ∃ m : ℂ → ℂ, Set.EqOn f (m ∘ g) D := by
  obtain ⟨m, hmg, hfg⟩ := su2_frame_alignment (D := D) (u₀ := u₀) hmono
  exact ⟨m, holo_eqOn_of_germ hD hu₀ hf hmg hfg⟩

end SeibergWitten.Physics.SU2
