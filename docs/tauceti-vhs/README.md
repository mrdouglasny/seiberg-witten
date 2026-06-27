# Roadmap (draft): variation of Hodge structure and periods of families of curves

*A **draft Tau Ceti roadmap entry** we would propose to
[`FormalFrontier/TauCetiRoadmap`](https://github.com/FormalFrontier/TauCetiRoadmap) as
`TauCetiRoadmap/VHS/` (this `README.md` + `Targets.lean`). It lives in the seiberg-witten repo as
a working sketch (mirroring `tauceti-conformal-mapping/`): the period-level input our
Seiberg–Witten project needs (`../../audit/PERIOD_LAYER_SCOPING.md`) is one downstream
application, but the area — how the periods of a family of Riemann surfaces vary with the
parameters — is general Hodge theory that belongs upstream. Written to the roadmap repo's
conventions: build the library not the theorem, ground everything in Mathlib + the existing
per-fiber period library, pin conventions up front, write Lean signatures.*

The per-fiber theory **exists**: [`jacobian-challenge`](https://github.com/rkirov/jacobian-claude)
(Buzzard's Jacobian-API challenge, solved, plus a large period library) has, for a **single**
curve — hyperelliptic curves `y² = f(x)` with genus `⌊(deg f − 1)/2⌋` (`HyperellipticData`), the
holomorphic differentials, the A/B-period integrals (`Elliptic.Periods`), the period matrix and
its Riemann-bilinear positivity (`Layer3.PeriodLattice`), and the abelian-variety target
(`AbelianVariety.{Siegel, Theta, ComplexTorus}`). Mathlib has the analytic backbone underneath:
differentiation under the integral (`Analysis/Calculus/ParametricIntervalIntegral`), the upper
half plane and modular group, `Matrix.PosDef`, `Matrix.SpecialLinearGroup`.

What is **missing — everywhere, not just in Lean** — is the *family*: how those per-fiber periods
**vary** as the curve moves in a parameter. There is no Gauss–Manin connection, no period map of a
family, no monodromy representation of the periods, no Picard–Fuchs equation, no period-map
rigidity. `jacobian-challenge` treats each curve as a fixed object; this roadmap is the **variation
of Hodge structure (VHS) layer** built directly on top of it.

The goal is to build that families layer as a reusable library: a researcher in Hodge theory,
periods, modular forms, mirror symmetry, or mathematical physics finds the period map of a family,
its flat Gauss–Manin connection, the `Sp(2g,ℤ)` monodromy representation, and the rigidity theorem
at their natural generality — so that, e.g., "the periods of a family satisfy a Picard–Fuchs ODE
and are rigid given their monodromy" is a *consequence of a developed theory*, not an isolated
endpoint.

Suggested home: `TauCeti/Geometry/VHS/` (with `…/VHS/PeriodMap.lean`, `…/GaussManin.lean`,
`…/Monodromy.lean`, `…/Rigidity.lean`).

## Prior art

- **Mathlib:** none of this layer — no VHS, Gauss–Manin, period map of a family, or
  Picard–Fuchs; only the analytic backbone (differentiation under the integral, `ℍ`, the modular
  group, `Matrix.PosDef`, `Matrix.SpecialLinearGroup`).
- **`jacobian-challenge`:** the *per-fiber* theory (single-curve periods, period matrix +
  Riemann-bilinear positivity, hyperelliptic curves, `Siegel`/`Theta`/`ComplexTorus`), sorry-free.
  This roadmap **consumes** it and adds the family/variation layer; it does not re-derive periods.
- **Genus-1 anchor (already in Lean, standard-3).** That the genus-1 case is reachable is not a
  hope: in the seiberg-witten repo, `swEllipticData_genus` realizes the elliptic curve family
  `y² = (x²−u)² − Λ⁴` as `HyperellipticData` over the parameter `u` with genus 1 proved (via
  `jacobian-challenge`'s own genus formula), and `model_period_differentiable` proves the L0
  milestone (a parameter period integral is `Differentiable ℂ` in the modulus) end-to-end from
  Mathlib's `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
- **Other provers:** Gauss–Manin / VHS / period-map rigidity appear unformalized in any system —
  this is genuinely new material, not a port.

## Generality bar (decide up front; do not silently specialize)

- **Weight-1, polarized, integral VHS — i.e. families of curves / abelian varieties.** Target the
  weight-1 case (Jacobians); state the base as an open `B ⊆ ℂ^r` (or a complex manifold) and work
  relative to it. Higher weight is out of scope for this entry.
- **The period domain is the Siegel upper half space `Siegel g`** (`jacobian-challenge`'s
  `AbelianVariety.Siegel`), and the duality group is `Sp(2g, ℤ)`. Do not specialize to `g = 1`
  (`ℍ`, `SL(2,ℤ)`) except where a milestone is explicitly the genus-1 instance — but **do** ship
  `g = 1` first as the proved anchor, since the elliptic case sits on existing `ℍ`/modular/`λ`/`θ`
  machinery.
- **Curves given by a squarefree polynomial family.** Start concretely from
  `HyperellipticData` varying in a parameter (the form `jacobian-challenge` already supports and
  the SW anchor uses), rather than an abstract proper smooth family — generalize later.
- **Connection / flatness via Mathlib vocabulary.** State holomorphy with `DifferentiableOn ℂ` /
  `AnalyticOnNhd`, the connection as the `fderiv` of the period map, monodromy via analytic
  continuation along paths (`π₁` / covering), positivity via `Matrix.PosDef` on `Im τ`.

## Conventions (pinned)

- **Parameter / base:** `u ∈ U`, `U` open in `ℂ^r`; the discriminant locus `Δ = {u : C_u singular}`
  is closed, `U = Δᶜ` on the smooth locus.
- **Periods:** `a(u) = ∮_γ ω_u` for a cycle `γ` and the relative holomorphic 1-form `ω_u`; the
  period vector is `(∮_{A_i} ω, ∮_{B_i} ω)`; the normalized period matrix is
  `τ = (∮_B ω)(∮_A ω)⁻¹`.
- **Duality group:** `Sp(2g, ℤ)` (`= SL(2,ℤ)` at `g = 1`); period domain `Siegel g`.
- **Monodromy:** the representation `ρ : π₁(U) → Sp(2g, ℤ)` of analytic continuation; local
  monodromy at a `Δ`-component is the Picard–Lefschetz transvection `v ↦ v + ⟨v, δ⟩ δ` in the
  vanishing cycle `δ`.

## Layers (each a discharge-gated milestone; `sorry` in `Targets.lean` is the goal)

- **L0 — the period map is holomorphic (P1).** Periods of a holomorphic family vary holomorphically
  in the parameter — differentiation under the integral, packaged as a reusable lemma. *Already
  proved for a model integrand (`model_period_differentiable`); the library task is the clean
  general statement and the SW integrand `((x²−u)²−Λ⁴)^(−1/2)` (`cpow` off its branch cut, plus
  domination across the integrable `√`-singularity at the branch points).*
- **L1 — Gauss–Manin connection & Picard–Fuchs (P2).** The period vector is a flat section of a
  holomorphic connection on the base; equivalently it satisfies a linear ODE system (for `g = 1`, a
  second-order Fuchsian ODE with regular singular points on `Δ ∪ {∞}`).
- **L2 — the period map lands in Siegel (P3).** `τ(u)` is symmetric with `(Im τ)` positive definite
  (Riemann's bilinear relations, per-fiber from `jacobian-challenge`), so the period map is a
  holomorphic `U → Siegel g`; and there is a local prepotential with `∂τ` symmetric.
- **L3 — monodromy representation & Picard–Lefschetz (P4).** Analytic continuation gives
  `ρ : π₁(U) → Sp(2g, ℤ)`; the local monodromy around each `Δ`-component is the transvection in the
  vanishing cycle.
- **L4 — rigidity (P5, the summit for applications).** If `ρ` is irreducible, two period maps over
  the same base with the same monodromy differ by a constant element of the centralizer of `ρ`,
  hence (Schur) by a scalar; with a normalization fixing the scalar, the two period vectors are
  related by a single constant `Sp(2g, ℤ)` frame. (The genus-1 instance is the
  developing-map rigidity of the `ConformalMapping` roadmap — see below.)

## Relation to sibling roadmaps (this entry connects four)

- **Below — `jacobian-challenge`.** The per-fiber period theory, Jacobian, `Siegel`, `Theta`,
  Riemann-bilinear positivity — consumed, not re-derived. This roadmap is the family layer on it.
- **Below — `ContourIntegration` (PR #35).** Periods `∮_γ ω` are contour integrals; the period map
  and its variation consume the residue/winding/contour-deformation layer.
- **Adjacent — `ModularForms` (PR #36).** The genus-1 VHS **is** the universal elliptic curve over
  the modular curve: periods of the universal elliptic curve, `Y(Γ)(ℂ) ≅ Γ\ℍ` as the `g = 1`
  moduli base. This roadmap supplies the period/monodromy side; the modular-curve side is #36.
- **Adjacent — `ConformalMapping` (PR #38).** Its `Γ(2)` uniformization `ℍ/Γ(2) ≅ ℂ∖{0,1}` and
  developing-map rigidity are exactly the **genus-1 instance of L4** — the rank-1 period-map
  rigidity our SW project's `su2_deck_of_periodFrame` consumes.

## Downstream

- **Seiberg–Witten (this project).** L0–L4 discharge the `PeriodLayer`/`SWPeriodLayer` structure
  (`audit/PERIOD_LAYER_SCOPING.md`): L4 is the `rigidity` field, L0–L3 + a weak-coupling
  normalization assemble `realize`. The headline uniqueness/existence become unconditional.
- Periods of modular forms; mirror maps / mirror symmetry; the Torelli theorem; mixed Hodge theory
  — all sit downstream of a period-map + monodromy + rigidity library.

## References

Voisin, *Hodge Theory and Complex Algebraic Geometry I–II*. Carlson–Müller-Stach–Peters,
*Period Mappings and Period Domains*. Griffiths, *Periods of integrals on algebraic manifolds*
(I, II). Deligne, *Équations différentielles à points singuliers réguliers* (Gauss–Manin,
regularity). Clemens, *Picard–Lefschetz*. For the genus-1 / physics anchor: Seiberg–Witten,
*Nucl. Phys.* B426 (1994) [hep-th/9407087]; Klemm–Lerche–Yankielowicz–Theisen, *Phys. Lett.* B344
(1995). Per-fiber Lean library: `jacobian-challenge`.

---

*NOTE: the genus-1 anchor lemmas (`swEllipticData_genus`, `model_period_differentiable`) and the
L0 statement were drafted/elaborated against the seiberg-witten toolchain's Mathlib + the
`Jacobians` library; re-elaborate against `TauCetiRoadmap`'s pinned Mathlib when filing.*
