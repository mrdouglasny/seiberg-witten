# Plan: explicit genus-1 SW periods on pure Mathlib (discharge the rank-1 period layer)

*The reachable route to discharging `PeriodLayer Λ` (rank 1), decided after measuring the
alternatives: **build the SU(2) periods explicitly on pure Mathlib** — no Jacobian-challenge /
jacobian-claude dependency (insufficient), no abstract de Rham / Gauss–Manin diff-geo layer (its
prerequisites — de Rham cohomology, integration of forms — are absent from Mathlib and from the
858k-line external diff-geo project alike). At genus 1 the periods are explicit elliptic integrals;
everything the layer needs is reachable from Mathlib's analysis + the repo's existing modular-`λ`
machinery.*

## Why pure Mathlib suffices at genus 1

- **Periods are explicit elliptic integrals.** The SU(2) curve `y² = (x²−u)² − Λ⁴` is elliptic;
  `a(u), a_D(u)` are integrals of `λ_SW` over cycles, with `da/du ∝ ∮ dx/y` a complete elliptic
  integral — an honest `∫` of an explicit function, not an abstract period of a cohomology class.
- **Holomorphy in `u` is already proved reachable.** `Physics/PeriodVariationProbe.lean`
  (`model_period_differentiable`) discharges the parameter-integral holomorphy via
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` — **pure Mathlib, no Jacobian
  import**.
- **The rigidity engine already exists in this repo.** `ModularLambda` / `ThetaLambda` (the `Γ(2)`
  covering `ℍ/Γ(2) ≅ ℂ∖{0,1}`, the `θ`/`λ` functions), `SU2Rigidity.su2_frame_alignment`, and the
  zero-axiom `SU2Uniqueness.su2_deck_of_periodFrame` are the SU(2) period-rigidity machinery; they
  power `sw_su2_unique` already. The explicit periods feed them.

So genus 1 is *analysis + the existing modular layer*, not new infrastructure.

## The construction (G0–G7), with concrete targets

- **G0 — the curve and its branch locus.** `swCurveValue Λ u x = (x²−u)²−Λ⁴` (`= (swQuartic Λ u).eval x`,
  tying to `SWFamily`); branch points `x² = u ± Λ²`; the curve degenerates exactly at `u = ±Λ²`
  (target: `Squarefree (swQuartic Λ u) ↔ u ∉ {Λ², −Λ²}` for `Λ ≠ 0` — a discriminant computation).
  *Starter file `Physics/Genus1Periods.lean` lays down G0.*
- **G1 — the period integrals.** `swOmegaIntegrand Λ u x = (swCurveValue Λ u x)^(−1/2)` (the `dx/y`
  integrand); `a(u), a_D(u)` as integrals of `λ_SW` over the A/B cycles, with
  `a'(u) ∝ ∮ swOmegaIntegrand` (the holomorphic-differential period). Model the A-cycle concretely
  as the segment between two branch points (a real interval with `u`-dependent endpoints), the
  B-cycle as the complementary contour.
- **G2 — holomorphy (P1).** `a, a_D` holomorphic on `U = ℂ ∖ {±Λ²}`. **DONE for off-cut contours**
  (`Genus1Periods.lean`, standard-3): `swPeriodSeg_hasDerivAt` / `swPeriodSeg_differentiableAt` —
  the period `u ↦ ∫_a^b (dx/y)` over a contour off the branch cut has the explicit derivative
  `∫_a^b ∂/∂u(dx/y)`, via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, with every hypothesis
  discharged by per-`x` helpers (`…_differentiableAt_modulus`, `…_hasDerivAt_modulus`, `…_norm`,
  `…_deriv_norm`, `…_continuousOn_segment`, `…DerivIntegrand_continuousOn_segment`). **Remaining:**
  the *integrable* `√`-singularity at the branch-point endpoints of a full A-cycle + the moving
  endpoints (a substitution fixes the contour) — the domination across the singularity.
- **G3 — Picard–Fuchs (P2).** The SU(2) periods satisfy an explicit 2nd-order ODE in `u` (regular
  singular points at `±Λ², ∞`). Target: exhibit `p, q` and verify
  `a'' + p a' + q a = 0` (and same for `a_D`) by differentiating under the integral (G2's
  derivative formula). Pins the periods up to their `2`-dim solution space.
- **G4 — the coupling lands in `ℍ` (P3).** `τ(u) = a_D(u)/a(u)`; `Im τ > 0` from the elliptic
  period ratio (Riemann bilinear at `g = 1`, i.e. the lattice `ℤ a ⊕ ℤ a_D` is non-degenerate).
  Connect `τ` to the modular `λ` (`ModularLambda`): the `u`-plane is `Γ(2)\ℍ` via `λ`.
- **G5 — monodromy (P4) ⇒ derive `SameSWMonodromy`.** Analytic continuation of `(a, a_D)` around
  `u = ±Λ²` gives explicit **parabolic** `M_± ∈ SL(2,ℤ)` (the monopole/dyon Picard–Lefschetz
  transvections). **New work:** the continuation + identifying `M_±`. This *derives* the monodromy
  input that `sw_su2_unique` currently assumes as the `SameSWMonodromy` axiom.
- **G6 — rigidity (P5) ⇒ `PeriodLayer.rigidity`.** With G5's monodromy fixed, reuse
  `su2_frame_alignment` (the `Γ(2)`/developing-map rigidity, `AX_developing_map_rigidity`) to get the
  `SL(2,ℤ)` period frame, then `su2_deck_of_periodFrame` for the `Deck`. This is the field the layer
  needs; most of the engine is already proved.
- **G7 — `realize`.** Assemble `a, a_D, τ` on a simply-connected chart into a `Sheet` and verify
  H1–H6 (H1 from G3/G4, H2/H3 from G0/G5, H6 from the weak-coupling asymptotics of the elliptic
  integral). Discharges `PeriodLayer.realize`.

## Reuse vs new

| Reused (no new infra) | New work (genus-1 analysis) |
|---|---|
| `PeriodVariationProbe` (parameter-integral holomorphy); `ParametricIntervalIntegral`; `ModularLambda`/`ThetaLambda` (`Γ(2)`, `λ`, `θ`); `SU2Rigidity.su2_frame_alignment`; `SU2Uniqueness.su2_deck_of_periodFrame`; `SWFamily` (the curve); Mathlib `ℍ`/modular/`cpow` | **G2** holomorphy across the `√`-singularity + moving endpoints; **G3** the explicit Picard–Fuchs ODE (differentiate under the integral); **G5** the monodromy `M_±` by analytic continuation (derives `SameSWMonodromy`); **G0** the discriminant `↔ u ∈ {±Λ²}`; **G7** the weak-coupling asymptotics for H6 |

## Effort

A few active weeks. G6 (rigidity) is largely done (the modular engine + `su2_deck_of_periodFrame`
exist); the genuinely new pieces are **G2** (holomorphy with the integrable singularity — the
hardest), **G3** (Picard–Fuchs), and **G5** (monodromy). None needs a Jacobian library or a de Rham
layer. Discharging G2–G7 turns `sw_su2_unique_of_periodLayer` and `sw_su2_exists_of_periodLayer`
into unconditional theorems (footprint: standard-3 + the `Γ(2)`/`θ` covering axioms only).

## Explicitly NOT this route

- *Not* `jacobian-challenge` / `jacobian-claude` (insufficient to build on).
- *Not* the abstract de Rham / Gauss–Manin diff-geo layer (its prerequisites — de Rham cohomology,
  integration of forms over chains — exist nowhere in Lean; that is a separate, multi-year general
  infrastructure project, the right home for the *general*-genus VHS but overkill for rank 1).
