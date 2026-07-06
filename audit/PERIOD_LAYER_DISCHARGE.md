# Discharging `periodRigidityAxiom` via jacobian-challenge (leaving its classical-period axioms open)

*Plan, 2026-06-29; names refreshed 2026-07-04 to the math-primary vocabulary
(`periodRigidityAxiom`/`PeriodRigidity`, `PeriodChart`, `SymplecticReframing`,
`IsPolarizedPeriodChart` — the old physics names remain as `Dictionary.lean` abbrevs).
Goal: turn `periodRigidityAxiom` (our `Placeholder` axiom) into a **theorem** built on
jacobian-challenge's hyperelliptic period machinery, so the SW headline rests on jacobian-challenge's
recognized **classical-period axioms** (`AX_RiemannBilinear`, `AX_PeriodCycleBasis`) — not on a
placeholder of ours. Corrects the earlier jacobian-claude direction: jacobian-challenge is the right
source (it *has* the Riemann bilinear, and is already our dependency; jacobian-claude lacks it and
cannot be co-required — see `JACOBIAN_DEPENDENCY_EVAL.md` (archived, local `history/audit/`)).*

## Baseline already on the target footprint (verified)

`#print axioms` (2026-06-29):
- `sw_coupling_mem_siegel`, `sw_metric_posDef` (`SpecialGeometry.lean`) depend on
  `[propext, Classical.choice, Quot.sound, Jacobians.Axioms.AX_PeriodCycleBasis]`.

So the special-Kähler positivity (`τ ∈ Siegel`, `Im τ ≻ 0` — the no-ghost condition / H1 core) is
**already proved leaving jacobian-challenge's classical-period axiom open**, with **no
`periodRigidityAxiom`**. Also standard-3 (no period axiom): `transvection_isSymplectic` (Picard–Lefschetz
monodromy ∈ Sp), `su2_deck_of_periodFrame` (SL(2,ℤ) period frame ⇒ `SymplecticReframing`), and the `SWVariation`
weight-1-VHS *spec* (`Family.lean`).

## What discharge requires: prove `PeriodRigidity`'s two fields

`periodRigidityAxiom` provides `rigidity` and `realize`. Discharging = constructing a
`PeriodRigidity` term (a `def`), proving both on the jacobian-challenge footprint.

**`realize`** — the SW curve `y²=P²−Λ^{2N}` furnishes a `PeriodChart` with `IsPolarizedPeriodChart` (H1–H6).
Per-field status / route:

| H | field | route | status |
|---|-------|-------|--------|
| H1 | `SpecialGeometry` | periods `a,a_D` (jacobian-challenge `aPeriodIntegral`/`bPeriodIntegral`); `τ ∈ Siegel`, `Im≻0` from `AX_RiemannBilinear` | τ∈Siegel **done**; the prepotential `a_D=∂F/∂a`, `τ=∂²F/∂a²` **to build** |
| H2 | `PeriodsDegenerateOnBoundary` | at `Δ` the vanishing branch-cut cycle ⇒ a massless BPS charge (`BranchCutGeneratesPi1`) | **to build** |
| H3 | `PicardLefschetzAtGenericStratum` | family monodromy = transvection in the vanishing charge | `transvection_isSymplectic` done; **family monodromy to build** (L4) |
| H5 | `HasFiniteOrderAutomorphism` | the curve's `ℤ_{2N}` symmetry `u ↦ ω u` fixing `Δ` | algebraic, **to build** |
| H6 | `HasPrescribedAsymptotics` | weak-coupling asymptotics of the period integrals (one-loop + instanton) | **to build** (the hard analytic piece) |

**`rigidity`** — two SW theories over a connected overlap are `SymplecticReframing`-related.
- `N=2`: routes through `su2_deck_of_periodFrame` (zero-axiom) + the period frame (currently the
  `Γ(2)` developing-map route, `sw_su2_unique`).
- general `N`: the higher-genus `deck_of_periodFrame` + same-monodromy frame (see
  `PERIOD_LAYER_SCOPING.md` (archived, local `history/audit/`)).

## Residual debt after discharge

jacobian-challenge's **`AX_RiemannBilinear`** and **`AX_PeriodCycleBasis`** (its recognized
classical-period axioms, on *its* discharge roadmap) — replacing our `periodRigidityAxiom` placeholder.
The headline then reads: physics hypotheses (H0–H6) + standard-3 + jacobian-challenge's
classical-period axioms. (`matterPeriodRigidityAxiom` discharges the same way once `periodRigidityAxiom` does.)

## Milestones

- **R1 — the SW period map. ✅ DONE** (`SeibergWitten/Physics/PeriodMap.lean`, 2026-06-29).
  `sw_coupling_exists` (curve-point-free via the curve's `Nonempty` instance), `swModuliPoly_natDegree`,
  `swPeriodMap : u ↦ τ(u) ∈ Siegel(N−1)` on the smooth locus with `_isSymm` / `_imPosDef`. Footprint
  `[standard-3 + AX_PeriodCycleBasis]`, no `periodRigidityAxiom`.
- **R1+ — the SW family is a weight-1 VHS. ✅ DONE** (same file). `swDiscriminant`, `swVariation`:
  given the vanishing charges, an `SWVariation` with `period := swPeriodMap` and `monodromy :=`
  transvection (`Loop := Δ` ⇒ `picard_lefschetz` by `rfl`). Same footprint.
- **R2a — the SW period `a(u) = ∮ λ_SW`. ✅ DONE** (`Genus1Periods.lean`, genus-1). The wall below was
  *breached* by building `λ_SW` directly (not via jacobian-challenge): `swLambdaIntegrand = x²·(dx/y)`,
  `swLambdaSeg = ∮ λ_SW`, `swLambdaSeg_hasDerivAt` (holomorphy in `u`). Footprint **standard-3**.
- **R2b — the special-geometry / Picard–Fuchs relation. ✅ DONE** (`Genus1Periods.lean`, genus-1, all
  standard-3). `swLambda_ibp_hasDerivAt` (the IBP identity `x²(x²−u)y⁻³ = ½y⁻¹ + d/dx(−x/(2y))`),
  `swLambda_ibp_integral` (FTC), `swLambda_deriv_eq_half_period` (`∂a/∂u = ½·swPeriodSeg + boundary`,
  i.e. `∂a/∂u = ½ ∮ dx/y`).
- **R2c — closed-cycle periods `a(u), a_D(u) : ℂ → ℂ` → H1. ⛔ THE LIFT** (the remaining analytic core).
  The genus-1 *segment* prototype (R2a/R2b) gives the integrand, holomorphy, and the special-geometry
  relation modulo a boundary term. To get the genuine special coordinates we need the **closed A/B
  cycles** (loops around the branch points `x = ±√(u±Λ²)`) so the boundary term vanishes and `a, a_D`
  become single functions of `u`; then the prepotential `F` (`a_D = ∂F/∂a`, `τ = ∂²F/∂a²` — `F` exists
  by the Poincaré lemma since `τ` is symmetric, R1) gives `PeriodChart.SpecialGeometry` (H1). This is the
  closed-contour/cycle modeling layer — a sustained build, not a single step.
- **R3 — `realize`/H2–H3.** Needs `a, a_D` (R2c) + the monodromy gluing `SymplecticReframing`. H2 forces `a, a_D`
  physical (`Z_n` vanishes at `Δ`).
- **R4 — `realize`/H5–H6.** **H5 definition fixed (2026-06-30)** — `HasFiniteOrderAutomorphism` is
  now a nontrivial `ℂ`-linear automorphism of order *dividing* `2N` fixing `Δ`, with a non-vacuity
  witness (`hasFiniteOrderAutomorphism_of_neg_invariant`, standard-3: the physical `u → −u`). H6 (weak-coupling asymptotics of `a, a_D`) needs
  R2c + asymptotic analysis (hardest).
- **R5 — `rigidity`.** SU(2) (period frame) then general `N`.
- **R6 — assemble the `PeriodRigidity` term** replacing `periodRigidityAxiom`; re-print axioms
  (expect standard-3 + `AX_RiemannBilinear` + `AX_PeriodCycleBasis`, no `periodRigidityAxiom`).

## Status (2026-06-29) and effort

**Done (genus-1):** R1 + R1+ (period map → Siegel, the VHS object) on `[standard-3 +
AX_PeriodCycleBasis]`; **R2a + R2b** (the SW period `a = ∮ λ_SW`, its holomorphy, and the
special-geometry relation `∂a/∂u = ½∮dx/y`) on **standard-3**. The earlier "R2 wall" — that the SW
differential's periods aren't in jacobian-challenge — was breached by **building `λ_SW` directly** on
Mathlib's integration engine (the `swOmega*`/`swLambda*` dominated-derivative + FTC machinery). The
**genus-1 analytic engine is complete.**

**The lift (R2c onward):** the remaining `realize` requires the **closed-cycle special coordinates
`a(u), a_D(u)`** — vanishing at `Δ` (H2), with the prepotential `F` (H1) of weak-coupling form (H6).
The pointwise/segment analytics are done; what remains is the multi-week build (the closed A/B-cycle
contours, the prepotential, asymptotics, the
monodromy gluing). H5 (R-symmetry) is algebraic; its definition was fixed (above);
either way `realize` needs *all* of H1–H6, so it cannot complete without the special coordinates.

This is the genuine period-geometry build scoped in `audit/RIEMANN_PERIODS_SCOPE.md`: routing through
jacobian-challenge (axioms open) got the period matrix → R1/R1+ for free, but the SW special
coordinates remain the real analytic work.
