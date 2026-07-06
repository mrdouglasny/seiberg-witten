# Scope: `riemann-periods` — the weight-1 VHS over a moduli base

*Plan for a standalone Lean library that supplies the **family** period geometry the SW headline
needs — the missing middle between the single-fiber Jacobian libraries and `periodRigidityAxiom`
(names refreshed 2026-07-04 to the math-primary vocabulary). Per
`JACOBIAN_DEPENDENCY_EVAL.md` (archived, local `history/audit/`), building this discharges axiom Groups A (period geometry),
B (monodromy), E (Riemann bilinear / Siegel), leaving the SW headline on physics + standard-3.*

## Goal and what it discharges

A reusable, **SW-agnostic** library: the **weight-1 variation of Hodge structure** of a family of
(hyperelliptic) curves over a base `U ⊆ ℂ^r` — periods varying holomorphically, the period map into
Siegel, the Gauss–Manin monodromy, and the rigidity. It is the **weight-1 realization** of the
general-VHS Tau Ceti roadmap (`docs/tauceti-vhs/`), and the **library form** of our in-repo genus-1
prototype (`SeibergWitten/Physics/Genus1Periods.lean`).

Directly discharges:
- `periodRigidityAxiom`, `matterPeriodRigidityAxiom` (Group A) — its period geometry + rigidity + realize;
- `localMonodromy`, `AX_picard_lefschetz_local`, `SameSWMonodromy` (Group B) — its Gauss–Manin /
  Picard–Lefschetz monodromy;
- the inherited `AX_PeriodCycleBasis` / `Im τ ≻ 0` (Group E) — its Riemann bilinear relations.

Does **not** cover the genus-1 modular side-route (`Γ(2)` covering `AX_thrice_punctured_uniformization`,
`AX_developing_map_rigidity`; theta `AX_jacobi_quartic`, `AX_theta3_ne_zero`) — different area
(RMT+Schwarz / modular forms), and off the headline critical path once this lands.

## Position in the stack

```
docs/tauceti-vhs   (general, weight-general VHS — SPEC apex)
        ▲  realized at weight 1 by
  riemann-periods  ──── consumes ────►  jacobian-claude  (axiom-free per-fiber: period lattice,
   (THIS plan)                          Abel–Jacobi, genus, Jacobian torus)
        ▲  prototyped by                      (jacobian-challenge: branch-cut cycles, but axiomatic)
  Genus1Periods.lean  (G2: ∮ holomorphic in u — DONE, standard-3)
        ▲  consumed by
  seiberg-witten  (periodRigidityAxiom / matterPeriodRigidityAxiom / the headline)
```

**Depend on `jacobian-claude`** (axiom-free), not `jacobian-challenge`, for the per-fiber layer.

## Generality bar

- **Weight 1, curves.** Periods of `H¹` of a curve family; period map into `Siegel g`; monodromy in
  `Sp(2g, ℤ)`. Higher weight / general Griffiths domains are **out of scope** (that's the Tau Ceti
  general-VHS entry).
- **Genus-1 first, then general genus.** Stage 1 = elliptic (`g = 1`, the SU(2)/SU(2)-matter case),
  reusing the `Genus1Periods` prototype. Stage 2 = hyperelliptic general `g` (SU(N)).
- **SW-agnostic.** No `PeriodBase`/`PeriodChart`/physics; a bare curve family. The SW interface (L6) is a
  thin adapter that lives in `seiberg-witten`, not here.

## Layers (each a discharge-gated milestone)

- **L0 — the family.** A family of curves `y² = f(u, x)` over a base `U` (smooth locus = complement
  of the discriminant `Δ`); total space + fibration. Reuse jacobian-claude's `RiemannSurface` /
  curve API fibrewise.
- **L1 — homology local system.** `H₁` of each fibre with a (branch-cut) `ℤ`-basis, the **intersection
  form** (alternating, unimodular = the symplectic / Dirac pairing), assembled into the local system
  `R¹` over `U∖Δ`. *(jacobian-challenge has branch-cut cycles but axiomatizes the intersection form;
  jacobian-claude has the `H₁` type — port + prove the intersection form, the first real sub-task.)*
- **L2 — periods, holomorphic in moduli (Gauss–Manin / period map).** `∮_γ ω(u)` as **holomorphic
  functions of `u`**; the period matrix `τ(u)`; the period map `U∖Δ → Siegel g`. *(The family-variation
  layer absent from both Jacobian libs — the heart. Genus-1 holomorphy is already proved:
  `Genus1Periods.swPeriodSeg_hasDerivAt`, the G2 milestone, via the dominated-convergence lemma.)*
- **L3 — Riemann bilinear / polarization (Group E).** `τ(u)` symmetric with `Im τ(u) ≻ 0` — the
  weight-1 Hodge–Riemann relations. *(The genuinely hard sub-task. jacobian-claude has the proof
  path — Hodge-star positivity / integration by parts on the cut surface — but not the proof.)*
- **L4 — monodromy / Picard–Lefschetz (Group B).** Analytic continuation of the period map gives
  `ρ : π₁(U∖Δ) → Sp(2g, ℤ)`; around a node (simple discriminant zero) `ρ` is the **transvection** in
  the vanishing cycle; at an `A₂` cusp, **two** vanishing cycles of intersection `±1`. *(Discharges
  `localMonodromy`/`AX_picard_lefschetz_local` and the matter `MatterPeriodRigidityData` cusp data.)*
- **L5 — rigidity (period-frame uniqueness).** Two period maps with the same monodromy agree up to an
  `Sp(2g, ℤ)` frame change (the rigidity / fixed-part statement). *(Discharges
  `SameSWMonodromy` and `PeriodRigidity.rigidity` ⇒ `SymplecticReframing`.)*
- **L6 — the SW adapter (in `seiberg-witten`, not in `riemann-periods`).** Package L2–L5 into
  `PeriodRigidity` / `MatterPeriodRigidityData`, and `realize`: build a `PeriodChart` satisfying H1–H6 — H1
  (special geometry: the prepotential from the periods), H2/H3 (massless states = vanishing cycles),
  H6 (**SW-specific** weak-coupling asymptotics — the one-loop+instanton matching, a small lemma on
  top), H5 (the curve's R/flavor symmetry).

## Reuse vs new

| Reused (no new infra) | New (this library) |
|---|---|
| jacobian-claude: per-fibre period lattice (discrete, rank-`2g`), Abel–Jacobi holomorphy, genus, Jacobian torus (all **axiom-free**); `Genus1Periods` G2 (∮ holomorphic in `u`); Mathlib analysis (`hasDerivAt_integral_of_dominated…`, `IsOpen`, `Sp`, Siegel) | **L1** intersection form (prove, not axiomatize); **L2** the family/Gauss–Manin variation + period map; **L3** Riemann bilinear `Im τ ≻ 0`; **L4** monodromy by continuation + Picard–Lefschetz; **L5** rigidity |

## Hard sub-tasks (the risk)

1. **L3 Riemann bilinear / `Im τ ≻ 0`** — the one deep piece; jacobian-claude's Hodge-star route is
   the candidate.
2. **L4 monodromy by analytic continuation** — continuation of `(a, a_D)` around `Δ`, identifying the
   transvections; partly prototyped for SU(2) in `SU2Rigidity`/`Monodromy`.
3. **L1 intersection form** — proving (not axiomatizing) the unimodular alternating pairing on `H₁`
   (Poincaré duality), the gap both Jacobian libs leave open.

## Out of scope

- Higher-weight / general-Griffiths VHS (→ Tau Ceti `docs/tauceti-vhs/`).
- The `Γ(2)`/`λ`/`θ` modular content (→ separate RMT+Schwarz and modular-forms work; off critical
  path once this lands).
- The SW-specific H6 asymptotic matching (→ stays in `seiberg-witten`, a small lemma on top of L2).

## Staging and effort

- **Stage 1 (genus 1, elliptic):** L0–L5 at `g = 1`, building on the `Genus1Periods` prototype
  (L2 largely done) + jacobian-claude's elliptic case. Discharges `periodRigidityAxiom` for SU(2) and
  `matterPeriodRigidityAxiom`. Estimate: **a few active weeks** (L3 and L4 are the cost; L2 is prototyped).
- **Stage 2 (general genus, hyperelliptic):** L1–L5 for general `g`. Discharges `periodRigidityAxiom` for
  all SU(N). Larger — the general intersection form (L1) and general Riemann bilinear (L3) are the
  Mathlib-scale pieces; sister-project speedups apply once Stage 1 exists.

**Net:** Stage 1 (genus-1) `riemann-periods` is the high-leverage target — it collapses the SW
headline's period/VHS axioms to standard-3, with the residual being the (named) Riemann-bilinear
sub-task and the SW-specific H6 lemma.
