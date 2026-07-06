# seiberg-witten

Formalizing the **Seiberg–Witten solution of N=2 SU(N) super Yang–Mills** in Lean 4.
The main library is **self-contained on pinned Mathlib**; the higher-genus
Riemann-surface layer (built against
[`jacobian-challenge`](https://github.com/mrdouglasny/jacobian-challenge)) lives in
`HigherGenus/`, outside the build — see its README.

The low-energy data of the theory *is* the period geometry of a family of algebraic
curves, so it sits directly on top of that machinery:

| SW physics (KLYT / Argyres–Faraggi / Lerche) | Our Lean foundation |
|---|---|
| SW curve `y² = P_N(x)² − Λ^{2N}` (hyperelliptic, genus `N−1`) | `jacobian-challenge` hyperelliptic family |
| holomorphic differentials `ωₖ = x^{N−1−k}dx/y = ∂λ_SW/∂uₖ` | `HolomorphicOneForm` |
| special coords `aᵢ, a_{D,i} = ∮ λ_SW` | period map over `H₁` |
| effective coupling `τ_{ij} = ∂a_{D,i}/∂a_j = ∂²F/∂aᵢ∂aⱼ` | the curve's period matrix |
| special-Kähler consistency `τ = τᵀ`, `Im τ ≻ 0` | Riemann bilinear relations (R1/R2) |

## Plan (milestones)

Full per-phase plan (target theorems, what each reduces to in jacobian-challenge,
effort, risks) is in [`PLAN.md` (archived, local `history/`)](PLAN.md). Summary:

- **Phase 0 — curve + genus.** ✅ The SU(N) curve `y²=P_N²−Λ^{2N}` as a hyperelliptic
  instance; **`genus = N−1`** proved (`SeibergWitten/Curve.lean`, axiom-clean, via
  jacobian-challenge's `genus_HyperellipticEven_eq`).
- **Phase 1 — special geometry (headline).** Holomorphic basis `ωₖ`, period matrix
  `τ`; prove **`τ = τᵀ` (R1) and `Im τ ≻ 0` (R2) ⇒ the special-Kähler metric is
  positive** on the smooth Coulomb branch. *SU(2) first* (genus 1 — reachable
  **axiom-free** from jacobian-challenge's unconditional elliptic period witness),
  then SU(N).
- **Phase 2 — special coordinates + prepotential.** Meromorphic `λ_SW` (residues =
  masses), periods `a, a_D`, `a_D = ∂F/∂a`, `τ = ∂²F/∂a²`. Needs the
  meromorphic-period (mass) layer.
- **Phase 3 — singular locus + Argyres–Douglas + Picard–Fuchs.** The discriminant
  stratification; AD loci as higher-order curve degenerations; Picard–Fuchs ODEs for
  the periods (links `math-commons/picard-lefschetz` for weak-coupling/instanton
  asymptotics).
- **Phase 4 (stretch) — monodromy `Sp(2(N−1),ℤ)`, BPS spectrum, periodic Toda.**

## Dependencies

- **Now:** `jacobian-challenge` (hyperelliptic curves, `HolomorphicOneForm`, period
  lattice, `ComplexTorus`/Jacobian, intersection form, Riemann bilinear).
- **Later (Phase 2–3):** `picard-lefschetz` (`AsymptoticMethods`) — contour
  deformation underpinning periods, Laplace/WKB/Mellin–Barnes for period asymptotics,
  and the SUSY-localization (Nekrasov) route to the *same* prepotential as a deep
  cross-check. *Not yet a dependency — added when Phase 2/3 needs it.*
- The topological monodromy / vanishing-cycle Picard–Lefschetz *formula* (Phase 4) is
  **not** in `picard-lefschetz` (which is the asymptotics flavor); it would be new
  machinery on jacobian-challenge's H₁ + intersection-form layer.

## Assurance

**Reviewing this project? Start at [`audit/REVIEWER.md`](audit/REVIEWER.md)** — the
claims, what each rests on, and the three commands that verify it independently.

A **forward-chaining** corpus project — it follows
[`math-commons/formalization-assurance`](https://github.com/math-commons/formalization-assurance)
in forward mode: a `CORRESPONDENCE_INDEX` mapping each KLYT/Argyres–Faraggi/Lerche
equation to its Lean form, `FIDELITY_REVIEW` with **numeric cross-checks** (periods
and `τ` are computable — diff against an independent reference), and a
`formalization.yaml` card. Axiom audit stays ≈ standard-3 (it inherits only
jacobian-challenge's, and Phase 0 is axiom-clean).

## Status

v0.1 — **Phases 0 + 1a landed**: genus `N−1` (axiom-clean); and the SW coupling
`τ ∈ SiegelUpperHalfSpace (N−1)` ⇒ `τ = τᵀ` and `Im τ ≻ 0` (special-Kähler metric
positivity), modulo the off-critical-path `AX_PeriodCycleBasis`. Plus the SU(2)
(original SW) genus-1 specialization. Build wires `jacobian-challenge` as a Lake
path dependency; see `BUILD.md`. Next: Phase 1b (axiom-free SU(2)) and Phase 2
(special coordinates / prepotential).

**Physics-foundations layer** (`SeibergWitten/Physics/`) — the project's foundations track: the SW
physical hypotheses H0–H7 as contentful predicates and structures (the fixed-Λ content bundled as
`IsPolarizedPeriodChart`; H4 in the atlas gluing; H7 the family-level `SpurionCovariantFamily`).
**SU(2)/genus one is the fully proved route**: uniqueness (`SU2.sw_su2_unique`) reports
**standard-3 + the `Γ(2)` covering/lift pair only** — `SameSWMonodromy` is a *definition* (demoted
from an axiom 2026-07-04), and **no physical axiom exists anywhere**; the explicit coupling layer
adds the classical `AX_elliptic_inversion` (Jacobi inversion), the λ/θ layer the θ pair. The
higher-rank headline — uniqueness up to `Sp(2(N−1),ℤ)` duality
(`sw_effective_theory_unique_up_to_duality`, atlas-level `sw_unique_up_to_duality`) and existence
(`sw_curve_admits_effective_theory`), in `Physics/PeriodLayer.lean` — is a **proved skeleton modulo
one consolidated math axiom `periodRigidityAxiom`** (the period-level Picard–Fuchs / Gauss–Manin
geometry, discharge = future work). No `sorry` in the main compiled `SeibergWitten`/`RiemannPeriods`
libraries — after relocating development scratch to the local `history/` archive, no `sorry`
remains in any tracked Lean source. Full axiom list: `AXIOM_AUDIT.md`; the golden `#print axioms`
certificate is `audit/axiom-report.txt` (regenerate/check: `bash audit/gen_axiom_report.sh
[--check]`); the write-up: `docs/paper1.tex`.

**Discharging `periodRigidityAxiom`** (`audit/PERIOD_LAYER_DISCHARGE.md`) — in
progress, routed through jacobian-challenge's classical-period axioms (`AX_RiemannBilinear`,
`AX_PeriodCycleBasis`) rather than the placeholder. The genus-1 **analytic engine is built**, adding
**no new axioms**: `swPeriodMap`/`swVariation` (period map `u↦τ(u)∈Siegel`, the weight-1 VHS object;
standard-3 + `AX_PeriodCycleBasis`), and the SW special coordinate `a=∮λ_SW` with holomorphy, the
integration-by-parts identity, and the special-geometry relation `∂a/∂u=½∮dx/y` (R2a/R2b, all
**standard-3**, in `Physics/Genus1Periods.lean`). Remaining (multi-week): R2c closed-cycle periods →
`PeriodChart.SpecialGeometry` (H1) → H2/H3/H6 → rigidity → assemble `def periodRigidityAxiom`.

## License

Copyright 2026 Michael R. Douglas. Released under the
[Apache License 2.0](LICENSE) (the Lean/Mathlib ecosystem convention).
