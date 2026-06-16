# seiberg-witten

Formalizing the **Seiberg–Witten solution of N=2 SU(N) super Yang–Mills** in Lean 4,
built on [`jacobian-challenge`](https://github.com/mrdouglasny/jacobian-challenge)'s
Riemann-surface / period / Jacobian machinery.

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
effort, risks) is in [`PLAN.md`](PLAN.md). Summary:

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
