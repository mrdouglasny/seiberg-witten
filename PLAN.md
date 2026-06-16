# PLAN — formalizing the Seiberg–Witten solution of N=2 SU(N) SYM

Per-phase: **target theorems**, **what they reduce to** in `jacobian-challenge`
(with the actual API), **effort**, **what it unlocks**, and **risks/gaps**. Status:
✅ done · 🔶 in reach · 🔬 needs new machinery. Each landed result adds a row to
[`audit/CORRESPONDENCE_INDEX.md`](audit/CORRESPONDENCE_INDEX.md) and a numeric
cross-check where a period/τ is computed.

## The dependency we build on

| SW object | jacobian-challenge API |
|---|---|
| SW curve (hyperelliptic) | `Jacobians.ProjectiveCurve.HyperellipticData`, `HyperellipticEvenProj` |
| genus | `Extensions.HyperellipticEven.genus_HyperellipticEven_eq` |
| holomorphic differentials `ωₖ` | `RiemannSurface.HolomorphicOneForm` |
| period lattice / `H₁` | `periodMapInBasis`, `periodLatticeInBasis`, `H1` |
| period matrix `τ ∈ Siegel` | `AbelianVariety.SiegelUpperHalfSpace`, `Layer3.riemannBilinear_exists` |
| Riemann bilinear R1/R2 | `Axioms.PeriodCycleBasis` (fields `R1`/`R2`); witnesses: `ellipticPeriodCycleBasis` (g=1, ℂ/Λ, **standard-3**), hyperelliptic (partial) |
| intersection form | `Axioms.intersectionForm`, `AX_IntersectionForm_{alternating,perfect}` |
| Jacobian / complex torus | `AbelianVariety.ComplexTorus`, `Jacobian` |
| meromorphic functions / divisors | `MeromorphicFunction`, `Divisor`, `abelJacobiDiv` |
| Riemann–Roch / Serre | `Layer3.riemannRochL3`, `serreDualityL3` |

---

## Phase 0 — the curve and its genus ✅

**Done.** `SeibergWitten.genus_swCurve`: the SU(N) curve `y² = P_N² − Λ^{2N}`
(`swData`, a `HyperellipticData` with `f = P_N² − Λ^{2N}`, squarefree = smooth
locus) has **genus `N − 1`**. Reduces to `genus_HyperellipticEven_eq` (degree `2N`
even ⇒ the even-atlas `Fact`, supplied as `instFactEvenSW`). `#print axioms` =
standard-3. *Effort: done (~1h).* **Unlocks:** everything below is stated on this
curve type.

---

## Phase 1 — special geometry: `τ ∈ Siegel`, metric positivity 🔶 (headline)

**Targets.**
- `swTau` : the period matrix of the SW curve, `τ ∈ SiegelUpperHalfSpace (N−1)`
  (i.e. `τ = τᵀ` and `Im τ ≻ 0`), via `Layer3.riemannBilinear_exists` on
  `HyperellipticEvenProj (swData …)`.
- `sw_metric_pos` : the special-Kähler metric `(ds² = Im(da_D dā))` is
  positive-definite on the smooth Coulomb branch — i.e. `Im τ ≻ 0` restated as the
  physical no-ghost statement. The interpretive identification "this `τ` is the SW
  effective coupling matrix" is part of the statement/`FAITHFULNESS` note.

**Reduces to.** `riemannBilinear_exists x₀ : τ(X) ∈ SiegelUpperHalfSpace (genus X)`,
fed by the curve's `PeriodCycleBasis` R1/R2 fields. So Phase 1 = supply a
`PeriodCycleBasis` for the SW curve and apply the engine.

**Sub-tasks / honest gating.**
- **1a — SU(N), modulo `AX_PeriodCycleBasis`.** For general genus the hyperelliptic
  `PeriodCycleBasis` is currently `AX_PeriodCycleBasis`-backed (off the Buzzard
  critical path, but an axiom). `τ_SW ∈ Siegel` then holds *modulo that axiom*.
  *Effort: ~days* (mostly the physics identification + wiring).
- **1b — SU(2), axiom-free.** The genus-1 case. **Caveat:** the unconditional
  `ellipticPeriodCycleBasis` is for the `ℂ/Λ` model `Elliptic ω₁ ω₂`, **not** for the
  quartic `HyperellipticEvenProj` the SW curve is built as. Closing 1b axiom-free
  needs either (i) a genus-1 *hyperelliptic* `PeriodCycleBasis` witness, or
  (ii) a biholomorphism SW-quartic ≅ `Elliptic ℂ/Λ` (Weierstrass uniformization /
  `j`-invariant) to transport `ellipticPeriodCycleBasis`. *Effort: ~1–2 weeks;*
  route (i) is likely shorter and also advances jacobian-challenge's hyperelliptic
  R1/R2.

**Unlocks.** The first physically meaningful theorem (metric positivity). Also the
`τ`-as-coupling object that Phases 2–3 differentiate / continue.
**Risks.** The hyperelliptic `PeriodCycleBasis` (the same wall as jacobian's general
R1/R2). Numeric check: compute `τ(u)` for sample moduli, confirm `Im τ ≻ 0`.

---

## Phase 2 — special coordinates and the prepotential 🔬

**Targets.**
- `swPeriods` : `aᵢ, a_{D,i} = ∮_{Aᵢ,Bᵢ} λ_SW`, with `λ_SW` the SW meromorphic
  differential (`∂λ_SW/∂uₖ = ωₖ` holomorphic; `Res λ_SW` = masses).
- `sw_special_geometry` : `a_{D,i} = ∂F/∂aᵢ` for a prepotential `F`, and
  `τ_{ij} = ∂a_{D,i}/∂a_j = ∂²F/∂aᵢ∂aⱼ` — tying Phase 1's `τ` to `F`.

**Reduces to / new machinery.** jacobian's period map is for **holomorphic** forms;
`λ_SW` is **meromorphic** (poles ↔ masses), so this needs a meromorphic-1-form
period layer (periods + residues), building on `MeromorphicFunction` and the Kirov
port's residue machinery. The `a_D = ∂F/∂a` relation is the special-geometry
closedness (an integrability statement over the moduli space).

*Effort: large (multi-week to month).* **Unlocks.** The full SW low-energy
effective action; the BPS central charge `Z = n_e a + n_m a_D`.
**Risks.** Meromorphic-period infrastructure is the main build; moduli-space
differentiation (`∂/∂uₖ`) needs a family/variation-of-Hodge-structure setup.
**Dependency:** add `picard-lefschetz` here (contour deformation across poles ⇒
residues; and Phase-3 asymptotics).

---

## Phase 3 — singular locus, Argyres–Douglas, Picard–Fuchs 🔬

**Targets.**
- `sw_discriminant` : the Coulomb-branch singular locus = zero set of the curve
  discriminant `disc(P_N² − Λ^{2N})`; the curve degenerates ⇔ a cycle vanishes ⇔ a
  BPS state becomes massless.
- `sw_argyres_douglas` : AD loci = where the discriminant has a **higher-order**
  zero (mutually non-local cycles collide); characterized as a coincidence condition
  on branch points.
- `sw_picard_fuchs` : the periods `a(u), a_D(u)` satisfy the Picard–Fuchs ODE system;
  weak-coupling asymptotics `a ~ √(2u)`, `τ ~ (i/π)log…` (one-loop + instantons).

**Reduces to.** Discriminant: Mathlib polynomial `discriminant` + the squarefree↔
smooth dictionary (we already use `Squarefree`). AD: branch-point coincidence
(algebraic). PF + asymptotics: **`picard-lefschetz`** (`AsymptoticMethods`:
Laplace/WKB/Mellin–Barnes for the period integrals).

*Effort: medium–large.* **Unlocks.** The global structure of the Coulomb branch;
contact with your AD-theory work. **Risks.** PF derivation from the period family;
the asymptotics need the meromorphic periods of Phase 2.

---

## Phase 4 — monodromy, BPS spectrum, integrable system 🔬 (stretch)

**Targets.** Monodromy representation `π₁(Coulomb ∖ sing) → Sp(2(N−1), ℤ)` via the
**Picard–Lefschetz formula** (`x ↦ x ± ⟨x,δ⟩δ` on a vanishing cycle `δ`); the BPS
spectrum / wall-crossing; the periodic-Toda reformulation; and (long-run) the
**Nekrasov/localization** route to the *same* `F` as a cross-check.

**Reduces to / new machinery.** The topological Picard–Lefschetz formula is **not**
in `picard-lefschetz` (that's the asymptotics flavor) — it would be new, built on
jacobian-challenge's `H₁` + `intersectionForm`. The localization route is where
`picard-lefschetz`'s SUSY-localization purpose meets this project.

*Effort: research-scale.* **Risks.** Monodromy/vanishing-cycle machinery is a
genuine gap; Toda/Nekrasov are large independent developments.

---

## Ordering & the critical path

`0 ✅ → 1a (modulo AX_PeriodCycleBasis) → 1b (axiom-free SU(2)) → 2 → 3 → 4`.
Phase 1a is the quickest next win (wire `riemannBilinear_exists` to the SW curve);
1b and the hyperelliptic `PeriodCycleBasis` are shared with jacobian-challenge's own
endgame. Phase 2's meromorphic-period layer is the largest single build and gates
3–4. Each phase: land the theorem, add the correspondence-index row, attach a
numeric cross-check (`numeric: pass@…`) once a period/τ is computed.
