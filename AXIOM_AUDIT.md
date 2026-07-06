# Axiom audit — seiberg-witten

*Last updated 2026-06-30.*

**Naming (math-primary).** The period axioms and their carriers are stated in mathematical vocabulary — `periodRigidityAxiom : PeriodRigidity`, with `PeriodBase`/`PeriodChart`/`SymplecticReframing`/`IsPolarizedPeriodChart`; the physics names (`swPeriodLayer`, `CoulombBase`, `Sheet`, `Deck`, `IsSWEffectiveTheory`, …) are machine-linked `abbrev` aliases in `SeibergWitten/Physics/Dictionary.lean`. `#print axioms` reports the math names.

**Verification (kernel facts, generate-don't-author).** The golden `#print axioms` trace is [`audit/axiom-report.txt`](audit/axiom-report.txt), emitted by the driver [`audit/axiom_report.lean`](audit/axiom_report.lean) over every headline / matter / beta / spine result. Regenerate or check drift with `bash audit/gen_axiom_report.sh [--check]`; the counts in this file are read from it, never hand-authored.

Format + conventions:
[`math-commons/formalization-assurance/AXIOM_AUDIT_FORMAT.md`](https://github.com/math-commons/formalization-assurance/blob/main/AXIOM_AUDIT_FORMAT.md).
This is a **forward-chaining** project (formalizing the SW corpus on top of
`jacobian-challenge`); the primary assurance artifact is the
[correspondence index](audit/CORRESPONDENCE_INDEX.md), not the axiom audit.

The **rigorous spine** (Phases 0–2) declares **no axioms of its own**; its
jacobian-challenge-facing part (genus, Riemann-bilinear positivity) was moved to the
unbuilt `HigherGenus/` layer (2026-07-06), so the built library carries **no
`Jacobians` axiom** — the golden trace is Jacobians-free. The **physics foundations**
layer (`SeibergWitten/Physics/Hypotheses.lean`) carries the physical content as named
**predicates and structures** (H0–H7), assumed as *hypotheses in theorem types* — no
physical `axiom` exists anywhere in the development (`SameSWMonodromy`, the last one,
was demoted to a definition 2026-07-04). The `axiom` declarations that remain are
**classical mathematics** (the Γ(2) covering/lift pair, Jacobi inversion, the θ pair)
plus the consolidated higher-rank period-geometry input `periodRigidityAxiom`
(future-work debt); each is named, cited, numerically vetted, and tracked per theorem
by the golden trace `audit/axiom-report.txt`.

## Rigorous spine (own axioms: 0)

| Result | Phase | `#print axioms` |
|---|---|---|
| `genus_swCurve`, `genus_swCurve_su2` | 0 | **standard-3** |
| `sw_coupling_mem_siegel*`, `sw_metric_posDef` | 1a | standard-3 + `Jacobians.Axioms.AX_PeriodCycleBasis` |
| `su2_singular_locus` (curve singular ⟺ `u=±Λ²`), `su2_squarefree_of_ne`, `holo_eqOn_of_germ` | 1b | **standard-3** |
| `transvection_isSymplectic` (Picard–Lefschetz monodromy ∈ Sp), `intersectionForm_*` bilinearity | 3 | **standard-3** |
| `symplecticMonoid` (Sp(2r,ℤ) as a submonoid), `SWVariation` spec + coherence lemmas | 3 | **standard-3** (no new axioms) |
| `WeightOneVHS` (base-agnostic weight-1 VHS spec), `SWVariation.toVHS` (SW is an instance) | 3 | **standard-3** (no new axioms) |
| `siegelOneEquiv` (`Siegel 1 ≃ ℍ`), `MulAction SL(2,ℤ) (Siegel 1)`, `siegelOneEquiv_smul` (g=1 Sp-action) | 3 | **standard-3** (no new axioms; built on Mathlib `ℍ` action) |
| `duality_preserves_metric_posDef`, `siegelOne_smul_im_pos`, `metric_posDef_of_h4'` (H4′: EM duality ⇒ special-Kähler positivity is duality-stable) | 3 | **standard-3** (the `H4'`-consequence also transits the `SmoothCover` carrier) |
| `su2DualityMap`, `su2_deck_of_periodFrame` (Step C of SU(2) uniqueness: SL(2,ℤ) period frame ⇒ duality `SymplecticReframing`, with symplectic + covariant from det 1) | 1b | **standard-3** (no axioms) |
| `PeriodLayer`/`PeriodRigidity` (period-level debt as a *structure*) + `sw_su2_unique_of_periodLayer`, `sw_su2_exists_of_periodLayer`, `sw_unique_of_swPeriodLayer`, `sw_exists_of_swPeriodLayer`, `PeriodLayer.toGeneral` (SU(2)/SU(N) B.1 goals proved *modulo* the layer) | — | **standard-3** (period-level debt is a hypothesis, not an axiom; vetted GR — connectedness, trace-free SU(N) slice, `N≥2` guard) |
| `su2BaseEquiv` (SU(2) base `ℂ∖{±Λ²} ≃ ℂ∖{0,1}`), `affineEquiv` | 1b | **standard-3** (no new axioms) |
| `theta3_eq_jacobiTheta`, `theta3_add_two`, `theta4_add_two`, `modularLambdaFn` def, `oneMinusLambda` | 1b | **standard-3** + `AX_jacobi_quartic`, `AX_theta3_ne_zero` (`oneMinusLambda` only) |
| `modularLambda_add_two` (`λ(τ+2)=λ(τ)`, i.e. `T²∈Γ(2)`-invariance), `theta2_pow_four`, `theta2_add_two_pow_four` | 1b | **standard-3** (proved dent in `AX_thrice_punctured_uniformization`'s Γ(2)-invariance) |
| `theta3_neg_inv`, `theta2_neg_inv` (θ₃, θ₂ modular S-laws `θ(-1/τ)=(-iτ)^½·θ`) | 1b | **standard-3** (both proved from Mathlib's `jacobiTheta₂_functional_equation`) |
| `modularLambda_S` (`λ(-1/τ)=1-λ(τ)`, the S-transformation) | 1b | standard-3 + `AX_jacobi_quartic`, `AX_theta3_ne_zero` |
| `modularLambda_ST2S` (invariance under 2nd `Γ(2)` generator `ST²S⁻¹`) | 1b | standard-3 + `AX_jacobi_quartic`, `AX_theta3_ne_zero` (no new axioms; with `_add_two` → full `Γ(2)`-invariance) |
| **SW period engine** (genus-1): `swPeriodMap`/`swVariation` (period map `u↦τ(u)∈Siegel`, the weight-1 VHS object); `swLambdaSeg` (the SW special coordinate `a=∮λ_SW`) + holomorphy; `swLambda_ibp_hasDerivAt`/`swLambda_ibp_integral`/`swLambda_deriv_eq_half_period` (IBP + FTC ⇒ special-geometry relation `∂a/∂u=½∮dx/y`) | 2 | `swPeriodMap`/`swVariation`: standard-3 + `AX_PeriodCycleBasis`; the `λ_SW` + special-geometry chain (R2a/R2b): **standard-3** (pure Mathlib, **adds no axioms**) |

Phase 0 (genus) is standard-3. Phase 1a (special geometry / metric positivity) transits
the inherited `AX_PeriodCycleBasis` — jacobian-challenge's hyperelliptic cycle-basis
axiom, **off the Buzzard critical path**. The axiom-free SU(2) route (Phase 1b) would
remove it for genus 1.

## Physics foundations — hypotheses (`Physics/Hypotheses.lean`)

After the strengthening refactor, the physical inputs **H0–H6 are no longer axioms**: they are
*contentful predicates and structures* — `PeriodBase`, `PeriodChart`, `PeriodChart.SpecialGeometry` (H1),
`PeriodChart.PeriodsDegenerateOnBoundary`/`PeriodVanishesAt` (H2), `PicardLefschetzAtGenericStratum` (H3),
`SymplecticReframing` (H4), `HasFiniteOrderAutomorphism` (H5), `PeriodChart.HasPrescribedAsymptotics`/`Instantonic` (H6) — bundled in
`IsPolarizedPeriodChart` and **assumed as hypotheses** of the headline theorems, so they never enter
the trusted base. The headline implications `sw_effective_theory_unique_up_to_duality`,
`sw_unique_up_to_duality`, and `sw_curve_admits_effective_theory` (`Physics/PeriodLayer.lean`) are
now **proved theorems — no `sorry`** — resting on the physics postulates plus the single
period-level math axiom `periodRigidityAxiom` (`#print axioms` = **standard-3 + `periodRigidityAxiom`**). The
rank-1 uniqueness `SU2.sw_su2_unique` rests instead on the finer `B.2` covering/lift axioms +
`SameSWMonodromy`. `coulombBranchDim` (`dim ℂ^{N-1} = N−1`) is **proved**. The old opaque physics
axioms (`SpecialGeometry`, `EMDualityConsistent`, `SmoothCover`, …) are **retired**.

So the remaining axioms are **mathematical** — all of them: the former rank-1 physical exception `SameSWMonodromy` was demoted to a *definition* (2026-07-04, see below) — the consolidated period axiom
`periodRigidityAxiom`, and the finer monodromy / modular / covering inputs below (the genus-1 pieces of
that period geometry, used by the rank-1 route). Reviewed by Gemini (GR) 2026-06-24; Codex (GR)
2026-06-27.

| Axiom | File | Rating | Sources | Notes |
|-------|------|--------|---------|-------|
| `periodRigidityAxiom` | PeriodLayer.lean | Placeholder | SA | **Consolidated period-level (Picard–Fuchs / Gauss–Manin) math axiom**: the SW period geometry exists (`PeriodRigidity N Λ`). The single math input the general headline (`sw_effective_theory_unique_up_to_duality`, `sw_curve_admits_effective_theory`) rests on. **Discharge in progress** (`audit/PERIOD_LAYER_DISCHARGE.md`): the genus-1 analytic engine is built (SW period `a=∮λ_SW` + holomorphy + the special-geometry relation `∂a/∂u=½∮dx/y`, R1–R2b, all standard-3 / std-3+`AX_PeriodCycleBasis`, **no new axioms**). Remaining: R2c closed-cycle periods → `PeriodChart`/H1 → H2/H3/H6 → rigidity → assemble (multi-week). The `PeriodRigidity` structure was GR/Codex-vetted (connectedness, trace-free `SU(N)` slice, `N≥2`). |
| `matterPeriodRigidityAxiom (DISCHARGED 2026-07-06)` | SU2Matter.lean | Likely correct | GR, CR | **Matter analogue of `periodRigidityAxiom`** (`SU(2)` SQCD, range `1 ≤ N_f ≤ 3`, `Λ ≠ 0`): a matter SW theory exists (`IsMatterPolarizedPeriodChart` = special geometry + `Δ` = the curve's discriminant locus) with its singular-fiber dictionary (`MatterPeriodRigidityData` — at each `A₂` cusp, two vanishing cycles of intersection `±1` with vanishing periods), giving `NonLocalDegenerationLocus ≠ ∅`. **Vetted by Gemini 3.1 Pro + Codex (2026-06-28)**: honest Gauss–Manin / Picard–Lefschetz debt (does not smuggle the cusp — that is `ring`-proved); soundness guards `N_f ≤ 3` (genus-1; Nat-sub `4−N_f` truncates) and `Λ ≠ 0` added; `IsMatterPolarizedPeriodChart` under-constrained (H2/H5/H6 deferred → it is *a* theory with the matter discriminant, not yet *the unique* SQCD theory). NB `MatterPeriodRigidityData` is a *hypothesis*, not a global axiom — `argyresDouglasLocus_nonempty_of_matterPeriodLayer` is standard-3. Discharged with the period geometry (`SU2_MATTER_PLAN.md` (archived, local `history/audit/`)). **Role narrowed (2026-07-05, MC-route):** the *rigidity/uniqueness* content is now the theorem `matter_coupling_rigidity` (θ pair + covering pair only); this axiom's remaining irreducible role is **existence** of the matter period chart (the `realize` debt, same species as `periodRigidityAxiom` — future work with higher genus). |
| `AX_developing_map_rigidity` | SU2Rigidity.lean | Placeholder | SA, LP | **Classical-math axiom (lift uniqueness)**: given the `Γ(2)` covering, two same-monodromy developing maps agree up to a modular frame change. Consumes `AX_thrice_punctured_uniformization`; replaces the retired bespoke `AX_su2_modular_frame_alignment`. Forster (monodromy thm); SW1 §3–4 **v2 (2026-07-05, MC3 review Q3):** generalized to a generic λ-base (`λ∘f = λ∘g`), analyticity/ℍ-valuedness now explicit hypotheses; the SW-specialized form is derived at `su2_frame_alignment`; footprints unchanged; scrutiny record in the axiom docstring. |
| `localMonodromy`, `AX_picard_lefschetz_local` | Monodromy.lean | Placeholder | SA, LP | **Monodromy gap**: local monodromy of the family = Picard–Lefschetz transvection; needs family/local-system layer. SW1 §3 |
| `AX_thrice_punctured_uniformization` | ModularLambda.lean | Placeholder | LP | **Classical analytic input**: modular `λ` realizes `ℍ` as universal cover of `ℂ∖{0,1}` (`Γ(2)` deck group); now realized by the concrete `modularLambdaFn`, and consumed by `sw_su2_unique` via `su2_frame_alignment` |
| `AX_jacobi_quartic` (`θ₃⁴=θ₂⁴+θ₄⁴`) | ThetaLambda.lean | Likely correct | LP, CAS | Jacobi's quartic identity. **CAS-verified** (`audit/theta_identities_cas_check.py`): exact integer `q`-series identity to order 200 (`θ₃⁴` coeffs = `r₄(n)`, the four-square counts), numeric error `2.7e-14`. Lean proof = Sturm bound on `M₂(Γ(2))` (bound 1 ⇒ ~2 coeffs); needs the modular-forms dimension/Sturm infra (ModularForms roadmap) |
| `AX_theta3_ne_zero` (`θ₃≠0` on `ℍ`) | ThetaLambda.lean | Likely correct | LP, CAS | Standard theta non-vanishing. **CAS-checked** non-vanishing on an `ℍ`-grid (`audit/theta_identities_cas_check.py`). Lean proof = Jacobi triple product (all factors `≠0`, `|q|<1`) or the form's divisor; not a symbolic-algebra check |
| ~~`periodRatio_logDeriv_asymptotic`~~ | BetaFunction.lean | **DISCHARGED 2026-07-05** | — | **Axiom deleted — with a fidelity finding.** The statement was purely existential (`∃ F` entire with `s·F′(s) → (4−Nf)/(2πi)`), never formally tied to the curve's periods, so it is *provable* with the explicit `Ein`-type witness `F₀(z) = ∫₀¹(1−e^{−tz})/t dt` (entire by differentiation under the integral; `s·F₀′(s) = 1−e^{−s} → 1`). `betaFunction_weakCoupling` (E10) is now axiom-free, but its physics content is correspondingly existential; the faithful strengthening — the asymptotic for the *actual* ratio `i·K(1−m)/K(m)` — is the R4 target, now within reach of the proved Legendre/cusp layer. Third outright deletion. |
| `AX_elliptic_inversion` (C1) | EllipticIntegrals.lean | Likely correct | LP, GR, CAS | **C-route milestone C0** (`GENUS1_PERIODS_PLAN.md` (archived, local `history/audit/`)): Jacobi inversion / θ-bridge (WW §§21–22), v2 with explicit `K ≠ 0`. Vetted: GR adversarial review 2026-07-04 (v1 NO-GO → corrections incorporated) + numeric 84/84 at dps=40 (witness formula in all four quadrants). **Consumed (2026-07-04)** by the coupling-level closure: `su2_coupling_exists` (std-3 + this axiom alone) and `su2_coupling_canonical` (+ the covering pair) — the SU(2) coupling exists and is unique up to `Γ(2)`, classical axioms only. |
| ~~`AX_legendre_relation` (C2)~~ | EllipticIntegrals.lean | **DISCHARGED 2026-07-04** | — | **Axiom deleted.** Now the theorem `legendre_relation` — **standard-3 only** since 2026-07-05 (its last input, C3, was discharged too): the two proved Legendre ODEs + constancy on the star-shaped domain + the cusp limit. The discharge loop's first outright axiom deletion. |
| ~~`AX_elliptic_cusp_limits` (C3)~~ | EllipticIntegrals.lean | **DISCHARGED 2026-07-05** | — | **Axiom deleted.** Now the theorem `elliptic_cusp_limit` (standard-3): the `K′` log cusp asymptotic on the positive-real ray, by the model-comparison route (realization as a real integral; the elementary `arcsinh` model carries the whole log divergence; constant-`π²`-dominated convergence to `∫(1/sinφ−1/φ) = log(4/π)`; `log(4/π)+logπ = 2log2`). Second outright axiom deletion; makes `legendre_relation` axiom-free. |
| ~~`AX_tau_cusp_zero`~~ (C4) | EllipticIntegrals.lean | **DEMOTED 2026-07-05** | LP, GR, CAS | **Axiom deleted — zero consumers.** The golden trace listed it on no theorem's footprint; an unconsumed axiom is trusted-base pollution. The statement survives unasserted as `def TauCuspLabelZero : Prop` (the cusp-label spec for H3's explicit monodromies, both cusp jumps numerically checked); a future consumer must prove it or reintroduce a tracked axiom. Fourth trusted-base deletion of the loop. |

## Discharge map — every math axiom's documented route

| Axiom(s) | Route | Plan document | Effort |
|---|---|---|---|
| `AX_jacobi_quartic`, `AX_theta3_ne_zero` | Jacobi triple product for `jacobiTheta₂` (or Sturm bound on `M₂(Γ(2))`) | [`audit/PROOF_STATUS.md`](audit/PROOF_STATUS.md) §B | days–weeks; self-contained Mathlib upstream |
| `AX_thrice_punctured_uniformization`, `AX_developing_map_rigidity` | fundamental domain + **Schwarz reflection** ⇒ the `Γ(2)` covering; lift uniqueness from covering-space theory | [`COVERING_SCOPING.md` (archived, local `history/audit/`)](COVERING_SCOPING.md, archived in local history/), [`SCHWARZ_REFLECTION_SCOPING.md` (archived, local `history/audit/`)](SCHWARZ_REFLECTION_SCOPING.md, archived in local history/) | the hardest cluster; scoped as upstream contributions |
| `periodRigidityAxiom` (rank 1) | **first**: the classical-axiomatization C-route — replace the coarse axiom by classical elliptic-integral axioms C1–C3 (Jacobi inversion, Legendre relation, `K` asymptotics) + the existing θ/covering clusters, `SameSWMonodromy` demoted to a definition; **then**: explicit elliptic periods on pure Mathlib (G0–G7) discharge C1–C3 (analytic engine R1–R2b is **built**) | [`GENUS1_PERIODS_PLAN.md` (archived, local `history/audit/`)](GENUS1_PERIODS_PLAN.md, archived in local history/) (C-route §revision), [`audit/PERIOD_LAYER_DISCHARGE.md`](audit/PERIOD_LAYER_DISCHARGE.md) | C-route: ~1–2 weeks gluing; G-route: weeks (R2c the lift) |
| `periodRigidityAxiom` (general `N`), `localMonodromy`, `AX_picard_lefschetz_local`, inherited `AX_PeriodCycleBasis` (`SameSWMonodromy`: already demoted to a def) | the SW-agnostic weight-1 VHS library (`riemann-periods`, L0–L6) | [`audit/RIEMANN_PERIODS_SCOPE.md`](audit/RIEMANN_PERIODS_SCOPE.md) | Stage 1 (genus 1) weeks; Stage 2 (general genus) Mathlib-scale |
| `matterPeriodRigidityAxiom (DISCHARGED 2026-07-06)` | matter extension of the genus-1 period layer (M6) | [`SU2_MATTER_PLAN.md` (archived, local `history/audit/`)](SU2_MATTER_PLAN.md, archived in local history/) | deferred with the period layer |
| `periodRatio_logDeriv_asymptotic` | weak-coupling asymptotics of the explicit periods (the H6/R4 work) | [`GENUS1_PERIODS_PLAN.md` (archived, local `history/audit/`)](GENUS1_PERIODS_PLAN.md, archived in local history/) | with R4/H6 |

Sequencing: the triple product is the cheap independent win; the genus-1 period build is the
reachable medium-term target (`SameSWMonodromy`'s definition: **done**); the covering/Schwarz
cluster is the hard classical-analysis debt; the `riemann-periods` library closes everything at
all ranks.

**Resolved — H5 `HasFiniteOrderAutomorphism` redefined (2026-06-30).** The earlier "order **exactly** `2N`" clause was unsatisfiable on the *moduli* for SU(2) (the anomaly-free `ℤ_{2N}` on `φ` descends to order `N` on `u ~ φ²`; the faithful `2N`-action lives on the `φ`-cover). Now redefined faithfully: a **nontrivial `ℂ`-linear automorphism of order dividing `2N`** fixing `Δ` (`ℂ`-linearity rules out set-theoretic junk; `ω ≠ id` rules out the identity). **Non-vacuity is proved** — `hasFiniteOrderAutomorphism_of_neg_invariant` (standard-3) exhibits the physical reflection `u → −u` as a witness on any reflection-symmetric base. No global axiom affected.

**Phase 1b (SU(2) rigidity).** `SeibergWitten/Physics/SU2Rigidity.lean` proves the rank-1
case of `sw_effective_theory_unique_up_to_duality` as a *theorem* (`sw_su2_unique`) modulo
two **classical-math** axioms — the `Γ(2)` covering
`AX_thrice_punctured_uniformization` and the lift-uniqueness `AX_developing_map_rigidity`
(combined in the derived `su2_frame_alignment`). **Resolved — `SameSWMonodromy` demoted
(2026-07-04):** the former uninterpreted physics axiom is now a *definition* (both
couplings develop the numerically pinned modulus `swCrossRatio Λ u = 2Λ²/(u+Λ²)`;
`audit/numerical/validate_swcrossratio.py`), so `sw_su2_unique`'s kernel footprint is
standard-3 + the two classical axioms — **no physics axiom**. The analytic propagation
core `holo_eqOn_of_germ` (the identity theorem) is **proved, standard-3**. Discharging the
covering upstream (Schwarz reflection ⇒ Riemann mapping ⇒ the `Γ(2)` cover) and the
lift-uniqueness step removes the remaining math debt.

All of `PeriodBase`, `PeriodChart`, the H1–H6 predicates above, `periodCombination`, `intersectionForm`,
`NonLocalDegenerationLocus`, and `IsPolarizedPeriodChart` are *definitions/structures* (not axioms) — in
particular Argyres–Douglas points are a *derived* notion (coalescence of mutually-non-local
vanishing cycles), not a physical input. Per-result axiom sets are tracked by `#print axioms`.
