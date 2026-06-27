# Axiom audit — seiberg-witten

*Last updated 2026-06-24.*

Format + conventions:
[`math-commons/formalization-assurance/AXIOM_AUDIT_FORMAT.md`](https://github.com/math-commons/formalization-assurance/blob/main/AXIOM_AUDIT_FORMAT.md).
This is a **forward-chaining** project (formalizing the SW corpus on top of
`jacobian-challenge`); the primary assurance artifact is the
[correspondence index](audit/CORRESPONDENCE_INDEX.md), not the axiom audit.

The **rigorous spine** (Phases 0–2) declares **no axioms of its own** — it proves
implications `A,B,C ⇒ X,Y,Z` from `jacobian-challenge`. Separately, the **physics
foundations** layer (`SeibergWitten/Physics/Hypotheses.lean`) *deliberately* introduces
named axioms codifying the non-rigorous physical lore the SW solution rests on, so the
residual trust is localized and machine-checkable (see
[`docs/foundations-for-physical-reasoning.md`](docs/foundations-for-physical-reasoning.md)).
These are **not** debt to be discharged — they are the codified hypotheses themselves.

## Rigorous spine (own axioms: 0)

| Result | Phase | `#print axioms` |
|---|---|---|
| `genus_swCurve`, `genus_swCurve_su2` | 0 | **standard-3** |
| `sw_coupling_mem_siegel*`, `sw_metric_posDef` | 1a | standard-3 + `Jacobians.Axioms.AX_PeriodCycleBasis` |
| `su2_singular_locus` (curve singular ⟺ `u=±Λ²`), `su2_squarefree_of_ne`, `holo_eqOn_of_germ` | 1b | **standard-3** |
| `transvection_isSymplectic` (Picard–Lefschetz monodromy ∈ Sp), `diracPairing_*` bilinearity | 3 | **standard-3** |
| `symplecticMonoid` (Sp(2r,ℤ) as a submonoid), `SWVariation` spec + coherence lemmas | 3 | **standard-3** (no new axioms) |
| `WeightOneVHS` (base-agnostic weight-1 VHS spec), `SWVariation.toVHS` (SW is an instance) | 3 | **standard-3** (no new axioms) |
| `siegelOneEquiv` (`Siegel 1 ≃ ℍ`), `MulAction SL(2,ℤ) (Siegel 1)`, `siegelOneEquiv_smul` (g=1 Sp-action) | 3 | **standard-3** (no new axioms; built on Mathlib `ℍ` action) |
| `duality_preserves_metric_posDef`, `siegelOne_smul_im_pos`, `metric_posDef_of_h4'` (H4′: EM duality ⇒ special-Kähler positivity is duality-stable) | 3 | **standard-3** (the `H4'`-consequence also transits the `SmoothCover` carrier) |
| `su2DualityMap`, `su2_deck_of_periodFrame` (Step C of SU(2) uniqueness: SL(2,ℤ) period frame ⇒ duality `Deck`, with symplectic + covariant from det 1) | 1b | **standard-3** (no axioms) |
| `PeriodLayer`/`SWPeriodLayer` (period-level debt as a *structure*) + `sw_su2_unique_of_periodLayer`, `sw_su2_exists_of_periodLayer`, `sw_unique_of_swPeriodLayer`, `sw_exists_of_swPeriodLayer`, `PeriodLayer.toGeneral` (SU(2)/SU(N) B.1 goals proved *modulo* the layer) | — | **standard-3** (period-level debt is a hypothesis, not an axiom; vetted GR — connectedness, trace-free SU(N) slice, `N≥2` guard) |
| `su2BaseEquiv` (SU(2) base `ℂ∖{±Λ²} ≃ ℂ∖{0,1}`), `affineEquiv` | 1b | **standard-3** (no new axioms) |
| `theta3_eq_jacobiTheta`, `theta3_add_two`, `theta4_add_two`, `modularLambdaFn` def, `oneMinusLambda` | 1b | **standard-3** + `AX_jacobi_quartic`, `AX_theta3_ne_zero` (`oneMinusLambda` only) |
| `modularLambda_add_two` (`λ(τ+2)=λ(τ)`, i.e. `T²∈Γ(2)`-invariance), `theta2_pow_four`, `theta2_add_two_pow_four` | 1b | **standard-3** (proved dent in `AX_thrice_punctured_uniformization`'s Γ(2)-invariance) |
| `theta3_neg_inv`, `theta2_neg_inv` (θ₃, θ₂ modular S-laws `θ(-1/τ)=(-iτ)^½·θ`) | 1b | **standard-3** (both proved from Mathlib's `jacobiTheta₂_functional_equation`) |
| `modularLambda_S` (`λ(-1/τ)=1-λ(τ)`, the S-transformation) | 1b | standard-3 + `AX_jacobi_quartic`, `AX_theta3_ne_zero` |
| `modularLambda_ST2S` (invariance under 2nd `Γ(2)` generator `ST²S⁻¹`) | 1b | standard-3 + `AX_jacobi_quartic`, `AX_theta3_ne_zero` (no new axioms; with `_add_two` → full `Γ(2)`-invariance) |

Phase 0 (genus) is standard-3. Phase 1a (special geometry / metric positivity) transits
the inherited `AX_PeriodCycleBasis` — jacobian-challenge's hyperelliptic cycle-basis
axiom, **off the Buzzard critical path**. The axiom-free SU(2) route (Phase 1b) would
remove it for genus 1.

## Physics foundations — hypotheses (`Physics/Hypotheses.lean`)

After the strengthening refactor, the physical inputs **H0–H6 are no longer axioms**: they are
*contentful predicates and structures* — `CoulombBase`, `Sheet`, `Sheet.SpecialGeometry` (H1),
`Sheet.SingularitiesAreBPS`/`BecomesMasslessAt` (H2), `PicardLefschetzAtGenericStratum` (H3),
`Deck` (H4), `RSymmetry` (H5), `Sheet.MatchesAsymptotics`/`Instantonic` (H6) — bundled in
`IsSWEffectiveTheory` and **assumed as hypotheses** of the headline theorems, so they never enter
the trusted base. The headline implications `sw_effective_theory_unique_up_to_duality`,
`sw_unique_up_to_duality`, and `sw_curve_admits_effective_theory` (`Physics/PeriodLayer.lean`) are
now **proved theorems — no `sorry`** — resting on the physics postulates plus the single
period-level math axiom `swPeriodLayer` (`#print axioms` = **standard-3 + `swPeriodLayer`**). The
rank-1 uniqueness `SU2.sw_su2_unique` rests instead on the finer `B.2` covering/lift axioms +
`SameSWMonodromy`. `coulombBranchDim` (`dim ℂ^{N-1} = N−1`) is **proved**. The old opaque physics
axioms (`SpecialGeometry`, `EMDualityConsistent`, `SmoothCover`, …) are **retired**.

So the only remaining axioms are **mathematical**, not physical — the consolidated period axiom
`swPeriodLayer`, and the finer monodromy / modular / covering inputs below (the genus-1 pieces of
that period geometry, used by the rank-1 route). Reviewed by Gemini (GR) 2026-06-24; Codex (GR)
2026-06-27.

| Axiom | File | Rating | Sources | Notes |
|-------|------|--------|---------|-------|
| `swPeriodLayer` | PeriodLayer.lean | Placeholder | SA | **Consolidated period-level (Picard–Fuchs / Gauss–Manin) math axiom**: the SW period geometry exists (`SWPeriodLayer N Λ`). The single math input the general headline (`sw_effective_theory_unique_up_to_duality`, `sw_curve_admits_effective_theory`) rests on. Discharged when the period geometry is built (`audit/PERIOD_LAYER_SCOPING.md`; future `riemann-periods`). The `SWPeriodLayer` structure was GR/Codex-vetted (connectedness, trace-free `SU(N)` slice, `N≥2`). |
| `SameSWMonodromy` | SU2Rigidity.lean | Placeholder | SA | Same `Sp(2,ℤ)` monodromy of two SU(2) period maps; until monodromy layer (Phase 3/4) |
| `AX_developing_map_rigidity` | SU2Rigidity.lean | Placeholder | SA, LP | **Classical-math axiom (lift uniqueness)**: given the `Γ(2)` covering, two same-monodromy developing maps agree up to a modular frame change. Consumes `AX_thrice_punctured_uniformization`; replaces the retired bespoke `AX_su2_modular_frame_alignment`. Forster (monodromy thm); SW1 §3–4 |
| `localMonodromy`, `AX_picard_lefschetz_local` | Monodromy.lean | Placeholder | SA, LP | **Monodromy gap**: local monodromy of the family = Picard–Lefschetz transvection; needs family/local-system layer. SW1 §3 |
| `AX_thrice_punctured_uniformization` | ModularLambda.lean | Placeholder | LP | **Classical analytic input**: modular `λ` realizes `ℍ` as universal cover of `ℂ∖{0,1}` (`Γ(2)` deck group); now realized by the concrete `modularLambdaFn`, and consumed by `sw_su2_unique` via `su2_frame_alignment` |
| `AX_jacobi_quartic` (`θ₃⁴=θ₂⁴+θ₄⁴`) | ThetaLambda.lean | Likely correct | LP, CAS | Jacobi's quartic identity. **CAS-verified** (`audit/theta_identities_cas_check.py`): exact integer `q`-series identity to order 200 (`θ₃⁴` coeffs = `r₄(n)`, the four-square counts), numeric error `2.7e-14`. Lean proof = Sturm bound on `M₂(Γ(2))` (bound 1 ⇒ ~2 coeffs); needs the modular-forms dimension/Sturm infra (ModularForms roadmap) |
| `AX_theta3_ne_zero` (`θ₃≠0` on `ℍ`) | ThetaLambda.lean | Likely correct | LP, CAS | Standard theta non-vanishing. **CAS-checked** non-vanishing on an `ℍ`-grid (`audit/theta_identities_cas_check.py`). Lean proof = Jacobi triple product (all factors `≠0`, `|q|<1`) or the form's divisor; not a symbolic-algebra check |

**Phase 1b (SU(2) rigidity).** `SeibergWitten/Physics/SU2Rigidity.lean` proves the rank-1
case of `sw_effective_theory_unique_up_to_duality` as a *theorem* (`sw_su2_unique`) modulo
two clearly-separated tiers: two **classical-math** axioms — the `Γ(2)` covering
`AX_thrice_punctured_uniformization` and the lift-uniqueness `AX_developing_map_rigidity`
(combined in the derived `su2_frame_alignment`) — and the **physics** input
`SameSWMonodromy`. The analytic propagation core `holo_eqOn_of_germ` (the identity theorem)
is **proved, standard-3**, and no bespoke placeholder remains. Discharging the covering
upstream (Schwarz reflection ⇒ Riemann mapping ⇒ the `Γ(2)` cover) and the lift-uniqueness
step removes the math debt; the physics axiom `SameSWMonodromy` is irreducible.

All of `CoulombBase`, `Sheet`, the H1–H6 predicates above, `centralCharge`, `diracPairing`,
`ArgyresDouglasLocus`, and `IsSWEffectiveTheory` are *definitions/structures* (not axioms) — in
particular Argyres–Douglas points are a *derived* notion (coalescence of mutually-non-local
vanishing cycles), not a physical input. Per-result axiom sets are tracked by `#print axioms`.
