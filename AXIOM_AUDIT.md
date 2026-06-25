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

## Physics foundations — codified lore (`Physics/Hypotheses.lean`)

These axiomatize the four-plus physical inputs that single out the SW curve. All are
`(NOT VERIFIED)` skeleton placeholders pending the later-phase machinery that makes them
precise; the headline lore axioms are the residual physical trust. Reviewed by Gemini
(GR) 2026-06-24 — the cover/Liouville, Picard–Lefschetz, and R-symmetry items are from
that review.

| Axiom | File:Line | Rating | Sources | Notes |
|-------|-----------|--------|---------|-------|
| `SmoothCover`, `SmoothCover.proj` | Hypotheses.lean | Placeholder | GR | Carrier: univ. cover of `ℂ^r∖Δ` (fixes Liouville triviality of global `τ`) |
| `SpecialGeometry` | Hypotheses.lean | Placeholder | GR, LP | H1 holomorphy: `a_D=∂F/∂a`, `τ=∂²F/∂a²`, 1-loop exact. SW1 §2 |
| `BecomesMasslessAt` | Hypotheses.lean | Placeholder | GR | `Z→0` limit at `Δ` (H2 building block) |
| `PicardLefschetzAtGenericSingularities` | Hypotheses.lean | Placeholder | GR, LP | H3 monodromy class `v↦v+⟨v,nₐ⟩nₐ` on the *generic* stratum of `Δ`. SW1 §3 |
| `EMDualityConsistent` | Hypotheses.lean | Placeholder | GR, LP | H4 `Sp(2r,ℤ)` monodromy. SW1 §3–4 |
| `RSymmetryConsistent` | Hypotheses.lean | Placeholder | GR, LP | H5 `U(1)_R→ℤ_{2N}` fixes `Δ` positions. SW1 §4 |
| `AsymptoticMatch` | Hypotheses.lean | Placeholder | GR, LP | H6 1-loop+instanton ≍ periods. SW1 §2,4 |
| `DualityEquiv` | Hypotheses.lean | Placeholder | GR | `Sp(2r,ℤ)` frame-change equivalence |
| `sw_effective_theory_unique_up_to_duality` | Hypotheses.lean | Needs review | GR, LP | **Headline lore**: hypotheses fix solution up to `Sp(2r,ℤ)`. SW1 |
| `sw_curve_admits_effective_theory` | Hypotheses.lean | Needs review | GR, LP | **Headline lore**: SW curve realizes such a theory. SW1 |
| `SameSWMonodromy` | SU2Rigidity.lean | Placeholder | SA | Same `Sp(2,ℤ)` monodromy of two SU(2) period maps; until monodromy layer (Phase 3/4) |
| `AX_developing_map_rigidity` | SU2Rigidity.lean | Placeholder | SA, LP | **Classical-math axiom (lift uniqueness)**: given the `Γ(2)` covering, two same-monodromy developing maps agree up to a modular frame change. Consumes `AX_thrice_punctured_uniformization`; replaces the retired bespoke `AX_su2_modular_frame_alignment`. Forster (monodromy thm); SW1 §3–4 |
| `localMonodromy`, `AX_picard_lefschetz_local` | Monodromy.lean | Placeholder | SA, LP | **Monodromy gap**: local monodromy of the family = Picard–Lefschetz transvection; needs family/local-system layer. SW1 §3 |
| `AX_thrice_punctured_uniformization` | ModularLambda.lean | Placeholder | LP | **Classical analytic input**: modular `λ` realizes `ℍ` as universal cover of `ℂ∖{0,1}` (`Γ(2)` deck group); now realized by the concrete `modularLambdaFn`, and consumed by `sw_su2_unique` via `su2_frame_alignment` |
| `AX_jacobi_quartic` (`θ₃⁴=θ₂⁴+θ₄⁴`) | ThetaLambda.lean | Placeholder | LP | Jacobi's quartic identity — concrete theta-series computation; bounded target |
| `AX_theta3_ne_zero` (`θ₃≠0` on `ℍ`) | ThetaLambda.lean | Placeholder | LP | standard theta non-vanishing |

**Phase 1b (SU(2) rigidity).** `SeibergWitten/Physics/SU2Rigidity.lean` proves the rank-1
case of `sw_effective_theory_unique_up_to_duality` as a *theorem* (`sw_su2_unique`) modulo
two clearly-separated tiers: two **classical-math** axioms — the `Γ(2)` covering
`AX_thrice_punctured_uniformization` and the lift-uniqueness `AX_developing_map_rigidity`
(combined in the derived `su2_frame_alignment`) — and the **physics** input
`SameSWMonodromy`. The analytic propagation core `holo_eqOn_of_germ` (the identity theorem)
is **proved, standard-3**, and no bespoke placeholder remains. Discharging the covering
upstream (Schwarz reflection ⇒ Riemann mapping ⇒ the `Γ(2)` cover) and the lift-uniqueness
step removes the math debt; the physics axiom `SameSWMonodromy` is irreducible.

`SingularitiesAreBPS`, `diracPairing`, `ArgyresDouglasLocus`, and `IsSWEffectiveTheory`
are *definitions/structures* (not axioms) — in particular Argyres–Douglas points are a
*derived* notion (coalescence of mutually-non-local vanishing cycles), not a physical
input. Per-result axiom sets are tracked in `formalization.yaml › main_results` and
verified by `#print axioms`.
