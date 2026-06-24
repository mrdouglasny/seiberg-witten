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
| `AX_su2_modular_frame_alignment` | SU2Rigidity.lean | Placeholder | SA, LP | **The one SU(2)-rigidity gap**: modular-`λ` uniformization of `ℂ∖{±Λ²}`; not in Mathlib. SW1 §3–4 |
| `localMonodromy`, `AX_picard_lefschetz_local` | Monodromy.lean | Placeholder | SA, LP | **Monodromy gap**: local monodromy of the family = Picard–Lefschetz transvection; needs family/local-system layer. SW1 §3 |

**Phase 1b (SU(2) rigidity).** `SeibergWitten/Physics/SU2Rigidity.lean` reduces the
rank-1 case of `sw_effective_theory_unique_up_to_duality` to a *theorem*
(`sw_su2_unique`) resting on exactly **one** mathematical input,
`AX_su2_modular_frame_alignment` (the modular-`λ` uniformization), plus the monodromy
placeholder `SameSWMonodromy`. The analytic propagation core `holo_eqOn_of_germ` (the
identity theorem) is **proved, standard-3**. Building/porting the `λ`/`Γ(2)`
uniformization discharges the gap and makes `sw_su2_unique` axiom-free.

`SingularitiesAreBPS`, `diracPairing`, `ArgyresDouglasLocus`, and `IsSWEffectiveTheory`
are *definitions/structures* (not axioms) — in particular Argyres–Douglas points are a
*derived* notion (coalescence of mutually-non-local vanishing cycles), not a physical
input. Per-result axiom sets are tracked in `formalization.yaml › main_results` and
verified by `#print axioms`.
