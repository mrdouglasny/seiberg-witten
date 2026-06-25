# Proof status — toward axiom-free SU(2) Seiberg–Witten

*Snapshot of how far `sw_su2_unique` (the rank-1 rigidity headline) is from being
axiom-free, what is proved, and exactly what each remaining gap needs. Companion to
[`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md). Last updated 2026-06-24.*

## The goal

Demote `sw_effective_theory_unique_up_to_duality` (`Physics/Hypotheses.lean`) from a
codified-physics axiom to a **theorem**, for rank 1 (SU(2)): `sw_su2_unique`
(`Physics/SU2Rigidity.lean`). That isolates the physics into genuinely-physical inputs and
makes the *mathematical* bridge (period-map rigidity) proved.

## Proved spine (column 1, `#print axioms` = standard-3 unless noted)

| Result | File | Content |
|---|---|---|
| `genus_swCurve` | Curve | SU(N) curve has genus `N−1` |
| `sw_coupling_mem_siegel*`, `sw_metric_posDef` | SpecialGeometry | `τ ∈ Siegel`, `Im τ ≻ 0` (modulo inherited `AX_PeriodCycleBasis`) |
| `su2_singular_locus`, `su2_squarefree_of_ne` | SU2Singularities | curve singular **iff** `u = ±Λ²` — the exact SU(2) singularity count |
| `holo_eqOn_of_germ` | SU2Rigidity | analytic propagation (identity theorem) — rigidity in a fixed frame |
| `transvection_isSymplectic`, `diracPairing_*` | Monodromy | Picard–Lefschetz transvections preserve the intersection form (∈ `Sp(2r,ℤ)`) |
| `symplecticMonoid`, `WeightOneVHS`, `SWVariation.toVHS` | Family, VHS | the `Sp(2r,ℤ)` target group; weight-1 VHS spec; SW as an instance |
| `siegelOneEquiv`, `MulAction SL(2,ℤ) (Siegel 1)`, `siegelOneEquiv_smul` | SiegelSL2 | the `g=1` Sp-action on Siegel ≅ ℍ (built on Mathlib) |
| `su2BaseEquiv`, `affineEquiv` | ModularLambda | SU(2) base `ℂ∖{±Λ²} ≃ ℂ∖{0,1}` (the thrice-punctured sphere) |
| `modularLambdaFn`, `theta{2,3,4}`, `oneMinusLambda` | ThetaLambda | `λ = θ₂⁴/θ₃⁴` from Mathlib's `jacobiTheta₂`; `1−λ = θ₄⁴/θ₃⁴` |
| `theta3_neg_inv`, `theta2_neg_inv` | ThetaLambda | both θ-null modular **S**-laws, from the functional equation |
| `modularLambda_add_two`, `modularLambda_S`, `modularLambda_ST2S` | ThetaLambda | `λ` invariant under **both** generators of `Γ(2) = ⟨T², ST²S⁻¹⟩`; `S: λ ↦ 1−λ` |

So `λ` is a proved `Γ(2)`-Hauptmodul (invariance clause), the SU(2) base is identified with
`ℂ∖{0,1}`, the rank-1 Sp-action exists, and the analytic-propagation core is proved.

## Remaining axioms, classified

### A. Physics-foundations (deliberate — *not* to be discharged)

`SpecialGeometry`, `PicardLefschetzAtGenericSingularities`, `EMDualityConsistent`,
`RSymmetryConsistent`, `AsymptoticMatch`, `SmoothCover`, `BecomesMasslessAt`, `DualityEquiv`,
`sw_effective_theory_unique_up_to_duality`, `sw_curve_admits_effective_theory`
(`Physics/Hypotheses.lean`). These are the codified physical lore — the point of the
project is to *state* them, not remove them.

### B. Mathlib-scale analytic gaps (these block axiom-free `sw_su2_unique`)

| Gap (axiom) | Discharged by | What that needs |
|---|---|---|
| `AX_jacobi_quartic` (`θ₃⁴=θ₂⁴+θ₄⁴`), `AX_theta3_ne_zero` (`θ₃≠0`) | the **Jacobi triple product** for `jacobiTheta₂` | a product expansion `θ = ∏(1−q²ⁿ)(1+q^{2n−1}z)(1+q^{2n−1}/z)`; **absent from Mathlib**. Gives the quartic identity and non-vanishing as corollaries. |
| `AX_thrice_punctured_uniformization` (surjectivity + fibres = `Γ(2)`-orbits) | the **modular `λ` covering** `ℍ/Γ(2) ≅ ℂ∖{0,1}` | open-mapping + properness of `λ`, or the classical uniformization; **absent from Mathlib**. *Invariance clause already proved* (`modularLambda_add_two` + `_ST2S`), so only surjectivity/fibres remain. |
| `AX_picard_lefschetz_local`, `AX_su2_modular_frame_alignment`, `localMonodromy`, `SameSWMonodromy` | the **family / Gauss–Manin VHS layer** over `U = moduli ∖ Δ` | `R¹π_*ℤ` as a local system, the flat Gauss–Manin connection, monodromy representation; **absent from Mathlib and jacobian-challenge**. The spec is `WeightOneVHS` (`VHS.lean`). |

## Conclusion

Incremental, single-proof chipping is **exhausted**: the proved spine above is everything
reachable from Mathlib + `jacobian-challenge` by bounded edits. The three residual gaps in
(B) are each standalone Mathlib-scale developments (the triple product is the smallest and
most self-contained, and a natural upstream contribution). Closing any one of them is a
project in itself; closing all three makes `sw_su2_unique` axiom-free.
