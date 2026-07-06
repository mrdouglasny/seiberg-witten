# Proof status — toward axiom-free SU(2) Seiberg–Witten

*Snapshot of how far `sw_su2_unique` (the rank-1 rigidity headline) is from being
axiom-free, what is proved, and exactly what each remaining gap needs. Companion to
[`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md). Last updated 2026-07-05.*

## The goal — and where it stands

The original goal — demote `sw_effective_theory_unique_up_to_duality` from a
codified-physics axiom to a **theorem** — is **done**, at all ranks: the headline
existence and uniqueness statements are proved (no `sorry`), carrying the physics
H0–H6 as *hypotheses* in their types and resting on the single consolidated math
axiom `periodRigidityAxiom` (`#print axioms` = standard-3 + `periodRigidityAxiom`;
golden trace in [`axiom-report.txt`](axiom-report.txt)). The rank-1 case
`sw_su2_unique` rests on the finer footprint: two classical-math axioms plus the
physics input `SameSWMonodromy`. The remaining goal tracked here is **discharging
the mathematical axioms** — making the rank-1 route axiom-free and constructing the
period layer behind `periodRigidityAxiom`.

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
| `modularLambda_add_two`, `modularLambda_S`, `modularLambda_ST2S` | ThetaLambda | `λ` invariant under **both** generators of `Γ(2) = ⟨T², ST²S⁻¹⟩`; `S: λ ↦ 1−λ` (`_add_two` standard-3; `_S`/`_ST2S` **modulo the θ pair** via `oneMinusLambda` — now visible in the golden trace) |
| `ellipticKm_hasDerivAt`, `ellipticEm_hasDerivAt` | EllipticIntegrals | the full first-order **Legendre ODE system** for `K`, `E` on the cut plane |
| `legendre_relation` | EllipticIntegrals | `E·K′+E′·K−K·K′ = π/2` — **axioms C2 AND C3 deleted; axiom-free** |
| `swAD_tendsto_zero_monopole` | SU2Rigidity | H2 at the monopole: `a_D → 0` within the chart (**axiom-free**) |
| `swA_hasDerivAt`, `swAD_hasDerivAt` | SU2Rigidity | closed-form `da/du`, `da_D/du` on the chart (**axiom-free**) |
| `swAD_deriv_eq_swTau_mul_swA_deriv` | SU2Rigidity | **S1: `da_D/da = τ`** — special geometry (H1) for the explicit solution (modulo C1's `K≠0`) |
| `elliptic_cusp_limit` | EllipticIntegrals | `K(1−x) + ½log x → 2log2` — **axiom C3 deleted**, proved by model comparison (**axiom-free**) |
| `tau_ratio_hasDerivAt`, `swTau_hasDerivAt` | EllipticIntegrals, SU2Rigidity | the **Wronskian formula** `dτ/dm = −iπ/(4m(1−m)K²)` and `dτ/du` closed form (modulo C1's `K≠0`) |
| `swTau_logDeriv_weakCoupling`, `swA_weakCoupling` | SU2Rigidity | **faithful one-loop running** `u·τ′ → i/π`; `a/√(u+Λ²) → 1/√2` (H6 shapes) |
| `periodRatio_logDeriv_asymptotic` | BetaFunction | **third axiom deleted** — existential log-running, explicit `Ein` witness (**axiom-free**, D3 finding) |
| `modularLambda_add_one` | ThetaLambda | the **T-law** `λ(τ+1) = λ/(λ−1)` (modulo the θ pair) — completes the anharmonic `S₃` from proved λ-laws |
| `multipliable_tripleProductTerm`, `tripleProduct_quasi_periodic`, `jacobiTripleProduct_ne_zero`, `differentiable_jacobiTripleProduct_exp` | ThetaProduct | triple-product bricks T0/T1/T3a + entirety in `z` (**axiom-free**) — head start for upstreaming |
| `matter_nf1_ad_invariants`, `quarticG2/G3_of_triple_root` | MatterInvariants | the AD point as `g₂ = g₃ = 0`; triple root ⇒ invariants vanish (**axiom-free**, two routes) |
| `matter_coupling_rigidity` | MatterInvariants | **matter coupling uniqueness** up to `Γ(2)` × an anharmonic word (**modulo the θ pair + covering pair — no matter axiom**) |
| `matterPeriodRigidity_nf1_ad`, `monic_quartic_squarefree_iff_disc`, `matter_argyresDouglasLocus_nonempty` | MatterChart | **matterPeriodRigidityAxiom DISCHARGED** (first constructed `PeriodChart`; exact disc factorization `−Λ⁶(u−3Λ²/4)²(u+15Λ²/16)`; unique cusp; disclosed non-SQCD witness — the predicate's weakness made formal; M6 now **axiom-free**) |
| `swModulusData_of_atlas_and_lifts`, `cusp_dichotomy`, `modularLambda_swMonodromyGroup` | CuspData | **the cusp data derived**: H4-atlas + per-puncture genuine cusp lifts (H2/H3 + H6-qual) ⇒ all of `SWModulusData` — dichotomy via `Periodic.cuspFunction` removability, no Picard; monodromy group ≤ Γ(2) with full λ-invariance (θ-pair footprint; dichotomy itself **axiom-free**) |
| `swModulusData_eq_crossRatio`, `entire_polynomial_of_growth` | DevelopingBase | **the developing base derived**: qualitative cusp data (3 limits + 2 omitted values) ⇒ the pinned formula `λ(τ) = 2Λ²/(u+Λ²)`, degree/rates/normalization all conclusions (**axiom-free**); decomposed headline `sw_su2_unique_of_modulusData` = covering pair only |
| `singularity_count_pinch`, `sw_exactly_two_singularities'`, `count_mod_twelve` | SingularityCount | **why exactly one monopole–dyon pair**: Euler/mod-12 counting (alone: `n ≡ 1 mod 6`, K3 loophole real) + homogeneity pinch ⇒ `n = 1` (**axiom-free**; both curve frames instantiated, `I₄*`+2`I₁` and `I₂*`+2`I₂`, Euler 12) |

So `λ` is a proved `Γ(2)`-Hauptmodul (invariance clause), the SU(2) base is identified with
`ℂ∖{0,1}`, the rank-1 Sp-action exists, and the analytic-propagation core is proved.

## Remaining axioms, classified

### A. Physics-foundations (deliberate — *not* to be discharged)

After the strengthening refactor the physical inputs **H0–H6 are predicates, not
axioms** (`PeriodBase`, `PeriodChart`, `SpecialGeometry`, `PeriodsDegenerateOnBoundary`,
`PicardLefschetzAtGenericStratum`, `SymplecticReframing`, `HasFiniteOrderAutomorphism`,
`HasPrescribedAsymptotics`, bundled in `IsPolarizedPeriodChart`) — they live in the
theorems' hypotheses, not the trusted base. The old opaque physics axioms
(`SpecialGeometry`, `EMDualityConsistent`, `SmoothCover`, …) are **retired**, and
`SameSWMonodromy` was **demoted from axiom to definition** (2026-07-04: both couplings
develop the curve's pinned modulus `swCrossRatio`; C-route). **No deliberate physics
axiom remains**; the physics lives entirely in hypotheses.

### B. Mathlib-scale analytic gaps (these block axiom-free `sw_su2_unique`)

| Gap (axiom) | Discharged by | What that needs |
|---|---|---|
| `AX_jacobi_quartic` (`θ₃⁴=θ₂⁴+θ₄⁴`), `AX_theta3_ne_zero` (`θ₃≠0`) | the **Jacobi triple product** for `jacobiTheta₂` | a product expansion `θ = ∏(1−q²ⁿ)(1+q^{2n−1}z)(1+q^{2n−1}/z)`; **absent from Mathlib**. Gives the quartic identity and non-vanishing as corollaries. |
| `AX_thrice_punctured_uniformization` (surjectivity + fibres = `Γ(2)`-orbits), `AX_developing_map_rigidity` (lift uniqueness) | the **modular `λ` covering** `ℍ/Γ(2) ≅ ℂ∖{0,1}` + covering-space theory | Schwarz reflection (or Riemann mapping) + `Γ(2)` fundamental domain + generators + covering-Galois — a *cluster* of absent machinery; **the hardest of the three gaps**. Invariance clause already proved; full decomposition + Mathlib map in `COVERING_SCOPING.md` (archived, local `history/audit/`). |
| `periodRigidityAxiom`, `matterPeriodRigidityAxiom`, `AX_picard_lefschetz_local`, `localMonodromy` (`SameSWMonodromy`: demoted to a def 2026-07-04) | the **family / Gauss–Manin VHS layer** over `U = moduli ∖ Δ` | `R¹π_*ℤ` as a local system, the flat Gauss–Manin connection, monodromy representation; **absent from Mathlib and jacobian-challenge**. The spec is `WeightOneVHS` (`VHS.lean`); genus-1 discharge plan in [`PERIOD_LAYER_DISCHARGE.md`](PERIOD_LAYER_DISCHARGE.md). |

### C. The C-route elliptic axioms (rank-1)

`AX_elliptic_inversion` (C1) — alone — backs the explicit coupling/coordinate
layer. `AX_tau_cusp_zero` (C4) was **demoted to the unasserted spec
`TauCuspLabelZero`** (2026-07-05: zero consumers in the golden trace).
**Both cusp-analysis axioms are deleted:**
`AX_legendre_relation` (C2) is the theorem `legendre_relation` and
`AX_elliptic_cusp_limits` (C3) is the theorem `elliptic_cusp_limit` — and since C2's
only remaining input was C3, `legendre_relation` is now **standard-3, axiom-free**.
Discharge log: `GENUS1_PERIODS_PLAN.md` (archived, local `history/audit/`).

## Conclusion

The discharge loop (2026-07-04) breached the earlier "chipping exhausted" assessment:
the Legendre ODE system, the Legendre relation (C2 — axiom deleted), the monopole H2
limit, and the full special-coordinate calculus including `da_D/da = τ` (S1) are now
theorems. What remains beyond bounded edits: C1/C4
(nome/covering theory; C3's log clause fell 2026-07-05 to the model-comparison
route), plus the three residual gaps in (B). The latter are each
standalone Mathlib-scale developments (the triple product is the smallest and
most self-contained, and a natural upstream contribution; the genus-1 period engine of the
Gauss–Manin row is partially built — see `PERIOD_LAYER_DISCHARGE.md`). Closing the first
two makes `sw_su2_unique` fully **axiom-free** (its physics is already a defined
hypothesis, not an axiom); closing the third discharges `periodRigidityAxiom` and, with
it, the general-rank headline.
