# Correspondence index — SW solution of N=2 SU(N) SYM

Source ↔ Lean map for the Seiberg–Witten corpus (forward-chaining; convention:
[`formalization-assurance/CORRESPONDENCE_INDEX.md`](https://github.com/math-commons/formalization-assurance/blob/main/CORRESPONDENCE_INDEX.md)).
`status`: proved | statement-only | absent. `fidelity`: faithful | flagged |
unchecked. `numeric`: independent cross-check — `pass@mpmath` runs in
[`numerical/validate_lambda.py`](numerical/validate_lambda.py) (output
[`validate_lambda.out.txt`](numerical/validate_lambda.out.txt)); see
[`FIDELITY_REVIEW.md`](FIDELITY_REVIEW.md).

Sources: SW = Seiberg–Witten *Nucl. Phys.* B426 (1994); KLYT = Klemm–Lerche–
Yankielowicz–Theisen *Phys. Lett.* B344 (1995); AF = Argyres–Faraggi *PRL* 74
(1995); Lerche = hep-th/9611190; DS = Diamond–Shurman, *A First Course in Modular
Forms*; classical = standard modular/theta theory.

## SW corpus (the physics statements)

| source_id | informal | lean_decl | status | fidelity | numeric | deps |
|---|---|---|---|---|---|---|
| KLYT/AF: SW curve | SU(N) curve `y²=P_N²−Λ^{2N}` hyperelliptic, genus `N−1` | `genus_swCurve` | **proved** | faithful (degree count) | n/a | std-3 |
| SW: SU(2) curve | `y²=(x²−u)²−Λ⁴` has genus `1` | `genus_swCurve_su2` | **proved** | faithful | n/a | std-3 |
| SW §3–4: singularity count | curve singular **iff** `u = ±Λ²` (monopole/dyon, no others) | `su2_singular_locus` | **proved** | faithful | `pass@numpy` | std-3 |
| SW/Lerche §2: special geometry | period matrix `τ = τᵀ` (R1) | `sw_coupling_mem_siegel_rank` | **proved** | faithful (Siegel type) | n/a (∃) | std-3 + `AX_PeriodCycleBasis` |
| SW/Lerche §2: metric positivity | `Im τ ≻ 0` ⇒ special-Kähler metric positive | `sw_metric_posDef` | **proved** | faithful (Siegel type) | n/a (∃) | std-3 + `AX_PeriodCycleBasis` |
| SW §3: monopole monodromy class | Picard–Lefschetz transvection `v↦v+⟨v,γ⟩γ` is symplectic | `transvection_isSymplectic` | **proved** | faithful | n/a | std-3 |
| SW §3–4: EM duality group | `Sp(2r,ℤ)` monodromy target (= `SL(2,ℤ)` at `r=1`) | `symplecticMonoid`, `MulAction SL(2,ℤ) (Siegel 1)` | **proved** | faithful | n/a | std-3 |
| SW: rigidity (rank 1) | hypotheses fix the SU(2) solution up to `Sp(2,ℤ)` | `sw_su2_unique` | **proved** | faithful | n/a | std-3 + `AX_thrice_punctured_uniformization`, `AX_developing_map_rigidity` (physics = the defined `SameSWMonodromy` hypothesis) |
| SW §2: prepotential / periods | `a,a_D=∮λ_SW`; `a_D=∂F/∂a`, `τ=∂²F/∂a²` | — | absent | — | — | — |
| AD: deeper strata | Argyres–Douglas = mutually-non-local coalescence (derived) | `NonLocalDegenerationLocus` (def) | n/a (def) | faithful | — | std-3 |

## Supporting machinery (the rigidity proof's analytic core)

| source_id | informal | lean_decl | status | fidelity | numeric | deps |
|---|---|---|---|---|---|---|
| classical: SU(2) base | `ℂ∖{±Λ²} ≃ ℂ∖{0,1}` (thrice-punctured sphere) | `su2BaseEquiv` | **proved** | faithful | n/a | std-3 |
| classical: identity theorem | holomorphic rigidity in a fixed frame | `holo_eqOn_of_germ` | **proved** | faithful | n/a | std-3 |
| DS §1: modular λ | `λ = θ₂⁴/θ₃⁴` (from Mathlib `jacobiTheta₂`); `λ(i)=½` | `modularLambdaFn` | **proved** (def) | faithful | `pass@mpmath` | std-3 |
| classical: Jacobi quartic | `θ₃⁴ = θ₂⁴ + θ₄⁴` | `AX_jacobi_quartic` | axiom (vetted) | faithful | **`pass@mpmath`** | — |
| classical: θ₃ non-vanishing | `θ₃ ≠ 0` on `ℍ` | `AX_theta3_ne_zero` | axiom (vetted) | faithful | `pass@mpmath` (partial) | — |
| classical: `1−λ` | `1 − λ = θ₄⁴/θ₃⁴` | `oneMinusLambda` | **proved** | faithful | `pass@mpmath` | + quartic, θ₃≠0 |
| classical: θ₂,θ₃ S-law | `θ(-1/τ) = (-iτ)^{½}·θ` | `theta3_neg_inv`, `theta2_neg_inv` | **proved** | faithful | (via λ S-law) | std-3 |
| classical: λ under `T²` | `λ(τ+2) = λ(τ)` | `modularLambda_add_two` | **proved** | faithful | **`pass@mpmath`** | std-3 |
| classical: λ under `S` | `λ(-1/τ) = 1 − λ(τ)` | `modularLambda_S` | **proved** | faithful | **`pass@mpmath`** | + quartic, θ₃≠0 |
| classical: λ under `ST²S⁻¹` | `λ(-1/(-1/τ+2)) = λ(τ)` (2nd `Γ(2)` generator) | `modularLambda_ST2S` | **proved** | faithful | **`pass@mpmath`** | + quartic, θ₃≠0 |

## Coverage

Proved-and-faithful ÷ in-scope SW-corpus rows: **7 / 9** (the prepotential/periods row and
the axiom-conditioned `sw_su2_unique` remain). The supporting machinery is almost entirely
proved; the residual axioms (`AX_jacobi_quartic`, `AX_theta3_ne_zero`,
`AX_thrice_punctured_uniformization`, `AX_developing_map_rigidity`, family-layer) are the Mathlib-scale gaps tracked in
[`PROOF_STATUS.md`](PROOF_STATUS.md). Numeric cross-checks now cover the λ layer and the
singularity locus (the first computable content to come online); period/τ numeric checks
await the Phase-2 period construction.
