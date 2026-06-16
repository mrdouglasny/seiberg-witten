# Correspondence index — SW solution of N=2 SU(N) SYM

Source ↔ Lean map for the Seiberg–Witten corpus (forward-chaining; convention:
[`formalization-assurance/CORRESPONDENCE_INDEX.md`](https://github.com/math-commons/formalization-assurance/blob/main/CORRESPONDENCE_INDEX.md)).
`status`: proved | statement-only | absent. `fidelity`: faithful | flagged |
unchecked. `numeric`: independent numerical cross-check (periods/τ are computable).

Sources: SW = Seiberg–Witten *Nucl. Phys.* B426 (1994); KLYT = Klemm–Lerche–
Yankielowicz–Theisen *Phys. Lett.* B344 (1995); AF = Argyres–Faraggi *PRL* 74
(1995); Lerche = hep-th/9611190.

| source_id | informal | lean_decl | status | fidelity | numeric | deps |
|---|---|---|---|---|---|---|
| KLYT/AF: SW curve | SU(N) SW curve `y²=P_N²−Λ^{2N}` is hyperelliptic of genus `N−1` | `SeibergWitten.genus_swCurve` | **proved** | faithful (degree count) | n/a | std-3 |
| SW: SU(2) curve | `y²=(x²−u)²−Λ⁴` (original SW) has genus `1` | `SeibergWitten.genus_swCurve_su2` | **proved** | faithful | n/a | std-3 |
| SW/Lerche §2: special geometry | period matrix `τ = τᵀ` (R1, special-geometry symmetry) | `SeibergWitten.sw_coupling_mem_siegel_rank` | **proved** | faithful (Siegel type) | pending | std-3 + `AX_PeriodCycleBasis` |
| SW/Lerche §2: positivity | `Im τ ≻ 0` ⇒ special-Kähler metric positive (no ghosts) | `SeibergWitten.sw_metric_posDef` | **proved** | faithful (Siegel type) | pending | std-3 + `AX_PeriodCycleBasis` |
| SW: special coords | `aᵢ, a_{D,i} = ∮λ_SW`; `a_D=∂F/∂a`, `τ=∂²F/∂a²` | — | absent | unchecked | — | — |
| SW/Lerche: weak coupling | `a ~ √(2u)`, `τ ~ (i/π)log…` (1-loop + instantons) | — | absent | unchecked | — | — |
| AD: singular locus | discriminant stratification; Argyres–Douglas degenerations | — | absent | unchecked | — | — |

Coverage (proved ÷ in-scope listed): 4 / 7 (Phases 0 + 1a). The special-geometry rows
transit `AX_PeriodCycleBasis` (off the Buzzard critical path); the axiom-free SU(2)
case is Phase 1b. Numeric checks (`pass@…`) come online with the period
computations (Phase 1b/2). The list grows as phases land.
