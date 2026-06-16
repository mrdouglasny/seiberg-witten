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
| SW/Lerche §2: special geometry | period matrix `τ = τᵀ` (R1) | — | absent | unchecked | — | — |
| SW/Lerche §2: positivity | `Im τ ≻ 0` ⇒ special-Kähler metric positive (SU(2) first, axiom-free) | — | absent | unchecked | — | — |
| SW: special coords | `aᵢ, a_{D,i} = ∮λ_SW`; `a_D=∂F/∂a`, `τ=∂²F/∂a²` | — | absent | unchecked | — | — |
| SW/Lerche: weak coupling | `a ~ √(2u)`, `τ ~ (i/π)log…` (1-loop + instantons) | — | absent | unchecked | — | — |
| AD: singular locus | discriminant stratification; Argyres–Douglas degenerations | — | absent | unchecked | — | — |

Coverage (proved ∧ faithful ÷ in-scope): 1 / 6 listed (Phase 0). The list grows as
phases land; numeric checks come online with the period computations (Phase 1+).
