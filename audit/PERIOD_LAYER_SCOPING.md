# Scoping: the period-level (Picard–Fuchs / Gauss–Manin) layer

*What it would take to **discharge** `PeriodLayer` / `SWPeriodLayer`
(`SeibergWitten/Physics/PeriodLayer.lean`) — i.e. to turn their `rigidity` and `realize` fields
from assumed clauses into theorems. Companion to [`SU2_UNIQUENESS_SCOPING.md`](SU2_UNIQUENESS_SCOPING.md).*

## Where we are

The SU(2) and general SU(N) headline goals (B.1: uniqueness up to duality, and existence) are
**proved modulo a structure**:

- `PeriodLayer Λ` (SU(2)) — `rigidity` (connected overlap ⇒ `SL(2,ℤ)` period frame) + `realize`
  (the curve realizes a theory). `sw_su2_unique_of_periodLayer` routes through the **zero-axiom**
  `su2_deck_of_periodFrame` (so `frame ⇒ Deck` is *proved*); `sw_su2_exists_of_periodLayer`.
- `SWPeriodLayer N Λ` (general, rank `N−1`, genus `N−1`) — `rigidity` carries the `Sp(2(N−1),ℤ)`
  `Deck` directly + `realize`; `PeriodLayer.toGeneral` exhibits SU(2) as the proved refinement.

Both layers are *hypotheses*, so the theorems are **standard-3**. Discharging the layer means
building the period geometry that *proves* `rigidity` and `realize`. This doc names the defs and
theorems that work needs.

## The basic definitions

| Def | Meaning | Status |
|-----|---------|--------|
| `swFamily` | the family of curves `C_u : y² = P_u(x)² − Λ^{2N}` over `U` — genus-`(N−1)` Riemann surfaces | have `swCurvePoly`; need the family of surfaces |
| `swDifferential` (`λ_SW`) | the Seiberg–Witten meromorphic 1-form, `dλ_SW =` the holomorphic symplectic form | not built |
| `H₁` local system | `H₁(C_u, ℤ) ≅ ℤ^{2(N−1)}` with the intersection pairing, varying over `U` | **spec** in `Family.SWVariation` / `VHS.WeightOneVHS`; need the actual `H₁` of the family |
| **`periodMap`** | `a_i(u) = ∮_{A_i} λ_SW`, `a_{D,i}(u) = ∮_{B_i} λ_SW`; coupling `τ =` period matrix `∈ Siegel(N−1)` | **the keystone — not built** |
| `picardFuchs` | the order-`2` (SU(2)) / higher ODE annihilating the periods | not built |

## The theorems (and which layer field each discharges)

1. **Gauss–Manin ⇒ monodromy** `ρ : π₁(U) → Sp(2(N−1),ℤ)` (flat connection on `H₁`). Promotes
   the `SWVariation` spec to the actual family. *(Feeds A and `rigidity`.)*
2. **Picard–Lefschetz**: local monodromy around a `Δ`-component = transvection in the vanishing
   cycle — *proves* H3 and discharges `Monodromy.AX_picard_lefschetz_local`. *(A.)*
3. **Riemann bilinear relations ⇒ special geometry H1**: `τ` symmetric, `Im τ ≻ 0`,
   `a_D = ∂F/∂a` for a prepotential `F`. Have the `Jacobians.Axioms.RiemannBilinear` import.
4. **Rigidity ⇒ `PeriodLayer.rigidity` (= B′):** two period maps with the same `ρ` differ by an
   element of its centralizer; the SW monodromy is **irreducible** (Schur) ⇒ a scalar; the H6
   asymptotic normalization fixes the scalar to `1` ⇒ the `SL(2,ℤ)` period frame. **The heart**
   — the genuinely new analytic argument (and the one the SU(2) closure ultimately rests on).
5. **H6 asymptotics**: the weak-coupling expansion `a ∼ √(2u)`, `a_D ∼ (i/π) a ln a + …`
   (one-loop + instanton). Must fix the *exact* scale (not just `∝`), or step 4's frame fails to
   be integral. *(Feeds B′ normalization and `realize`'s H6.)*
6. **`realize`**: assemble 1–5 into a `Sheet` whose `a, aD` are the periods, and *verify* H1–H6
   on it (the existence clause). For `N ≥ 3`, respect the Argyres–Douglas strata where the
   single-transvection picture is generic-only.

## How hard

Recalibrated to this project's Lean-time norms (sister-task where infrastructure exists):

- **SU(2) (genus 1): a few weeks active.** The family is *elliptic*; periods are elliptic
  integrals; `τ ∈ ℍ`; monodromy in `SL(2,ℤ)`. Mathlib + this repo already supply `ℍ`, the
  modular `λ` (`ModularLambda.lean`), the `θ` functions (`ThetaLambda.lean`), and — crucially for
  step 4 — `AX_developing_map_rigidity`. The work is: build the elliptic period map + its
  (hypergeometric) Picard–Fuchs ODE, and wire steps 1–5 to the existing λ/θ/rigidity machinery.
- **General SU(N) (genus `N−1`): months — a Mathlib-scale build.** Needs higher-genus Jacobians,
  `Siegel(N−1)`, the Gauss–Manin connection *for a family*, and Schottky-aware rigidity. Mathlib
  has no families-of-Riemann-surfaces VHS; that is the genuine infrastructure investment.

## Existing scaffold (build on, don't redo)

- `Family.SWVariation` (polarized integral weight-1 VHS over `U = ℂ^r ∖ Δ`) with
  `generator_isSymplectic`, `monodromy_mem_symplecticMonoid` — the *specification*.
- `VHS.WeightOneVHS` (base-agnostic weight-1 VHS) + `SWVariation.toVHS`.
- `Jacobians.Axioms.RiemannBilinear` (imported by `Hypotheses.lean`).
- The rank-1 analytic core: `SU2Rigidity.su2_frame_alignment` (coupling rigidity via the Γ(2)
  covering), `SU2Uniqueness.su2_deck_of_periodFrame` (frame ⇒ `Deck`, zero-axiom).

These are *specs and the rank-1 endgame*; the missing middle is the **period map** (the `∮ λ_SW`
integrals) and the **Picard–Fuchs ODE**, plus step 4's rigidity argument.

## Recommended ordering

1. **SU(2) period map + Picard–Fuchs ODE** (the elliptic case) — unblocks steps 1–3 at genus 1.
2. **Step 4 rigidity at genus 1** — reuse `AX_developing_map_rigidity`; this discharges
   `PeriodLayer.rigidity` and removes the period-frame hypothesis from the SU(2) closure.
3. **`realize` at genus 1** — verify H1–H6 on the elliptic period sheet.
4. *(Long horizon)* the general-genus VHS: families Jacobians + `Siegel(r)` Gauss–Manin +
   higher-rank `deck_of_periodFrame`, discharging `SWPeriodLayer` for all `N`.
