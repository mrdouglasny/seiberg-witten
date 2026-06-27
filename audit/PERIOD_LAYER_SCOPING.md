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

## The needed results, in informal mathematics

*Setup.* Fix `Λ ≠ 0`, `N ≥ 2`, rank `r = N − 1`. For a modulus `u` (the trace-free Casimirs) let
`C_u` be the genus-`r` hyperelliptic curve `y² = P_u(x)² − Λ^{2N}`, and `U = {u : C_u smooth} =
{Δ(u) ≠ 0}` the moduli base. Let `λ_SW` be the Seiberg–Witten meromorphic differential on `C_u`
(its `u`-derivatives `∂λ_SW/∂u_i` are holomorphic 1-forms), and fix a symplectic basis
`A_i, B_i` of `H₁(C_u, ℤ)`.

**(P1) Period map.** The periods `a_i(u) = ∮_{A_i} λ_SW` and `a_{D,i}(u) = ∮_{B_i} λ_SW` are
holomorphic multivalued functions on `U` (single-valued on its universal cover): the period
vector varies holomorphically with the modulus (the Gauss–Manin period map is holomorphic).

**(P2) Picard–Fuchs.** `(a, a_D)` satisfy a holomorphic linear ODE system in `u` (the Gauss–Manin
connection). For SU(2): one second-order Fuchsian ODE in `u`, regular singular points at
`u = ±Λ²` and `∞`.

**(P3) Special geometry ⇒ H1.** `τ_{ij}(u) = ∂a_{D,i}/∂a_j` is symmetric with positive-definite
imaginary part (Riemann's bilinear relations), so `τ(u) ∈ Siegel(r)`; and there is a holomorphic
prepotential `F` with `a_{D,i} = ∂F/∂a_i`, `τ = ∂²F/∂a²`.

**(P4) Monodromy + Picard–Lefschetz ⇒ H3.** Analytic continuation around loops gives
`ρ : π₁(U) → Sp(2r, ℤ)`. Around each discriminant component — where a cycle `γ` vanishes, i.e. a
BPS state of charge `γ` becomes massless — the monodromy is the Picard–Lefschetz transvection
`v ↦ v + ⟨v, γ⟩ γ`. (Discharges `AX_picard_lefschetz_local`.)

**(P5) Rigidity ⇒ `PeriodLayer.rigidity` / B′.** `ρ` is irreducible (for SU(2): two parabolic
transvections generate a non-abelian, hence irreducible, group). So two period maps over the same
base with the same monodromy differ by a constant matrix commuting with `ρ`, which by Schur is a
scalar; the weak-coupling normalization (P6) fixes the scalar to `1`. Hence on a connected overlap
the two period vectors are related by a single constant `Sp(2r, ℤ)` matrix — **the period frame.**

**(P6) Weak-coupling asymptotics ⇒ H6.** As `u → ∞`, `a_i ∼` the classical value (`a ∼ √(2u)` for
SU(2)) and `a_{D,i} ∼` the one-loop logarithm `(i/π)·(\text{1-loop coeff})·a_i log(a_i/Λ)` plus an
instanton series in `Λ^{2N}`, with the **exact** (one-loop-exact) leading coefficients — which is
what makes the scalar in P5 equal `1` and the period frame integral.

**(P7) Existence ⇒ `PeriodLayer.realize`.** For a smooth modulus the data (P1, P3) assemble into a
`Sheet` — periods and coupling on a simply-connected chart — satisfying H1–H6, with singular locus
exactly `{Δ(u) = 0}`. (For `N ≥ 3` the discriminant is a hypersurface with Argyres–Douglas strata
where several cycles vanish together; P4's transvection picture is the *generic*-stratum statement.)

P5 and P7 are literally the layer's two fields (`rigidity`, `realize`); P1–P4 and P6 are what
prove them. The one piece with no Lean precedent is the **holomorphic variation** P1/P2 — periods
moving holomorphically with a flat connection.

*Probe result (`Physics/PeriodVariationProbe.lean`).* P1/P2 is **reachable**: Mathlib's
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` gives the complex derivative
of a parameter integral, proved end-to-end (standard-3) for a model integrand `exp(u·t)` —
`model_period_differentiable : Differentiable ℂ (fun u => ∫ t in 0..1, exp(u·t))`. The friction is
entirely the *domination* hypothesis (a uniform integrable bound on `∂F/∂u`), discharged here from
contour-compactness + continuity. The SW-specific work that remains plugs into the same lemma:
the integrand `((x²−u)²−Λ⁴)^(−1/2)` holomorphic in `u` on the smooth locus (`cpow` off its branch
cut), and domination across the integrable `√`-singularity at the branch points — standard
analysis, no fundamental obstruction.

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

**The big asset: `jacobian-challenge` is already the `Jacobians` dependency** (the manifest binds
`Jacobians → ../jacobian-challenge`). It supplies the **per-fiber (single-curve) period theory** —
the hardest classical half — largely sorry-free (≈2466 proved, 23 sorry, 15 axioms):
- `Jacobians.ProjectiveCurve.Elliptic.Periods` — the genus-1 A/B-cycle period integrals
  (`aLoop_period_eq`, `bLoop_period_eq`): *exactly the SU(2) periods of one elliptic fiber*.
- `Jacobians.Layer3.Periods` / `PeriodLattice` — period matrix, `periodBasis`, `periodColumns`,
  and Riemann-bilinear positivity (`eq_zero_of_posDef_mulVec_eq_zero`) ⇒ feeds H1's `Im τ ≻ 0`.
- `Jacobians.Axioms.RiemannBilinear` (already imported), `AbelianVariety.{Siegel,Theta,ComplexTorus}`,
  and the large `ProjectiveCurve.Hyperelliptic.*` stack (genus, atlas, cycle basis, involution,
  forms) — the genus-`(N−1)` SW curve fiber and its Jacobian/period domain.
- (`jacobian-claude` is complementary: Buzzard's categorical Jacobian-API challenge solved —
  `genus`, `Jacobian` functor, `ofCurve`, `pushforward`/`pullback`, standard-3 — the abstract
  abelian-variety side, not the period integrals.)

**What `jacobian-challenge` does NOT have — the family/variation half (the real gap):** it does
*one curve / one Jacobian*. There is no `GaussManin`, no `PicardFuchs`, no period-matrix
**variation over the moduli `u`**; its only `monodromy` is covering-space `π₁` monodromy
(`Topology.CoveringPi1`), **not** the `Sp(2r,ℤ)`-valued Gauss–Manin monodromy of the periods over
`U`. So the missing middle is precisely: assemble the per-fiber periods into a **variation over
`u`** (Gauss–Manin connection ⇒ `Sp`-monodromy ⇒ Picard–Fuchs), then the rigidity (step 4).

In this repo: `Family.SWVariation` / `VHS.WeightOneVHS` (`monodromy_mem_symplecticMonoid`) are the
VHS *spec*; `SU2Rigidity.su2_frame_alignment` (Γ(2)-covering coupling rigidity) and
`SU2Uniqueness.su2_deck_of_periodFrame` (frame ⇒ `Deck`, zero-axiom) are the rank-1 endgame.

**Revised hardness with this dependency:** the per-fiber build is mostly done, so the period
layer is largely *family glue* on top of `jacobian-challenge`. At genus 1 especially — sitting on
`Elliptic.Periods` + this repo's `λ`/`θ` + `AX_developing_map_rigidity` — the remaining work is
"vary `u` ⇒ `SL(2,ℤ)` Gauss–Manin monodromy + rigidity," which shortens the SU(2) estimate.

## Recommended ordering

1. **SU(2) period map + Picard–Fuchs ODE** (the elliptic case) — *reuse* `jacobian-challenge`'s
   `Elliptic.Periods` (A/B period integrals) and `Layer3.PeriodLattice`; the new content is the
   *variation over `u`* (how those periods move as the curve's modulus changes). Unblocks 1–3.
   *Done (bridge): `Physics/SWFamily.lean` realizes the SW fiber `y²=(x²−u)²−Λ⁴` as
   `jacobian-challenge`'s `HyperellipticData` over `u` and proves `genus = 1` (standard-3, via its
   own genus formula) — so the per-fiber curve type is reusable. The `u`-variation of the periods
   on top of it remains the new build (measured: `jacobian-challenge` has no curve-in-a-parameter
   notion).*
2. **Step 4 rigidity at genus 1** — reuse `AX_developing_map_rigidity`; this discharges
   `PeriodLayer.rigidity` and removes the period-frame hypothesis from the SU(2) closure.
3. **`realize` at genus 1** — verify H1–H6 on the elliptic period sheet.
4. *(Long horizon)* the general-genus VHS: families Jacobians + `Siegel(r)` Gauss–Manin +
   higher-rank `deck_of_periodFrame`, discharging `SWPeriodLayer` for all `N`.
