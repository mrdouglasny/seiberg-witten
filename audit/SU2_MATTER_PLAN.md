# Plan: SU(2) with matter (N_f > 0), and the Argyres–Douglas points

*Goal: establish that **N=2 SU(2) SQCD with N_f fundamental hypermultiplets** fits the existing
framework, and exhibit **Argyres–Douglas (AD) points** — the locus where mutually non-local BPS
states collide — which are **empty for pure SU(2)** but appear once N_f > 0. This both vindicates the
general `ArgyresDouglasLocus` definition (`Physics/Hypotheses.lean:245`) with a worked nonempty case
and shows the framework is not pure-gauge-specific. References: Seiberg–Witten II (Nucl. Phys. B431,
1994); Argyres–Douglas (Nucl. Phys. B448, 1995); Argyres–Plesser–Seiberg–Witten, arXiv:hep-th/9511154.*

## How far we need to take it (the answer up front)

- **M0–M2 (no new axioms) prove the headline of this plan**: with matter the SW curve admits a
  collision of singularities (a cusp) that pure SU(2) cannot have — i.e. *AD points appear*. Pure
  algebra, standard-3. **This alone establishes that N_f > 0 is doable and produces AD points.**
- **M3–M4 embed it in the physics framework**: a small carrier extension (flavor charges + masses in
  the central charge) and the identification of the cusp with a mutually-non-local massless
  collision, modulo a *matter period layer* (the same period/monodromy debt we already carry for
  pure SU(2) as `swPeriodLayer`/`SameSWMonodromy` — no new *kind* of axiom).
- **M5–M6 are optional breadth**: N_f = 2, 3 AD points; the matter `IsSWEffectiveTheory` and its
  `swPeriodLayer`.

So: take it through **M2** to settle doability and AD-appearance with zero axiom cost; through
**M4** to connect it to `ArgyresDouglasLocus` and H0–H6; **stop before** building the full matter
period geometry, which is the deferred analytic layer common to the whole project, not specific to
matter.

## Physics recap (what changes from pure SU(2))

Still **rank 1, genus 1**: the Coulomb branch is the `u`-plane, the curves are elliptic, the carrier
`CoulombBase 1` / `Sheet` and the hypotheses H0–H6 reuse unchanged. What matter adds:

- **Curves** (SW-II, quartic form), scale `Λ ≡ Λ_{N_f}`, masses `m_i`:
  `y² = (x² − u)² − Λ^{4−N_f} · ∏_{i=1}^{N_f} (x − m_i)`.
  N_f = 0 recovers `(x²−u)² − Λ⁴`; the power `4 − N_f = b₀` is the one-loop coefficient (asymptotic
  freedom for N_f ≤ 3). *(Exact normalization/shifts to be pinned against SW-II/APSW at M1; the
  triple-root structure below is convention-robust.)*
- **Central charge** gains flavor terms: `Z = nₑ a + n_m a_D + Σ_i S_i m_i/√2`. The Dirac pairing is
  unchanged (flavor charges `S_i` are global, do not enter it), so *mutual non-locality is
  untouched*.
- **Singular locus**: roots of `disc_x` of the quartic — double root in `x` ⇒ a massless BPS state
  ⇒ a singularity of the `u`-plane. **AD point**: a *triple* root in `x` (the curve degenerates to a
  **cusp** `y² ∼ (x−a)³`), where two such singularities collide and the colliding states are
  mutually non-local — an interacting SCFT with no Lagrangian.

## The flagship computation (verified by `ring`)

The simplest AD point — the `(A₁, A₂)` theory of **N_f = 1** — is an exact polynomial identity. With
`Q(x) = (x²−u)² − Λ³(x − m)`, at the tuned point `(u, m) = (¾Λ², −¾Λ)`:

```lean
-- a TRIPLE root at x = −Λ/2 : the Argyres–Douglas cusp y² ~ (x+Λ/2)³
(x^2 - (3/4)*Λ^2)^2 - Λ^3 * (x - (-(3/4)*Λ)) = (x + (1/2)*Λ)^3 * (x - (3/2)*Λ)   -- by ring ✓
```

Contrast — pure SU(2) splits into two **distinct** quadratics, so its only `x`-collisions are simple
double roots (`u = ±Λ²`), never a triple root: no AD point.

```lean
(x^2 - u)^2 - Λ^4 = (x^2 - (u + Λ^2)) * (x^2 - (u - Λ^2))                         -- by ring ✓
```

Both identities **elaborate and close by `ring`** (checked, `scratchpad/adcheck.lean`): doability is
not in question.

## Milestones

- **M0 — the matter curves.** `swCurveMatter (Nf) (Λ) (m : Fin Nf → ℂ) (u) : Polynomial ℂ` (or `ℂ`
  value), `= (x²−u)² − Λ^{4−Nf} ∏(x − m_i)`; `swCurveMatter 0 … = swCurvePoly` (the pure case).
  *(standard-3.)*
- **M1 — the N_f=1 AD point.** The flagship identity above: at `(u,m)=(¾Λ²,−¾Λ)`, `swCurveNf1`
  factors as `(x+½Λ)³(x−3⁄2Λ)` — a triple root. Plus `Λ ≠ 0 → x = −Λ/2` is a root of multiplicity
  exactly 3 (a cusp). *(standard-3, `ring` + a multiplicity lemma.)*
- **M2 — the contrast (no AD for pure SU(2)).** For `Λ ≠ 0`, `(x²−u)² − Λ⁴` has no triple root in
  `x` for any `u` (its branch points collide only pairwise, at `u = ±Λ²`). *(standard-3.)*
  **M0–M2 deliver "AD points appear with matter," axiom-free.**
- **M3 — carrier extension (flavor/mass).** Extend the central charge with flavor charges + masses:
  `Z = nₑ a + n_m a_D + Σ S_i m_i/√2`; keep `diracPairing` on the (e,m) part only. A `MatterCoulombBase`
  / mass-parameterized `Sheet`, or a flavor field added to the existing carrier. *(standard-3; modest.)*
- **M4 — the cusp is a mutually-non-local collision ⇒ `ArgyresDouglasLocus ≠ ∅`.** Given a *matter
  period layer* (which BPS charges `n, n'` vanish at the AD `u₀`, with `diracPairing n n' ≠ 0` — the
  two cycles colliding at the cusp), conclude `u* ∈ ArgyresDouglasLocus`. *(Inherits period-layer
  debt — one matter axiom of the same kind as `swPeriodLayer`; no new kind.)*
- **M5 — N_f = 2, 3 AD points** (optional breadth): the analogous tuned `(u, m_i)` giving a cusp;
  for N_f=3 the maximal AD point. *(standard-3 algebra.)*
- **M6 — matter `IsSWEffectiveTheory`** (optional): H1–H6 for the matter theory (H5/H6 modified —
  `b₀ = 4−N_f`, the matter one-loop, the flavor symmetry), and a matter `swPeriodLayer` closing the
  matter headline. *(period-layer debt; large, not needed for this plan's goal.)*

## Reuse vs new

| Reused unchanged | New (this plan) |
|---|---|
| `CoulombBase 1` / `Sheet`, H0–H6, `Deck`/`SWAtlas`, `diracPairing`, `ArgyresDouglasLocus`, the genus-1 period machinery, `swCurvePoly` (as the N_f=0 case) | the matter curves (M0); the N_f=1 cusp + multiplicity (M1); the pure-SU(2) no-triple-root contrast (M2); flavor charges + masses in `Z` (M3); the matter period-layer hypothesis (M4) |

## Effort

M0–M2: a few active days (algebra + multiplicity lemmas; the core identities are `ring`). M3: days
(carrier extension). M4: gated by stating the matter period-layer cleanly (an afternoon to state, the
*discharge* being the deferred analytic layer). M5–M6: weeks if pursued. The plan's stated goal
(M0–M4) is **~1–2 active weeks**, all standard-3 except the one M4 matter period axiom.

## Explicitly NOT this plan

- Not the full matter period geometry / matter `swPeriodLayer` *discharge* (M6) — same deferred
  analytic layer as pure SU(2).
- Not higher-rank SU(N) matter (would change genus/rank); this plan is rank-1 SU(2) only.
