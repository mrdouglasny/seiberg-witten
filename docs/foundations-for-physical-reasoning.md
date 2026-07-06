# Foundations for physical reasoning — Seiberg–Witten as codified lore

*Companion note to the ICML 2026 talk "Validation of AI-generated results in
theoretical physics" (`docs/talk/validation.tex`). Why this formalization project is
the canonical example of the talk's deepest theme.*

## Two kinds of formalization in physics

| | What it is | Examples |
|---|---|---|
| **Traditional mathematical physics** | A rigorous statement exists; you prove it. The mathematician's paradigm applies directly. | Stability of matter, CPT; `mrdouglasny/lgt` (lattice YM mass gap), OSforGFF (free QFT, OS axioms); **and the rigorous core of *this* repo** — the SW curve, `genus = N−1`, special-Kähler `R1/R2`, the period matrix and prepotential, all proved from `jacobian-challenge`. |
| **Foundations for physical reasoning** | Codifying the *non-rigorous* reasoning physicists nonetheless trust — where there is no proof from foundations, and may never be, yet agreement is rock-solid. | **The Seiberg–Witten *argument* itself.** |

The repo's Lean development lives in the first column. The *physical argument* that
singled out the SW curve in the first place lives in the second. This note is about the
second, and how the first makes it auditable.

## What the repo proves vs. the lore it rests on

The formalization establishes the **implications** — `A,B,C ⇒ X,Y,Z`:

> *Given* the SW curve `y² = P_N(x)² − Λ^{2N}` and the period geometry of
> `jacobian-challenge`, *then* `τ = τᵀ`, `Im τ ≻ 0`, the special-Kähler metric is
> positive, `a_D = ∂F/∂a`, `τ = ∂²F/∂a²`, …

What it does **not** establish — and what no proof from ZFC will — is that *this curve
is the right curve*. That step is **physical lore**, a tight web of assumptions the
community trusts:

1. **Holomorphy / non-renormalization** (from `N=2` SUSY): the low-energy effective
   theory on the Coulomb branch is captured by a single holomorphic prepotential `F`;
   perturbative corrections stop at one loop.
2. **Exact singularity structure**: the Coulomb branch has *exactly* the expected
   singularities — points where a monopole or dyon becomes massless — and *no others*.
3. **Electric–magnetic duality**: the `Sp(2(N−1),ℤ)` monodromies around those
   singularities must compose consistently with the one at weak coupling.
4. **Asymptotic matching**: the weak-coupling (one-loop + instanton) expansion is
   asymptotic to the exact answer encoded in the periods.

Holomorphy + the assumed singularities + duality + asymptotics **uniquely fix the
curve**. None of (1)–(4) is a theorem of mathematics; together they are *why physicists
believe the answer*.

## Why it is trusted: the perturbation ↔ instanton ↔ exact triangle

The SW solution is the textbook case where trust comes from **independent agreement**
across three handles on the same quantity:

- **Perturbation theory** — one-loop-exact for `N=2`, the weak-coupling asymptotics.
- **Semiclassics / instantons** — the `Λ^{2N}`-series; **Nekrasov's instanton partition
  function reproduces the SW prepotential order by order**, and that instanton sum was
  *later made rigorous* (Nekrasov–Okounkov, Nakajima–Yoshioka).
- **The exact result** — the SW curve and its periods.

These three agreeing *is* the validation. This is the same "survive the physicist's
battery of consistency checks" that the talk argues must accompany any AI-generated
result. Phase 3 of `PLAN.md` already wires in `math-commons/picard-lefschetz` for the
Picard–Fuchs ODEs governing the weak-coupling/instanton asymptotics — i.e., the formal
infrastructure to *check the asymptotic matching*, not just assert it.

## What "codifying the lore" buys (the talk's thesis, here)

Formalization does not make the lore *true*. It does three things that matter:

- **Makes the dependency structure machine-checkable** — exactly which results rest on
  holomorphy, which on the no-extra-singularity assumption, which on duality. If a
  surprise appears (an unexpected Argyres–Douglas point, a failure of asymptotic
  matching), you can trace precisely what propagates.
- **Localizes the trust**. The rigorous implications are certified by the proof kernel;
  the residual trust collapses onto a *small set of explicit physical axioms*, each
  stated, vetted, and recorded (`AXIOM_AUDIT.md`, `formalization.yaml`, the
  faithfulness/comparator protocol of `formalization-assurance`) — rather than spread
  through a long informal argument no one re-checks.
- **Lets the verifier detect contradiction** — the audit can flag if the codified
  axioms, together with the proved implications, are inconsistent.

## How to do it in this repo

- **Rigorous spine (proved):** Phases 0–2 — curve, genus, special geometry, periods,
  prepotential — from `jacobian-challenge`. These are the `A,B,C ⇒ X,Y,Z`.
- **Codified lore (named axioms to state + vet):** the four physical inputs above.
  Each becomes a named axiom with a faithfulness note, tracked in `AXIOM_AUDIT.md` /
  `formalization.yaml`.
- **Independent-agreement checks (the validation):** the numeric/comparator
  cross-checks the repo already attaches per landed result — Nekrasov instanton vs. SW
  prepotential at low order, monodromy composition, period numerics — are precisely the
  "multiple consistency checks" that earn trust.

## Talk cross-reference

This note backs two slides of `docs/talk/validation.tex`:

- **"The deep frontier — foundations for physical reasoning."**
- **"Example — codifying the lore behind an exact result"** (the Seiberg–Witten slide).

Contrast with the *traditional math physics* examples (OSforGFF, lgt) and the
*verified physical computation* worked example (the collider amplitude). The collider
amplitude is rigorous-derivation-plus-spec; Seiberg–Witten is the harder, deeper case —
**non-rigorous lore, made auditable**.
