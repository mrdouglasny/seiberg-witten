# Reasoning from physics axioms — Seiberg–Witten as a worked example

*How this repo turns a celebrated piece of physical reasoning into an auditable
chain: explicit physical hypotheses on top, machine-checked implications below, and a
clear line between the two. Companion to
[`foundations-for-physical-reasoning.md`](foundations-for-physical-reasoning.md), which
argues why this matters; this page shows the actual Lean.*

> **Historical design note.** This narrative predates the current Lean naming/architecture. Live names are in `SeibergWitten/Physics/Hypotheses.lean` and the paper §4 (`PeriodBase`/`PeriodChart`/`SymplecticReframing`/`IsPolarizedPeriodChart`); the headline are **proved theorems** on the single math axiom `periodRigidityAxiom`. Specific declaration names (`LowEnergyData`, `SmoothCover`, `DualityEquiv`, …) and `#print axioms` outputs below may be stale — kept for the reasoning narrative.

## The problem with formalizing physics

Most physics results are not theorems. The Seiberg–Witten solution of N=2 SU(N)
super-Yang–Mills is the textbook case: there is no proof from the axioms of mathematics
that the low-energy effective theory is governed by the curve
`y² = P_N(x)² − Λ^{2N}`. What exists instead is an *argument* — a tight web of physical
assumptions (holomorphy, the singularity structure, electric–magnetic duality,
asymptotics) that together single out that curve, and which the community trusts because
independent computations agree.

So "formalizing Seiberg–Witten" cannot mean "proving it." It means something more
honest and, for AI-generated physics, more useful:

> State the physical assumptions as **explicit named axioms**, prove every **rigorous
> consequence** of them as a theorem, and keep a bright line between the two — so the
> residual trust collapses onto a short, inspectable list, and `#print axioms` shows
> exactly what each result depends on.

That is *reasoning from physics axioms*. This repo is built around it.

## Two columns

| Column 1 — proved (theorems) | Column 2 — assumed (physics axioms) |
|---|---|
| Given the curve, its genus is `N−1`; its period matrix `τ` is symmetric with `Im τ ≻ 0`; the special-Kähler metric is positive; `a_D = ∂F/∂a`, `τ = ∂²F/∂a²`. | The four-plus physical inputs that say *this curve is the right curve* and *these periods are the effective theory*. |
| `SeibergWitten/Curve.lean`, `SpecialGeometry.lean` — axiom-clean (modulo the inherited `jacobian-challenge` period machinery). | `SeibergWitten/Physics/Hypotheses.lean` — deliberately introduces named axioms. |

The work of the project is to push as much as possible into column 1, and to make
column 2 small, explicit, and vetted.

## The axioms (column 2)

The setup is the data of the low-energy `U(1)^{N−1}` theory on the Coulomb branch
(`r = N−1`, moduli `u ∈ ℂ^r`): the special coordinates `a, a_D`, the coupling matrix
`τ`, and the central charge `Z = nₑ·a + n_m·a_D` whose modulus is the BPS mass.

A faithfulness subtlety, caught in review, shapes the very *type* of the data. The
periods `a, a_D` are multivalued and `τ` is not globally defined on `ℂ^r`: a global
holomorphic map `ℂ^r → SiegelUpperHalfSpace` is constant by Liouville — a free theory.
So the carrier `LowEnergyData r Δ` puts the data on the universal cover `SmoothCover Δ`
of the smooth locus `U = ℂ^r ∖ Δ`, where `τ` can vary and the monodromy lives. (Baking
a false simplification into a definition is the most common way a formalization quietly
lies; the type system here is made to *refuse* the free-theory shortcut.)

On that carrier, six physical hypotheses are stated as named declarations:

1. **`SpecialGeometry`** — N=2 SUSY: a holomorphic prepotential `F` with `a_D = ∂F/∂a`,
   `τ = ∂²F/∂a²`, perturbation theory one-loop exact.
2. **`SingularitiesAreBPS`** — `U` is singular *exactly* where some BPS state becomes
   massless, and nowhere else. (Stated concretely via the central charge.)
3. **`PicardLefschetzAtGenericSingularities`** — at the generic stratum of `Δ`, one
   hypermultiplet goes massless and the monodromy is its Picard–Lefschetz reflection
   `v ↦ v + ⟨v,nₐ⟩nₐ`.
4. **`EMDualityConsistent`** — the monodromies lie in `Sp(2r,ℤ)` and compose to the
   weak-coupling monodromy.
5. **`RSymmetryConsistent`** — the anomalous `U(1)_R → ℤ_{2N}` fixes the symmetric
   positions of the singularities.
6. **`AsymptoticMatch`** — the weak-coupling (one-loop + instanton) expansion is
   asymptotic to the exact periods.

These bundle into `IsPolarizedPeriodChart` (physics name `IsSWEffectiveTheory`; current predicate/field names are in `SeibergWitten/Physics/Hypotheses.lean` and the paper §4). The headline statements are now two **proved theorems** — each `#print axioms` = standard-3 + the single period axiom `periodRigidityAxiom`, no `sorry` — not axioms:

- `sw_effective_theory_unique_up_to_duality` — the six hypotheses fix the solution
  **uniquely up to `Sp(2r,ℤ)` duality**;
- `sw_curve_admits_effective_theory` — the SW curve realizes such a theory.

Existence + uniqueness is the precise content of *"the SW curve is the answer."*

## Derived, not assumed: Argyres–Douglas points

A good test of an axiom set is whether the *surprises* it should explain come out as
consequences rather than needing new postulates. Argyres–Douglas points — where the
theory becomes an interacting SCFT with no Lagrangian — are exactly such a surprise.
They are **not** a new axiom here. They are a *definition*:

```
ArgyresDouglasLocus Δ d := { u | ∃ n n', n ≠ 0 ∧ n' ≠ 0 ∧ diracPairing n n' ≠ 0 ∧
                                  BecomesMasslessAt Δ d u n ∧ BecomesMasslessAt Δ d u n' }
```

the locus where two *mutually non-local* charges (nonzero Dirac–Schwinger–Zwanziger
pairing `diracPairing`) become massless together. They still satisfy hypothesis 2 (they
are massless-BPS loci); what they evade is the *single-reflection* hypothesis 3, which is
why 3 is restricted to the generic stratum. This is the methodology paying off: a
phenomenon that looks like it needs its own physical input is instead forced by the
charge lattice and the central charge already in hand. (Coalescence of *mutually local*
charges, `diracPairing = 0`, gives enhanced gauge symmetry instead — same definition,
opposite pairing.)

## What you can read off the result

Because column 2 is a finite list of named axioms, you can ask the proof assistant what
any result actually rests on. For the headline:

```
#print axioms sw_effective_theory_unique_up_to_duality
-- propext, Classical.choice, Quot.sound, DualityEquiv, SmoothCover,
-- sw_effective_theory_unique_up_to_duality
```

— the three standard logical axioms, plus exactly the physics symbols it invokes. The
proved consequences in column 1 do *not* depend on the physics axioms at all:

```
#print axioms SeibergWitten.genus_swCurve        -- [propext, Classical.choice, Quot.sound]
#print axioms SeibergWitten.sw_coupling_mem_siegel -- + Jacobians.Axioms.AX_PeriodCycleBasis
```

This is the payoff of the discipline. Trust is not spread through prose no one
re-checks; it is localized onto named axioms, each carrying a citation and a
faithfulness note, recorded in [`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md), and the
dependency graph is machine-checkable.

## Why this is the right model for AI-generated physics

When an AI produces a physics result, the danger is not usually a wrong algebra step —
it is an unstated assumption smuggled in as if it were derived. Reasoning from physics
axioms makes that impossible to hide: every physical input must be *named* to be used,
every named input shows up in `#print axioms`, and an honest definition (like the
universal-cover carrier, or AD points as a derived locus) refuses to encode a
convenient falsehood. The remaining job — *justifying* the axioms — is then the
physicist's: independent agreement across perturbation theory, instantons (Nekrasov),
and the exact periods, which this repo attaches as numeric cross-checks rather than
assertions.

Formalization does not make the physics true. It makes the reasoning **auditable** — and
that is exactly what a result no one can prove from first principles needs.

## Pointers

- Axioms and definitions: [`../SeibergWitten/Physics/Hypotheses.lean`](../SeibergWitten/Physics/Hypotheses.lean)
- Proved consequences: [`../SeibergWitten/Curve.lean`](../SeibergWitten/Curve.lean), [`../SeibergWitten/SpecialGeometry.lean`](../SeibergWitten/SpecialGeometry.lean)
- The axiom ledger: [`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md)
- Why it matters (the talk's thesis): [`foundations-for-physical-reasoning.md`](foundations-for-physical-reasoning.md)
- The physics itself: [`intro-to-the-solution.md`](intro-to-the-solution.md)
