# Roadmap (draft): the Schwarz reflection principle

*A **draft Tau Ceti roadmap entry** we would propose to
[`FormalFrontier/TauCetiRoadmap`](https://github.com/FormalFrontier/TauCetiRoadmap) as
`TauCetiRoadmap/SchwarzReflection/` (this `README.md` + `Targets.lean`). It lives in the
seiberg-witten repo as a working sketch — Schwarz reflection is the analytic keystone our
modular-`λ` covering needs (see `../../audit/SCHWARZ_REFLECTION_SCOPING.md`), but it is
**not** SW-specific: it is basic complex analysis that belongs upstream. Written to the
roadmap repo's conventions: build the library not the theorem, ground everything in
Mathlib, pin conventions up front, write Lean signatures.*

Mathlib has the **Cauchy-theory substrate** — contour integrals, the rectangle-integral
vanishing lemma `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`,
`Analysis/Complex/HasPrimitives`, the Riemann removable-singularity theorem (point version),
`conjCLE`/`starRingEnd ℂ`, the open mapping theorem — but **not the Schwarz reflection
principle**. (`Mathlib/Analysis/Complex/Schwarz.lean` is the *Schwarz lemma*, `‖f z‖ ≤ ‖z‖`
for disk self-maps — a different theorem.) A web search (2026-06) surfaced no formalization
of the reflection principle in Lean, Isabelle, or Coq: this is genuinely new.

The goal is to **build the reflection principle as reusable theory**, not to race to the
real-axis statement. "Done" means a researcher reaching for reflection — for boundary
regularity of the Riemann map, Schwarz–Christoffel, the modular/elliptic uniformization, or
plain analytic continuation across a real-analytic boundary — finds it at its natural
generality with the basic API (the reflected function, its agreement and symmetry, the
across-an-arc and across-a-circle forms).

Suggested home: `TauCeti/Analysis/Complex/SchwarzReflection.lean`.

## Generality bar (decide up front; do not silently specialize)

- **Real-axis, scalar-valued first; conjugation-symmetric domain.** Layer 1 is reflection
  across (a segment of) `ℝ` for `f : ℂ → ℂ` on a conjugation-symmetric open `Ω`
  (`z ∈ Ω ↔ (starRingEnd ℂ) z ∈ Ω`). This is the load-bearing case and the one the covering
  needs. Conjugation is **`starRingEnd ℂ`** throughout (Mathlib's vocabulary), never an ad hoc
  `fun z => ⟨z.re, -z.im⟩`.
- **The boundary hypothesis is "`f` is real on `L`".** Stated `∀ z ∈ Ω, z.im = 0 → (f z).im = 0`.
  The reflected extension is the **explicit witness**
  `F z = if 0 ≤ z.im then f z else (starRingEnd ℂ) (f ((starRingEnd ℂ) z))` — pin this form
  (existence is proved *with* this witness, so downstream users get the formula, not just `∃`).
- **Continuity only up to the line.** `f` is `ContinuousOn (Ω ∩ {im ≥ 0})` and
  `DifferentiableOn ℂ` on `Ω ∩ {im > 0}`; do **not** assume differentiability on `L`.
- **`E`-valued is a later generalization, not the default.** State Layer 1 for `ℂ → ℂ`. A
  Banach-`E`-valued form (`f : ℂ → E`, with `conj` replaced by an antilinear involution /
  real structure on `E`) is a stretch; flag it, don't silently bake it in.
- **Across an arc / circle = Layer 2, by reduction.** The reflection across a real-analytic
  arc or a circle reduces to the line case by a biholomorphic (Möbius) change of coordinates;
  state it as its own milestone built *on* Layer 1, not from scratch.

## Layers (each a discharge-gated milestone; `sorry` in `Targets.lean` is the goal)

- **Layer 0 — antiholomorphic composition.** `z ↦ (starRingEnd ℂ) (f ((starRingEnd ℂ) z))`
  is `DifferentiableOn ℂ` on the reflected set when `f` is. The one genuinely missing
  micro-lemma (a few lines from `conjCLE` + chain rule); the foundation for the witness.
- **Layer 1 — the reflection principle (summit of this entry).** The real-axis statement
  above: `f` extends holomorphically across `L` via the witness, with agreement on the closed
  upper half and the symmetry `F (conj z) = conj (F z)`. Proof route: Morera — `F` is
  continuous on `Ω` and holomorphic off `L`, so its boundary integral over every rectangle
  vanishes (split at `L`; each half is a limit of rectangles inside `Ω±` where the
  rectangle-vanishing lemma applies; continuity passes to the limit), hence `F` has local
  primitives, hence is holomorphic.
- **Layer 2 — arc/circle reflection** (built on Layer 1 by Möbius reduction) and the
  **`E`-valued** form. Optional for the covering, expected by general users.

## Why it matters / downstream

Reflection is a prerequisite for: boundary regularity of the **Riemann mapping**,
**Schwarz–Christoffel**, the **modular `λ` / elliptic uniformization** (the
`ℍ/Γ(2) ≅ ℂ∖{0,1}` covering — see the SW project's `audit/COVERING_SCOPING.md`, where it
combines with the existing `TauCetiRoadmap/UniversalCovers` deck-group milestone), and
analytic continuation across real-analytic boundaries generally.

## References

Ahlfors, *Complex Analysis* §6.5 (and *Conformal Invariants*); Conway, *Functions of One
Complex Variable I* §IX.1; Stein–Shakarchi, *Complex Analysis* §2.5. New formalization (no
known prior art); credit none — original.
