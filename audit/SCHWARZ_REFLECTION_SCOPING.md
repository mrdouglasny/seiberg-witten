# Scoping: the Schwarz reflection principle (keystone upstream target)

*The analytic keystone the `λ`-covering route needs (see [`COVERING_SCOPING.md`](COVERING_SCOPING.md)).
It is **not** SW-specific — it is general complex analysis, absent from Mathlib — so it is
scoped here as an **upstream** contribution (Mathlib or Tau Ceti), not as repo-local code.*

## Prior art — is it already proven?

- **Mathlib:** No. `Mathlib/Analysis/Complex/Schwarz.lean` is the **Schwarz lemma**
  (`‖f z‖ ≤ ‖z‖` for disk self-maps) — a *different* theorem, easy to conflate. The
  reflection *principle* is absent.
- **Other provers:** A web search (Lean/Isabelle/Coq, 2026-06) surfaced **no** formalization
  of the reflection principle. It appears unformalized — making it a genuinely new contribution.

## Statement (the real-axis version; conventions pinned)

Let `Ω ⊆ ℂ` be open and **conjugation-symmetric** (`z ∈ Ω ↔ conj z ∈ Ω`). Write
`Ω⁺ = Ω ∩ {im > 0}`, `L = Ω ∩ ℝ`. If `f` is continuous on `Ω⁺ ∪ L`, holomorphic on `Ω⁺`,
and **real on `L`**, then `f` extends holomorphically to all of `Ω` by `F(z̄) = conj(F(z))`.

A clean Lean target signature (Tau-Ceti style — signature, not proof):

```lean
theorem schwarz_reflection
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hsymm : ∀ z, z ∈ Ω ↔ (starRingEnd ℂ) z ∈ Ω)
    {f : ℂ → ℂ}
    (hcont : ContinuousOn f (Ω ∩ {z | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω
      ∧ Set.EqOn F f (Ω ∩ {z | 0 ≤ z.im})
      ∧ ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z)
```
with the witness `F z = if 0 ≤ z.im then f z else conj (f (conj z))`. (Generalizations —
reflection across an analytic arc/circle, `E`-valued `f` — are follow-on targets; the
real-axis scalar version is the load-bearing one.)

## Proof route (Morera) and Mathlib substrate

1. **Reflected branch is holomorphic.** `g z := conj (f (conj z))` is holomorphic on `Ω⁻`
   (antiholomorphic ∘ holomorphic ∘ antiholomorphic). *Substrate:* `conjCLE` /
   `starRingEnd`; needs a small `DifferentiableAt` lemma for `conj ∘ f ∘ conj` (likely a
   few lines from `conjCLE` + chain rule — the one genuinely missing micro-lemma).
2. **Agreement on `L`.** `f` real on `L` ⇒ `g = f` there; with `hcont`, `F` is continuous
   on `Ω`. *Substrate:* elementary.
3. **Holomorphic across `L` (the crux).** `F` continuous on `Ω`, holomorphic off `L`
   ⇒ holomorphic on `Ω`, via Morera: the boundary integral of `F` over every rectangle
   vanishes (split at `L`; each half is the limit of rectangles in `Ω±` where `F` is
   holomorphic; continuity closes the limit), hence `F` has local primitives, hence is
   holomorphic. *Substrate (present):*
   - `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`
     (continuous on closed rect + differentiable on interior ⇒ boundary integral 0) — the
     exact tool for the limiting half-rectangles;
   - `Analysis/Complex/HasPrimitives.lean` (primitives from vanishing rectangle integrals);
   - Cauchy theory and `RemovableSingularity` (point version) for the local-primitive ⇒
     holomorphic step.

So Mathlib supplies the heavy machinery (rectangle integrals, primitives, Cauchy). The
genuinely new work is: the antiholomorphic-composition lemma (small), the across-`L`
Morera glue (the substance), and the bookkeeping/witness.

## Effort

Moderate, *not* multi-month — the substrate is strong. Recalibrated estimate (cf. the
project's Lean-time norms): a **focused 1–2 weeks** for the real-axis scalar version
including the residual-`sorry` tail. The general-arc/`E`-valued versions add more but are
optional for the covering.

## Fit as a Tau Ceti / Mathlib roadmap entry

Excellent fit. Tau Ceti (Lean FRO) is "basic material" complex analysis, AI-authored,
**axiom-clean** (`propext, Classical.choice, Quot.sound` only) — and this proof needs *no*
exotic axioms (pure Cauchy theory). It is reusable far beyond SW: the reflection principle
is a prerequisite for the **Riemann mapping theorem boundary regularity**, **Schwarz–
Christoffel**, the **modular/elliptic** uniformization, and analytic continuation generally.
A roadmap entry would be a `README.md` + `Targets.lean` with the signature above stated as a
`sorry`-goal, conventions pinned (real-axis first; `starRingEnd` for conjugation; witness
form), suggested home `…/Analysis/Complex/SchwarzReflection.lean`.

**Recommendation.** This is the right keystone to pursue upstream — small, self-contained,
genuinely new, and high-leverage (it unblocks our covering route *and* much else). It is a
better near-term investment than the full covering (which also needs `Γ(2)` geometry and
covering-Galois theory on top) and is independent of the Jacobi triple product. If pursued,
propose it to TauCetiRoadmap as above and implement against the Mathlib substrate listed.

A **draft roadmap entry** (README + `Targets.lean`, conventions pinned, signatures
elaborated against Mathlib) is in
[`../docs/tauceti-conformal-mapping/`](../docs/tauceti-conformal-mapping/) — Schwarz
reflection is its **L4** layer within the broader *conformal-mapping & geometric function
theory* area (summit: the Riemann mapping theorem), ready to propose to
`FormalFrontier/TauCetiRoadmap` as `TauCetiRoadmap/ConformalMapping/`.
