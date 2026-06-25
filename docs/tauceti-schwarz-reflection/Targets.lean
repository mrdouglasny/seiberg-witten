import Mathlib

/-!
# Schwarz reflection principle: target signatures

The narrative roadmap (proof route, generality bar, references, downstream uses) is in
`README.md`. Mathlib has the Cauchy-theory substrate — the rectangle-integral vanishing
lemma `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`,
`Analysis/Complex/HasPrimitives`, the point Riemann removable-singularity theorem,
`conjCLE`/`starRingEnd ℂ`, the open mapping theorem — but **not** the reflection principle
(`Analysis/Complex/Schwarz.lean` is the Schwarz *lemma*). We build it in
`TauCeti/Analysis/Complex/SchwarzReflection.lean`.

These are stated with `sorry` (allowed in this human-owned roadmap library); what lands in
`TauCeti/` must be fully proved with only the three kernel axioms. Conventions are pinned in
`README.md`: real-axis scalar case first; conjugation is `starRingEnd ℂ`; the extension is
the explicit witness `F z = if 0 ≤ z.im then f z else conj (f (conj z))`.

NOTE: drafted against Mathlib as of the seiberg-witten toolchain; re-elaborate against
`TauCetiRoadmap`'s pinned Mathlib (lean4 v4.31) when filing.
-/

namespace TauCetiRoadmap.SchwarzReflection

open Complex

/-- **Layer 0 — antiholomorphic composition.** If `f` is `ℂ`-differentiable on a set `S`,
then `z ↦ conj (f (conj z))` is `ℂ`-differentiable on the conjugate set `conj '' S`
(antiholomorphic ∘ holomorphic ∘ antiholomorphic = holomorphic). The micro-lemma underlying
the reflected branch of the witness; a few lines from `conjCLE` and the chain rule. -/
example {f : ℂ → ℂ} {S : Set ℂ} (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) '' S) :=
  sorry

/-- **Layer 1 — the Schwarz reflection principle (real axis).** Let `Ω` be open and
conjugation-symmetric. If `f` is continuous on the closed upper part `Ω ∩ {im ≥ 0}`,
holomorphic on the open upper part `Ω ∩ {im > 0}`, and real on `L = Ω ∩ ℝ`, then `f` extends
to a function holomorphic on all of `Ω` that agrees with `f` on the closed upper part and
satisfies the reflection symmetry `F (conj z) = conj (F z)`.

The extension is the explicit witness
`F z = if 0 ≤ z.im then f z else conj (f (conj z))`. Proof route (Morera): `F` is continuous
on `Ω` (the branches agree on `L` since `f` is real there) and holomorphic off `L`; its
boundary integral over every rectangle vanishes (split at `L`, each half a limit of
sub-rectangles where `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`
applies), so `F` has local primitives (`HasPrimitives`) and is holomorphic. -/
example {Ω : Set ℂ} (hΩ : IsOpen Ω) (hsymm : ∀ z, z ∈ Ω ↔ (starRingEnd ℂ) z ∈ Ω)
    {f : ℂ → ℂ}
    (hcont : ContinuousOn f (Ω ∩ {z | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F Ω ∧
      Set.EqOn F f (Ω ∩ {z | 0 ≤ z.im}) ∧
      ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z) :=
  sorry

/-- **Layer 1, witness form.** The same conclusion, pinning the extension to the explicit
witness so downstream users get the formula, not just existence. (Equivalent to the above;
stated separately because the witness is the convention to standardize on.) -/
example {Ω : Set ℂ} (hΩ : IsOpen Ω) (hsymm : ∀ z, z ∈ Ω ↔ (starRingEnd ℂ) z ∈ Ω)
    {f : ℂ → ℂ}
    (hcont : ContinuousOn f (Ω ∩ {z | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    DifferentiableOn ℂ
      (fun z => if 0 ≤ z.im then f z else (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) Ω :=
  sorry

end TauCetiRoadmap.SchwarzReflection
