# Roadmap (draft): conformal mapping and the geometric theory of holomorphic functions

*A **draft Tau Ceti roadmap entry** we would propose to
[`FormalFrontier/TauCetiRoadmap`](https://github.com/FormalFrontier/TauCetiRoadmap) as
`TauCetiRoadmap/ConformalMapping/` (this `README.md` + `Targets.lean`). It lives in the
seiberg-witten repo as a working sketch (mirroring how `graphons/` keeps its roadmap
sketch): the modular-`λ` covering our SW project needs (`../../audit/COVERING_SCOPING.md`)
is one downstream application, but the area is general complex analysis that belongs
upstream. Written to the roadmap repo's conventions: build the library not the theorem,
ground everything in Mathlib, use Mathlib's vocabulary, pin conventions up front, write
Lean signatures.*

Mathlib has the **Cauchy foundations** of complex analysis — contour integration and the
Cauchy integral formula, power series / analyticity, the **open mapping theorem**
(`Complex.AnalyticOnNhd.is_constant_or_isOpenMap`), the **maximum modulus principle**
(`Analysis/Complex/AbsMax`), the **Schwarz lemma** (`Analysis/Complex/Schwarz`), the
**Riemann removable-singularity** theorem, the rectangle-integral vanishing lemmas, the unit
disc `Complex.UnitDisc`, `conjCLE`/`starRingEnd ℂ` — but **almost none of the geometric /
boundary superstructure built on them**: no argument principle, no Rouché or Hurwitz, no
Morera as a named theorem, no normal families / Montel, **no Riemann mapping theorem**, no
Schwarz reflection, no Carathéodory boundary correspondence, no Schwarz–Christoffel, no
Schwarz–Pick / hyperbolic metric, no analytic continuation / monodromy theorem.

The goal is to **build that geometric theory as a reusable library**, with the **Riemann
mapping theorem** (RMT) as the summit. "Done" means a researcher in conformal geometry,
several-complex-variables, modular forms, or PDE finds the objects — conformal
isomorphisms, normal families, the reflected continuation, the boundary correspondence — at
their natural generality with full basic API, so RMT and its boundary regularity are
*consequences of a developed theory*, not isolated endpoints.

Suggested home: `TauCeti/Analysis/Complex/Conformal/` (with
`…/Conformal/ArgumentPrinciple.lean`, `…/NormalFamilies.lean`, `…/RiemannMapping.lean`,
`…/Reflection.lean`, `…/BoundaryCorrespondence.lean`).

## Prior art

- **Mathlib:** none of the layer summits below (RMT, reflection, Rouché, Montel, …) are
  present; only the foundations listed above. (`Analysis/Complex/Schwarz.lean` is the
  Schwarz *lemma*, not the reflection *principle*.)
- **Isabelle/HOL:** the **Riemann mapping theorem is formalized** (Paulson, `Riemann_Mapping`
  in `HOL-Complex_Analysis`), so RMT is *achievable* — Lean simply lacks it. The reflection
  principle and Schwarz–Christoffel appear unformalized in Lean and were not found in a
  search of other provers. So this area ports/re-proves RMT into Lean and adds genuinely new
  material on top.

## Generality bar (decide up front; do not silently specialize)

- **Scalar `ℂ`, the geometric (one-complex-variable) theory.** RMT and the boundary theory
  are `ℂ`-specific; state them for `f : ℂ → ℂ`. The few layer-0 lemmas that are naturally
  `E`-valued (reflection, parts of the maximum principle) may be stated over a complex Banach
  `E`, flagged as such, but the spine is `ℂ`.
- **Domains: open + connected, simple-connectivity via Mathlib.** Use `IsOpen`,
  `IsConnected`/`IsPreconnected`, and `SimplyConnectedSpace ↥Ω` (Mathlib's class) — never an
  ad hoc "no holes". RMT's hypotheses are: `Ω` open, simply connected, `Ω ≠ univ`, nonempty.
- **Conformal isomorphism = holomorphic bijection.** A biholomorphism `Ω ≃ Ω'` is a
  `DifferentiableOn ℂ` bijection with `DifferentiableOn ℂ` inverse; since holomorphic +
  injective ⇒ open with holomorphic inverse (open mapping), state RMT's conclusion as
  `∃ f, DifferentiableOn ℂ f Ω ∧ Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1` and derive the
  packaged `≃` / `ConformalAt` API as companions. Relate to Mathlib's `ConformalAt`.
- **Target disc: `Complex.UnitDisc` / `Metric.ball (0:ℂ) 1`.** Reuse the existing disc and
  its automorphism/`Schwarz` API; do not re-encode the disc.
- **Convergence of holomorphic families: `TendstoLocallyUniformlyOn`** (compact-open), the
  topology under which "holomorphic" is closed and Montel lives. Local boundedness =
  "bounded on each compact `K ⊆ Ω`".
- **Reflection: real-axis first; conjugation is `starRingEnd ℂ`; explicit witness.** See L4.

## Layers (each a discharge-gated milestone; `sorry` in `Targets.lean` is the goal)

- **L0 — the local-mapping engine.** *Argument principle* (zero/pole count `= (2πi)⁻¹ ∮ f'/f`)
  → *Rouché* → *Hurwitz* (locally-uniform limits of zero-free maps are zero-free or `≡ 0`).
  *Morera* as a named theorem and the maximum-modulus corollaries packaged. The open mapping
  theorem and `AbsMax` are **consumed**; this layer is the counting/perturbation API on top.
- **L1 — normal families / Montel.** Locally bounded ⇒ precompact for
  `TendstoLocallyUniformlyOn` (every sequence has a locally-uniformly-convergent subsequence
  with holomorphic limit); Vitali. The compactness engine RMT runs on.
- **L2 — Schwarz lemma extensions.** *Schwarz–Pick* (holomorphic disc self-maps contract the
  pseudo-hyperbolic metric), the **hyperbolic / Poincaré metric** on `𝔻`, and the disc
  automorphism group `Aut(𝔻) = {e^{iθ}(z−a)/(1−āz)}`. Built on Mathlib's Schwarz lemma.
- **L3 — the Riemann mapping theorem (summit).** Every simply connected proper open
  `Ω ⊊ ℂ` (nonempty) is biholomorphic to `𝔻`. Standard route: the family of injective
  holomorphic `Ω → 𝔻` fixing a point is nonempty (square-root trick on simple-connectivity)
  and normal (L1); maximize `|f′(z₀)|`; the maximizer is onto (else compose with a disc
  automorphism + square root to beat it — L2). Uniqueness up to `Aut(𝔻)`.
- **L4 — analytic continuation & the reflection principle.** Morera-based **Schwarz
  reflection** across `ℝ` (witness `F z = if 0 ≤ z.im then f z else conj (f (conj z))`),
  then across an analytic arc / circle by Möbius reduction; **Painlevé removability** across
  an arc; the **monodromy theorem** (continuations along homotopic paths agree). Reflection's
  reflected branch needs the antiholomorphic-composition lemma (L4.0). *This is the layer the
  SW modular-`λ` covering consumes.*
- **L5 — Carathéodory boundary correspondence.** The RMT map of a Jordan domain extends to a
  homeomorphism of closures; prime ends in general. Uses L4 (reflection) for analytic
  boundary arcs.
- **L6 (stretch) — Schwarz–Christoffel.** Explicit conformal maps onto polygons, built on
  L4 + L5.

## Downstream / applications

- **Modular & elliptic uniformization** — the `ℍ/Γ(2) ≅ ℂ∖{0,1}` covering (`λ`-function) is
  L4 (reflection) + L5 + the existing
  [`TauCetiRoadmap/UniversalCovers`](https://github.com/FormalFrontier/TauCetiRoadmap) deck-group
  milestone; this is the SW project's `audit/COVERING_SCOPING.md` target. The `j`-invariant and
  Picard's theorem follow.
- **Several complex variables, PDE (conformal/quasiconformal), special functions** all consume
  the conformal-mapping and boundary layers.

## References

Ahlfors, *Complex Analysis* (Ch. 4–6) and *Conformal Invariants*; Conway, *Functions of One
Complex Variable I* (VII–IX); Rudin, *Real and Complex Analysis* (Ch. 14); Stein–Shakarchi,
*Complex Analysis* (Ch. 2, 8); Remmert, *Classical Topics in Complex Function Theory*. RMT:
cf. Paulson's Isabelle/HOL `Riemann_Mapping`. New Lean formalization; credit none — original.
