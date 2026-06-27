import Mathlib

/-!
# Variation of Hodge structure / periods of families of curves: target signatures

The narrative roadmap (layers, generality bar, conventions, references, downstream uses, and the
relation to the `jacobian-challenge` per-fiber library and the sibling `ContourIntegration` /
`ModularForms` / `ConformalMapping` roadmaps) is in `README.md`.

The per-fiber theory exists in `jacobian-challenge` (single-curve periods, period matrix +
Riemann-bilinear positivity, hyperelliptic curves, `AbelianVariety.{Siegel, Theta}`). Mathlib has
the analytic backbone (differentiation under the integral, `ℍ`, the modular group, `Matrix.PosDef`,
`Matrix.SpecialLinearGroup`). What is missing — everywhere — is the **family/variation** layer:
how the periods vary with the parameter. We build it in `TauCeti/Geometry/VHS/`.

A representative milestone from each layer is stated below with `sorry` (allowed in this
human-owned roadmap library); what lands in `TauCeti/` must be proved with only the three kernel
axioms. The per-fiber periods, Jacobian, and `Siegel`/`Theta` are **consumed** from
`jacobian-challenge`, not re-derived; the contour integrals `∮` consume the `ContourIntegration`
roadmap (PR #35). The genus-1 case is the proved anchor (`swEllipticData_genus`,
`model_period_differentiable` in the seiberg-witten repo).

Conventions (pinned in `README.md`): weight-1 (curves); base `U` open in `ℂ^r`, smooth locus
`U = Δᶜ`; period vector `(∮_{A_i} ω, ∮_{B_i} ω)`; normalized period matrix `τ = (∮_B ω)(∮_A ω)⁻¹`;
period domain `Siegel g`; duality group `Sp(2g, ℤ)`; Picard–Lefschetz transvection
`v ↦ v + ⟨v, δ⟩ δ`.

NOTE: drafted/elaborated against the seiberg-witten toolchain's Mathlib; re-elaborate against
`TauCetiRoadmap`'s pinned Mathlib when filing.
-/

namespace TauCetiRoadmap.VHS

open Complex Filter Topology MeasureTheory Matrix

/-- **L0 — the period map is holomorphic (P1).** The period `u ↦ ∫_γ F(u, ·)` of a holomorphic
family of integrands over a fixed contour is holomorphic in the parameter `u`. (Joint continuity +
holomorphy in `u` on a compact contour gives the local domination via Cauchy estimates.) Proved
for a model integrand in the seiberg-witten repo (`model_period_differentiable`); the library task
is the clean general lemma and the Seiberg–Witten integrand `((x²−u)²−Λ⁴)^(−1/2)`. -/
example {a b : ℝ} (F : ℂ → ℝ → ℂ)
    (hcont : Continuous (Function.uncurry F))
    (hholo : ∀ t, Differentiable ℂ (fun u => F u t)) :
    Differentiable ℂ (fun u => ∫ t in a..b, F u t) :=
  sorry

/-- **L1 — Gauss–Manin / Picard–Fuchs (P2).** The two periods of a genus-1 family satisfy a
*common* second-order linear ODE in the parameter (the Picard–Fuchs equation) — they span the
solution space of the Gauss–Manin connection. (The content is the shared `p, q`: a single
function cannot be the witness.) -/
example {U : Set ℂ} (a aD : ℂ → ℂ)
    (ha : DifferentiableOn ℂ a U) (haD : DifferentiableOn ℂ aD U) :
    ∃ p q : ℂ → ℂ, ∀ u ∈ U,
      (deriv (deriv a) u + p u * deriv a u + q u * a u = 0) ∧
      (deriv (deriv aD) u + p u * deriv aD u + q u * aD u = 0) :=
  sorry

/-- **L2 — the period map lands in Siegel (P3).** From Riemann's first bilinear relation
(`Aᵀ B = Bᵀ A`) and invertibility of the A-period matrix, the normalized period matrix
`τ = B A⁻¹` is symmetric; with the second bilinear relation (`Im τ ≻ 0`) the period map is a
holomorphic `U → Siegel g`. (Per-fiber positivity is `jacobian-challenge`'s; the family statement
is `τ : U → Siegel g` holomorphic.) -/
example {g : ℕ} (PA PB : Matrix (Fin g) (Fin g) ℂ) (hA : IsUnit PA.det)
    (hbil : PAᵀ * PB = PBᵀ * PA) :
    (PB * PA⁻¹).IsSymm :=
  sorry

/-- **L3 — Picard–Lefschetz monodromy is symplectic (P4).** The local monodromy around a
discriminant component is the transvection `v ↦ v + ⟨v, δ⟩ δ` in the vanishing cycle `δ`, and it
preserves the (antisymmetric) intersection form — so the monodromy representation lands in
`Sp(2g, ℤ)`. (Proved at rank 1 in the seiberg-witten repo as `transvection_isSymplectic`; the
library task is the general statement and tying it to analytic continuation around `Δ`.) -/
example {V : Type*} [AddCommGroup V] (ω : V → V → ℤ) (δ : V)
    (hanti : ∀ v w, ω v w = - ω w v)
    (hbilin : ∀ v w x, ω (v + w) x = ω v x + ω w x)
    (hsmul : ∀ (n : ℤ) (v x : V), ω (n • v) x = n * ω v x)
    (T : V → V) (hT : ∀ v, T v = v + (ω v δ) • δ) :
    ∀ v w, ω (T v) (T w) = ω v w :=
  sorry

/-- **L4 — period-map rigidity (P5, the summit for applications).** If the monodromy
representation is irreducible, two period maps over the same base with the *same* monodromy are
related by a single constant `Sp(2g, ℤ)` frame (Schur's lemma forces the centralizer element to a
scalar; a normalization fixes it). This is the `rigidity` field of the Seiberg–Witten period
layer; its genus-1 instance is the developing-map rigidity of the `ConformalMapping` roadmap. The
`SameMonodromy`/irreducibility/normalization hypotheses are abstracted here as `hyp`. -/
example {g : ℕ} {U : Set ℂ} (a a' : ℂ → (Fin (2 * g) → ℂ)) (hyp : Prop) (h : hyp) :
    ∃ M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ,
      ∀ u ∈ U, a' u = (M.map (fun n => (n : ℂ))) *ᵥ a u :=
  sorry

end TauCetiRoadmap.VHS
