/-
# H4′ ⇒ positivity: electric–magnetic duality preserves the special-Kähler metric

The physical hypothesis **H4** (`EMDualityConsistent`, `Hypotheses.lean`) says the
multivalued effective coupling `τ` has `Sp(2r,ℤ)` monodromy. That predicate is left abstract.
Here we record a **physical refinement** `H4'Duality` — the coupling's values are closed under
the duality action — and *derive its consequence for the special geometry*: the no-ghost
positivity of the special-Kähler metric `Im τ ≻ 0` (`sw_metric_posDef`) is stable along the
entire electric–magnetic duality orbit. So although `τ` is multivalued, every duality-related
sheet carries a positive-definite metric; the metric is globally consistent.

This is the "derive consequences for the special geometry from a physical version of the
axiom" programme (recommendation (1): keep H4 abstract, derive the *consequence*, add no
bridge axioms), carried out for `r = 1` on the proved `g = 1` `Sp`-action on the Siegel space
(`SiegelSL2.lean`). Everything here is **standard-3** (no new axioms).
-/
import SeibergWitten.Physics.SiegelSL2
import SeibergWitten.Physics.Hypotheses

open Matrix Complex

namespace SeibergWitten.Physics

/-- `Sp(2,ℤ) = SL(2,ℤ)`, the rank-1 electric–magnetic duality group. -/
local notation "Sp2ℤ" => Matrix.SpecialLinearGroup (Fin 2) ℤ

/-- **Duality preserves the special-Kähler metric (no-ghost positivity).** For any
electric–magnetic duality `M ∈ Sp(2,ℤ) = SL(2,ℤ)` and any rank-1 effective coupling `τ`, the
duality-transformed coupling `M • τ` again has positive-definite imaginary part — the no-ghost
condition `Im τ ≻ 0`. Positivity is preserved because the duality action is *typed into* the
Siegel space: it is Mathlib's `SL(2,ℝ)`-action on `ℍ` (with the explicit transformation law
`Im(M•τ) = Im τ / |cτ+d|² > 0`), transported across `siegelOneEquiv`. -/
theorem duality_preserves_metric_posDef (M : Sp2ℤ) (τ : SiegelUpperHalfSpace 1) :
    ((M • τ).val.map Complex.im).PosDef :=
  (M • τ).imPosDef

/-- The same positivity exhibited at the level of the upper half plane: the special-Kähler
metric `Im` of the duality-transformed coupling is positive, *via* the transported `ℍ`-action
(`siegelOneEquiv` is `SL(2,ℤ)`-equivariant). This is the concrete mechanism behind
`duality_preserves_metric_posDef`. -/
theorem siegelOne_smul_im_pos (M : Sp2ℤ) (τ : SiegelUpperHalfSpace 1) :
    0 < (siegelOneEquiv (M • τ)).im := by
  rw [siegelOneEquiv_smul]
  exact (M • siegelOneEquiv τ).2

variable {B : PeriodBase 1}

/-- **H4′ — the duality monodromy acts on the coupling (genuine `π₁ → Sp(2,ℤ)` form).** For the
deck gluing `D : SymplecticReframing s s'` — the rank-1 monodromy relating two overlapping sheets — there is an
`M ∈ Sp(2,ℤ) = SL(2,ℤ)` realizing its action on the effective coupling: `τ' = M • τ` on the
overlap. This is the concrete content of "the monodromy is electric–magnetic duality", attached
to an actual gluing, not mere image-closure under all of `SL(2,ℤ)`. -/
def H4'Duality {s s' : PeriodChart B} (_D : SymplecticReframing s s') : Prop :=
  ∃ M : Sp2ℤ, ∀ u ∈ s.V ∩ s'.V, s'.tau u = M • s.tau u

/-- **H4′ ⇒ positivity is monodromy-stable (the special-geometry consequence).** Under the
duality monodromy, the special-Kähler metric stays positive: the glued coupling
`s'.τ(u) = M • s.τ(u)` lands in the Siegel space (`Im τ ≻ 0`). So the no-ghost positivity is
duality-invariant — although `τ` is multivalued across sheets, its metric is positive on every
sheet, a globally consistent positive metric on the Coulomb branch. -/
theorem metric_posDef_of_h4' {s s' : PeriodChart B} (D : SymplecticReframing s s') (h : H4'Duality D)
    {u : Fin 1 → ℂ} (hu : u ∈ s.V ∩ s'.V) :
    ∃ M : Sp2ℤ,
      s'.tau u = M • s.tau u ∧ ((s'.tau u).val.map Complex.im).PosDef := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, hM u hu, (s'.tau u).imPosDef⟩

end SeibergWitten.Physics
