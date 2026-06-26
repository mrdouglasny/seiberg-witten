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

open Matrix Complex Jacobians.AbelianVariety

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

variable {Δ : Set (Fin 1 → ℂ)}

/-- **H4′ — electric–magnetic duality, a physical refinement of H4 (`EMDualityConsistent`).**
The values of the multivalued effective coupling are closed under the `Sp(2,ℤ) = SL(2,ℤ)`
duality action: every duality frame-change of a coupling value is again realized as a coupling
value on some sheet of the universal cover. This is the concrete content of "the monodromy is
by electric–magnetic duality", stated directly on the data — more physical than the abstract
`EMDualityConsistent`, which it is intended to imply. -/
def H4'Duality (d : LowEnergyData 1 Δ) : Prop :=
  ∀ (M : Sp2ℤ) (p : SmoothCover Δ), ∃ q : SmoothCover Δ, d.tau q = M • d.tau p

/-- **H4′ ⇒ positivity is monodromy-stable (the special-geometry consequence).** Assuming
electric–magnetic duality (`H4'Duality`), every duality frame-change `M • τ(p)` of the
coupling is realized by an actual sheet `q` of the cover, and that sheet carries a
positive-definite special-Kähler metric (`Im τ ≻ 0`). So the no-ghost positivity holds on the
whole duality orbit: although `τ` is multivalued, its metric is positive everywhere it is
defined — a globally consistent positive metric on the Coulomb branch. (With
`sw_metric_posDef`, which gives positivity at the base point, this closes the loop.) -/
theorem metric_posDef_of_h4' (d : LowEnergyData 1 Δ) (h : H4'Duality d)
    (M : Sp2ℤ) (p : SmoothCover Δ) :
    ∃ q : SmoothCover Δ,
      d.tau q = M • d.tau p ∧ ((d.tau q).val.map Complex.im).PosDef := by
  obtain ⟨q, hq⟩ := h M p
  exact ⟨q, hq, (d.tau q).imPosDef⟩

end SeibergWitten.Physics
