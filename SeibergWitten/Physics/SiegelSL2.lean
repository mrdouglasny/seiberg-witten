/-
# The `g = 1` Sp-action on the Siegel space (built on Mathlib's `ℍ` action)

The VHS layer (`VHS.lean`) needs the `Sp(2g,ℤ)` action on `SiegelUpperHalfSpace g` to
state `ρ`-equivariance of the period map. For `g = 1` this is *reachable now*, because:

* `Sp(2,ℤ) = SL(2,ℤ)` (the rank-1 symplectic group is the special linear group), and
* `SiegelUpperHalfSpace 1 ≃ ℍ` (a `1×1` symmetric complex matrix with positive-definite
  imaginary part is just a point of the upper half plane), and
* Mathlib already has the `SL(2,ℝ)`-action on `ℍ` (`UpperHalfPlane.SLAction`), hence the
  `SL(2,ℤ)`-action.

So we build the `g = 1` action by **transporting Mathlib's action across the
identification** — filling in two TODOs left in `jacobian-challenge`'s `Siegel.lean`
(the `Siegel 1 ≃ ℍ` bijection and the `Sp(2g,ℤ)`-action). This is the rank-1 foothold for
the general `Sp(2g,ℤ)`-on-Siegel action (target #1 of the VHS scoping) and feeds the
SU(2) rigidity gap `AX_su2_modular_frame_alignment`.

Everything here is proved (standard-3); the only new content is the identification and the
transported action.
-/
import SeibergWitten.Physics.VHS
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

namespace SeibergWitten.Physics

/-- A `1×1` real matrix is positive definite iff its single entry is positive. -/
theorem posDef_fin_one_real (M : Matrix (Fin 1) (Fin 1) ℝ) : M.PosDef ↔ 0 < M 0 0 := by
  set a := M 0 0 with ha
  have hM : M = Matrix.diagonal (fun _ : Fin 1 => a) := by
    ext i j; fin_cases i; fin_cases j; simp [Matrix.diagonal_apply_eq, ha]
  rw [hM, Matrix.posDef_diagonal_iff]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-- **`SiegelUpperHalfSpace 1 ≃ ℍ`.** A point of the rank-1 Siegel upper half space — a
`1×1` symmetric complex matrix with `Im ≻ 0` — is exactly its single entry, a point of the
upper half plane. (Fills the `g = 1` compatibility TODO in `jacobian-challenge`.) -/
noncomputable def siegelOneEquiv : SiegelUpperHalfSpace 1 ≃ UpperHalfPlane where
  toFun τ := ⟨τ.val 0 0, by
    have h := (posDef_fin_one_real _).mp τ.imPosDef
    simpa [Matrix.map_apply] using h⟩
  invFun z := ⟨Matrix.of (fun _ _ => (z : ℂ)), by
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i; fin_cases j; rfl
    · rw [posDef_fin_one_real]
      simpa [Matrix.map_apply, Matrix.of_apply] using z.coe_im_pos⟩
  left_inv τ := by
    apply SiegelUpperHalfSpace.ext
    ext i j; fin_cases i; fin_cases j; rfl
  right_inv z := by
    apply UpperHalfPlane.ext; rfl

/-- **The `g = 1` Sp-action on the Siegel space**: `Sp(2,ℤ) = SL(2,ℤ)` acts on
`SiegelUpperHalfSpace 1`, transported from Mathlib's `SL(2,ℝ)`-action on `ℍ` across
`siegelOneEquiv`. The fractional-linear action `τ ↦ (aτ+b)/(cτ+d)` realized on the Siegel
side. -/
noncomputable instance : MulAction (Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (SiegelUpperHalfSpace 1) where
  smul g τ := siegelOneEquiv.symm (g • siegelOneEquiv τ)
  one_smul τ := by
    change siegelOneEquiv.symm ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • siegelOneEquiv τ) = τ
    rw [one_smul, Equiv.symm_apply_apply]
  mul_smul g h τ := by
    change siegelOneEquiv.symm ((g * h) • siegelOneEquiv τ)
       = siegelOneEquiv.symm (g • siegelOneEquiv (siegelOneEquiv.symm (h • siegelOneEquiv τ)))
    rw [Equiv.apply_symm_apply, mul_smul]

/-- The action is the transported `ℍ` action: `siegelOneEquiv` is `SL(2,ℤ)`-equivariant.
This is what makes it usable as the `ρ`-equivariance target in a weight-1 VHS at `g = 1`. -/
theorem siegelOneEquiv_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (τ : SiegelUpperHalfSpace 1) :
    siegelOneEquiv (g • τ) = g • siegelOneEquiv τ :=
  siegelOneEquiv.apply_symm_apply _

end SeibergWitten.Physics
