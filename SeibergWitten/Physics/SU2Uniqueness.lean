/-
# SU(2) uniqueness in `SymplecticReframing` form — Step C of `audit/SU2_UNIQUENESS_SCOPING.md`

Given that two SU(2) sheets have **period vectors related by an `SL(2,ℤ)` frame** (det 1) on
their overlap, we build the duality `SymplecticReframing` between them: the contragredient `Sp(2,ℤ)` action on
the charge lattice, with the central charge `Z = nₑ a + n_m a_D` covariant (so `|Z|` and the
metric descend) — both derived from `det = 1`.

This is the genuine linear-algebra core of closing the rank-1 headline
`sw_effective_theory_unique_up_to_duality`: it shows **period frame ⇒ `SymplecticReframing`**, with footprint
standard-3 (no axioms). The remaining link — **same monodromy ⇒ period frame** — is the
rigidity step (`su2_frame_alignment`, modulo the period-vs-coupling scale lift) plus the
monodromy layer; see the scoping doc.
-/
import SeibergWitten.Physics.Hypotheses
import Mathlib

namespace SeibergWitten.Physics.SU2

open SeibergWitten.Physics

variable {B : PeriodBase 1}

/-- The `SL(2,ℤ)`-contragredient action on the rank-1 charge lattice for a period frame
`(α,β;γ,δ)` of determinant 1: `g(nₑ,n_m) = (δ nₑ − γ n_m, −β nₑ + α n_m)`, a ℤ-linear
automorphism (inverse `(α nₑ + γ n_m, β nₑ + δ n_m)`). -/
noncomputable def su2DualityMap (α β γ δ : ℤ) (hdet : α * δ - β * γ = 1) :
    CycleLattice 1 ≃ₗ[ℤ] CycleLattice 1 :=
  LinearEquiv.ofLinear
    { toFun := fun n => (fun _ => δ * n.1 0 - γ * n.2 0, fun _ => -β * n.1 0 + α * n.2 0)
      map_add' := by intro m n; ext i <;> fin_cases i <;> simp <;> ring
      map_smul' := by intro c n; ext i <;> fin_cases i <;> simp <;> ring }
    { toFun := fun n => (fun _ => α * n.1 0 + γ * n.2 0, fun _ => β * n.1 0 + δ * n.2 0)
      map_add' := by intro m n; ext i <;> fin_cases i <;> simp <;> ring
      map_smul' := by intro c n; ext i <;> fin_cases i <;> simp <;> ring }
    (by
      refine LinearMap.ext fun n => Prod.ext ?_ ?_
      · funext i; fin_cases i
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.id_coe, id_eq, Fin.zero_eta, Fin.isValue]
        linear_combination (n.1 0) * hdet
      · funext i; fin_cases i
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.id_coe, id_eq, Fin.zero_eta, Fin.isValue]
        linear_combination (n.2 0) * hdet)
    (by
      refine LinearMap.ext fun n => Prod.ext ?_ ?_
      · funext i; fin_cases i
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.id_coe, id_eq, Fin.zero_eta, Fin.isValue]
        linear_combination (n.1 0) * hdet
      · funext i; fin_cases i
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.id_coe, id_eq, Fin.zero_eta, Fin.isValue]
        linear_combination (n.2 0) * hdet)

@[simp] theorem su2DualityMap_fst (α β γ δ : ℤ) (hdet : α * δ - β * γ = 1) (n : CycleLattice 1) :
    (su2DualityMap α β γ δ hdet n).1 0 = δ * n.1 0 - γ * n.2 0 := rfl

@[simp] theorem su2DualityMap_snd (α β γ δ : ℤ) (hdet : α * δ - β * γ = 1) (n : CycleLattice 1) :
    (su2DualityMap α β γ δ hdet n).2 0 = -β * n.1 0 + α * n.2 0 := rfl

/-- **Step C — period frame ⇒ duality `SymplecticReframing`.** If on the overlap the periods of `s'` are the
`(α,β;γ,δ)`-frame transform of those of `s` (determinant 1), the two SU(2) sheets are glued by
an `Sp(2,ℤ)` deck transformation: the contragredient charge action is symplectic (from `det=1`)
and the central charge is covariant (the period and charge actions cancel). Footprint
standard-3. -/
theorem su2_deck_of_periodFrame (s s' : PeriodChart B)
    (α β γ δ : ℤ) (hdet : α * δ - β * γ = 1)
    (hper : ∀ u ∈ s.V ∩ s'.V,
      s'.a u 0 = α * s.a u 0 + β * s.aD u 0 ∧
      s'.aD u 0 = γ * s.a u 0 + δ * s.aD u 0) :
    Nonempty (SymplecticReframing s s') := by
  have hdetC : (α : ℂ) * δ - β * γ = 1 := by exact_mod_cast hdet
  refine ⟨{ g := su2DualityMap α β γ δ hdet, symplectic := ?_, covariant := ?_ }⟩
  · intro n n'
    simp only [intersectionForm, Fin.sum_univ_one, su2DualityMap_fst, su2DualityMap_snd]
    linear_combination (n.1 0 * n'.2 0 - n.2 0 * n'.1 0) * hdet
  · intro u hu n
    obtain ⟨ha, haD⟩ := hper u hu
    simp only [PeriodChart.periodCombination, Fin.sum_univ_one, su2DualityMap_fst, su2DualityMap_snd]
    rw [ha, haD]; push_cast
    linear_combination (n.1 0 : ℂ) * s.a u 0 * hdetC + (n.2 0 : ℂ) * s.aD u 0 * hdetC
