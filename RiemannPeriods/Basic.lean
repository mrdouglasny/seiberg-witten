import Mathlib

/-!
# RiemannPeriods — weight-1 VHS targets (validating the SW period axioms)

Bootstrap of the period-geometry library that is to discharge `periodRigidityAxiom` /
`matterPeriodRigidityAxiom` (see `audit/RIEMANN_PERIODS_SCOPE.md` and
`audit/JACOBIAN_DEPENDENCY_EVAL.md`). The point here is to **state the content of the period
axioms** — what `periodRigidityAxiom` asserts about the periods — as well-typed, SW-agnostic VHS goals
over a curve family, so we can see they are real, non-vacuous targets and start discharging them.
Genus-1 (elliptic) first; `Siegel 1 ≃ ℍ`, so the polarization is just `Im τ > 0`.

Status of the period content of `periodRigidityAxiom`, validated here:
* **L2 (Gauss–Manin / period map holomorphic)** — `tau_differentiableOn`, **proved** (reduces to the
  periods' holomorphy; prototyped by `Genus1Periods.swPeriodSeg_hasDerivAt`).
* **L3 (Riemann bilinear / `Im τ > 0`)** — `tau_im_pos`, **proved** from the polarization field
  `riemann`. `periodMap : U → ℍ` assembles L2 + L3.

The abstract interface is **sorry-free**. The remaining debt is the **geometric construction**:
building `WeightOnePeriods` from an actual curve so that `riemann` (and `a_ne_zero`, the holomorphy)
are *theorems*, not fields.

Wiring note (2026-06-29, re "prove all using jacobian-claude"): jacobian-claude shares our toolchain
+ Mathlib pin (`c5ea0035`) and proves the per-fibre period lattice **axiom-free**, but
(i) its lib is also named `Jacobians`, so it **cannot be co-required** alongside jacobian-challenge
in this package — using it needs `RiemannPeriods` as a *separate* package (or swapping
jacobian-challenge out); and (ii) it has **no Riemann-bilinear / `Im τ > 0`** result (only the
lattice ⇒ `Im τ ≠ 0`, not `> 0`). So `riemann` (L3) must be built via the Hodge-star positivity
path regardless of the Jacobian library.

Main definitions: `WeightOnePeriods`, `WeightOnePeriods.tau`, `WeightOnePeriods.periodMap`.
-/

namespace RiemannPeriods

open Complex

variable {U : Set ℂ}

/-- **Weight-1 period data** of a genus-1 curve family over a base `U ⊆ ℂ` (the SW Coulomb branch
minus its discriminant locus): holomorphic period functions `a, a_D` (the periods `∮ ω` over an A/B
cycle basis of the fibre) with `a` nonvanishing. This is the data `periodRigidityAxiom` packages; in the
full library it is *constructed* from jacobian-claude's per-fibre periods together with the
Gauss–Manin variation over `U`. -/
structure WeightOnePeriods (U : Set ℂ) where
  /-- the period `a(u) = ∮_A ω` -/
  a : ℂ → ℂ
  /-- the dual period `a_D(u) = ∮_B ω` -/
  aD : ℂ → ℂ
  ha : DifferentiableOn ℂ a U
  haD : DifferentiableOn ℂ aD U
  a_ne_zero : ∀ u ∈ U, a u ≠ 0
  /-- **Riemann bilinear positivity (the weight-1 polarization).** `0 < Im(ā·a_D)` — this is
  `(i/2)∮ ω ∧ ω̄ > 0` for the dual A/B cycle basis (intersection number `1`). The genuine geometric
  input; it pins the period ratio to the upper half plane and is what the full library proves from
  the cut-surface Hodge-star positivity. -/
  riemann : ∀ u ∈ U, 0 < ((starRingEnd ℂ) (a u) * aD u).im

/-- The **coupling / period map** `τ(u) = a_D(u) / a(u)` — the genus-1 period map into
`ℍ = Siegel 1`. -/
noncomputable def WeightOnePeriods.tau (P : WeightOnePeriods U) (u : ℂ) : ℂ := P.aD u / P.a u

/-- **L2 — the period map is holomorphic (Gauss–Manin).** The coupling varies holomorphically over
the smooth locus. This *reduces to* the holomorphy of the periods (the structure data): the genuine
content is `ha`/`haD`, prototyped at genus 1 by `Genus1Periods.swPeriodSeg_hasDerivAt`. So the
holomorphy half of `periodRigidityAxiom`'s period geometry is **not** axiomatic — it is here a theorem. -/
theorem tau_differentiableOn (P : WeightOnePeriods U) : DifferentiableOn ℂ P.tau U :=
  P.haD.div P.ha P.a_ne_zero

/-- **L3 — Riemann bilinear (`g = 1`): `Im τ(u) > 0`.** The period ratio lands in the upper half
plane `ℍ = Siegel 1` (the special-Kähler / no-ghost positivity). **Proved** from the polarization
`riemann`: `Im(a_D/a) = Im(ā·a_D)/|a|² > 0`. So `τ ∈ ℍ` is *not* axiomatic — it reduces to the
Riemann-bilinear positivity, the genuine geometric input. -/
theorem tau_im_pos (P : WeightOnePeriods U) (u : ℂ) (hu : u ∈ U) : 0 < (P.tau u).im := by
  have hN : 0 < Complex.normSq (P.a u) := Complex.normSq_pos.mpr (P.a_ne_zero u hu)
  have key : (P.tau u).im
      = ((starRingEnd ℂ) (P.a u) * P.aD u).im / Complex.normSq (P.a u) := by
    rw [WeightOnePeriods.tau, Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
  rw [key]
  exact div_pos (P.riemann u hu) hN

/-- **The period map into the Siegel upper half space** (`Siegel 1 = ℍ`): `u ↦ τ(u) ∈ ℍ`. Assembles
L2 (holomorphy, `tau_differentiableOn`) and L3 (the polarization lands `τ` in `ℍ`, `tau_im_pos`)
into the genus-1 weight-1 VHS period map — the object `periodRigidityAxiom` ultimately provides. -/
noncomputable def WeightOnePeriods.periodMap (P : WeightOnePeriods U) (u : U) : UpperHalfPlane :=
  ⟨P.tau u.1, tau_im_pos P u.1 u.2⟩

end RiemannPeriods
