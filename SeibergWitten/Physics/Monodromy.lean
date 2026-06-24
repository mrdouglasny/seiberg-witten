/-
# The monodromy layer — scoping (Phase 3/4)

The `Sp(2r,ℤ)` monodromy of the SW family is what both open gaps need: the
"no-too-many-singularities" budget (`SU2Singularities.lean`) and the SU(2) rigidity
uniformization (`SU2Rigidity.lean`, `AX_su2_modular_frame_alignment`). This file scopes
it: it **proves** the algebraic core and isolates the topological/family inputs.

## What is proved here (column 1)

The charge lattice `ChargeLattice r = ℤ^r × ℤ^r` carries the Dirac pairing `diracPairing`
(`Physics/Hypotheses.lean`) — the symplectic form `H₁` inherits as the intersection
form. The **Picard–Lefschetz transvection** of a vanishing charge `γ`,
`T_γ : v ↦ v + ⟨v,γ⟩ γ`, is the local monodromy around a singularity where the BPS state
`γ` goes massless. We prove:

* `diracPairing` is `ℤ`-bilinear, antisymmetric, and alternating (`diracPairing_self`);
* **`transvection_isSymplectic`**: every transvection preserves `diracPairing` — so the
  monodromy lands in `Sp(2r,ℤ)`. This is the algebraic reason the monodromy
  representation is symplectic, proved (standard-3), no family/topology needed.

## What is scoped (the gaps)

* **The monodromy representation of the family.** `π₁(U)` (`U = moduli ∖ Δ`) acting on
  `H₁` of the fibre via the Gauss–Manin connection / local system. Needs a
  family/variation layer over the base — *not yet present* in `jacobian-challenge`
  (which has `H₁` and `π₁` of a *single* surface, not of a family).
* **Picard–Lefschetz identification.** That the *local* monodromy around a generic
  component of `Δ` *equals* `T_γ` for the vanishing charge `γ`. A topological theorem
  (Picard–Lefschetz) — isolated as `AX_picard_lefschetz_local`.

Once these land, `EMDualityConsistent` / `PicardLefschetzAtGenericSingularities`
(`Hypotheses.lean`) get real content, the SU(2) "no-too-many" budget becomes
`M_∞ = ∏ T_{γ_i}` (a relation in `Sp(2,ℤ)`), and `AX_su2_modular_frame_alignment`'s
monodromy hypothesis is discharged.

References: Seiberg–Witten, hep-th/9407087 §3–4; Lerche, hep-th/9611190 §3; Picard–
Lefschetz theory (vanishing cycles, transvections).
-/
import SeibergWitten.Physics.Hypotheses

open Finset

namespace SeibergWitten.Physics

variable {r : ℕ}

/-! ## `diracPairing` is an alternating `ℤ`-bilinear form -/

theorem diracPairing_self (v : ChargeLattice r) : diracPairing v v = 0 := by
  unfold diracPairing
  rw [sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem diracPairing_antisymm (a b : ChargeLattice r) :
    diracPairing a b = -diracPairing b a := by
  unfold diracPairing
  have h1 : ∑ i, a.1 i * b.2 i = ∑ i, b.2 i * a.1 i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : ∑ i, a.2 i * b.1 i = ∑ i, b.1 i * a.2 i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1, h2]; ring

theorem diracPairing_add_left (a b c : ChargeLattice r) :
    diracPairing (a + b) c = diracPairing a c + diracPairing b c := by
  simp only [diracPairing, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

theorem diracPairing_smul_left (c : ℤ) (a b : ChargeLattice r) :
    diracPairing (c • a) b = c * diracPairing a b := by
  simp only [diracPairing, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub]

theorem diracPairing_add_right (a b c : ChargeLattice r) :
    diracPairing a (b + c) = diracPairing a b + diracPairing a c := by
  rw [diracPairing_antisymm a (b + c), diracPairing_add_left,
      diracPairing_antisymm b a, diracPairing_antisymm c a]; ring

theorem diracPairing_smul_right (c : ℤ) (a b : ChargeLattice r) :
    diracPairing a (c • b) = c * diracPairing a b := by
  rw [diracPairing_antisymm a (c • b), diracPairing_smul_left, diracPairing_antisymm a b]
  ring

/-! ## Symplectic maps and Picard–Lefschetz transvections -/

/-- A charge-lattice map is **symplectic** if it preserves the Dirac pairing. The
monodromy representation of the SW family lands in this group — concretely `Sp(2r,ℤ)`. -/
def IsSymplectic (f : ChargeLattice r → ChargeLattice r) : Prop :=
  ∀ v w, diracPairing (f v) (f w) = diracPairing v w

/-- **Picard–Lefschetz transvection** of a vanishing charge `γ`: `T_γ v = v + ⟨v,γ⟩ γ`.
This is the local monodromy on the charge lattice around a singularity where the BPS
state of charge `γ` becomes massless. -/
def transvection (γ v : ChargeLattice r) : ChargeLattice r :=
  v + diracPairing v γ • γ

/-- **A Picard–Lefschetz transvection preserves the Dirac pairing.** The algebraic core
of the monodromy layer: every such local monodromy is symplectic, so the whole monodromy
representation lands in `Sp(2r,ℤ)`. Proved from bilinearity + `⟨γ,γ⟩ = 0`. -/
theorem transvection_diracPairing (γ v w : ChargeLattice r) :
    diracPairing (transvection γ v) (transvection γ w) = diracPairing v w := by
  simp only [transvection, diracPairing_add_left, diracPairing_add_right,
    diracPairing_smul_left, diracPairing_smul_right, diracPairing_self, mul_zero, add_zero]
  rw [diracPairing_antisymm γ w]; ring

/-- Every Picard–Lefschetz transvection is symplectic. -/
theorem transvection_isSymplectic (γ : ChargeLattice r) :
    IsSymplectic (transvection γ) :=
  fun v w => transvection_diracPairing γ v w

/-! ## The remaining gap: identifying local monodromies as transvections -/

/-- **GAP (Phase 3/4) — the Picard–Lefschetz theorem.** The *local* monodromy of the SW
    family around a generic component of the singular locus `Δ` *equals* the transvection
    `T_γ` of the charge `γ` that becomes massless there. Stated abstractly via an opaque
    local-monodromy map `localMonodromy`; making it concrete needs the family/local-system
    layer (`π₁(U)` acting on `H₁` via Gauss–Manin), which `jacobian-challenge` does not
    yet have. Once supplied, `transvection_isSymplectic` immediately gives that the local
    monodromy is symplectic, and the budget `M_∞ = ∏ T_{γ_i}` follows from the `π₁`
    presentation of the punctured base.

    Reference: Picard–Lefschetz theory; Seiberg–Witten hep-th/9407087 §3. (NOT VERIFIED.) -/
axiom localMonodromy : ∀ {r : ℕ}, ChargeLattice r → (ChargeLattice r → ChargeLattice r)

/-- The Picard–Lefschetz identification (the gap above), stated. -/
axiom AX_picard_lefschetz_local {r : ℕ} (γ : ChargeLattice r) :
    localMonodromy γ = transvection γ

/-- Consequence (modulo the gap): the local monodromy is symplectic — i.e. lies in
`Sp(2r,ℤ)`. This is how `transvection_isSymplectic` feeds `EMDualityConsistent`. -/
theorem localMonodromy_isSymplectic (γ : ChargeLattice r) :
    IsSymplectic (localMonodromy γ) := by
  rw [AX_picard_lefschetz_local]; exact transvection_isSymplectic γ

end SeibergWitten.Physics
