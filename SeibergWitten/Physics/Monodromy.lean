/-
# The monodromy layer — scoping (Phase 3/4)

The `Sp(2r,ℤ)` monodromy of the SW family is what both open gaps need: the
"no-too-many-singularities" budget (`SU2Singularities.lean`) and the SU(2) rigidity
uniformization (`SU2Rigidity.lean`, `AX_su2_modular_frame_alignment`). This file scopes
it: it **proves** the algebraic core and isolates the topological/family inputs.

## What is proved here (column 1)

The charge lattice `CycleLattice r = ℤ^r × ℤ^r` carries the Dirac pairing `intersectionForm`
(`Physics/Hypotheses.lean`) — the symplectic form `H₁` inherits as the intersection
form. The **Picard–Lefschetz transvection** of a vanishing charge `γ`,
`T_γ : v ↦ v + ⟨v,γ⟩ γ`, is the local monodromy around a singularity where the BPS state
`γ` goes massless. We prove:

* `intersectionForm` is `ℤ`-bilinear, antisymmetric, and alternating (`intersectionForm_self`);
* **`transvection_isSymplectic`**: every transvection preserves `intersectionForm` — so the
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

/-! ## Dirac-pairing algebra and transvections — now in `Hypotheses.lean`

The Dirac-pairing bilinearity lemmas (`intersectionForm_self`, `_antisymm`, `_add_left`, …),
`IsSymplectic`, the Picard–Lefschetz `transvection`, and `transvection_isSymplectic` now live
beside `intersectionForm` in `Hypotheses.lean` — so H3 (`PicardLefschetzAtGenericStratum`) and this
family layer share **one** `transvection`. They are re-exported by the `import` above. -/

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
axiom localMonodromy : ∀ {r : ℕ}, CycleLattice r → (CycleLattice r → CycleLattice r)

/-- The Picard–Lefschetz identification (the gap above), stated. -/
axiom AX_picard_lefschetz_local {r : ℕ} (γ : CycleLattice r) :
    localMonodromy γ = transvection γ

/-- Consequence (modulo the gap): the local monodromy is symplectic — i.e. lies in
`Sp(2r,ℤ)`. This is how `transvection_isSymplectic` feeds `EMDualityConsistent`. -/
theorem localMonodromy_isSymplectic (γ : CycleLattice r) :
    IsSymplectic (localMonodromy γ) := by
  rw [AX_picard_lefschetz_local]; exact transvection_isSymplectic γ

end SeibergWitten.Physics
