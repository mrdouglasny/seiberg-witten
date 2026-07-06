/-
# The family / variation layer — scoping (the keystone gap)

Everything still open reduces to this: the SW curves form a *family* over the smooth
Coulomb branch `U = ℂ^r ∖ Δ`, and the open gaps (`AX_picard_lefschetz_local`,
`AX_su2_modular_frame_alignment`, the "no-too-many" budget, `EMDualityConsistent`) all
need the structure that family carries.

Mathematically that structure is a **polarized integral variation of Hodge structure
(VHS) of weight 1** over `U`:

* **Local system** `ℒ = R¹π_*ℤ` — the fibrewise `H¹(C_u,ℤ) ≅ ℤ^{2r}` as a locally
  constant sheaf; equivalently the **monodromy representation** `ρ : π₁(U) → Sp(2r,ℤ)`.
* **Gauss–Manin connection** `∇` — the flat connection whose flat sections are `ℒ`;
  in coordinates its horizontal sections solve the **Picard–Fuchs** ODEs.
* **Hodge filtration / period map** — the holomorphic sub-bundle `F¹ = H^{1,0}` varying
  over `U`, i.e. the holomorphic **period map** `U → Siegel` (our `τ(u)`).
* **Polarization** — the intersection form = the Dirac pairing `intersectionForm`; `ρ`
  preserves it (lands in `Sp`).

## What is proved here (column 1)

The **target group** of the monodromy is built and shown to be a genuine group:
`IsSymplectic` maps are closed under identity and composition, so they form
`symplecticMonoid r` — the realization of `Sp(2r,ℤ)` as symplectic self-maps of the
charge lattice. The monodromy budget `M_∞ = ∏ T_{γ_i}` is then an equation *in this
monoid*. With `transvection_isSymplectic` (`Monodromy.lean`) this gives the whole
algebraic side of "monodromy ⊆ `Sp(2r,ℤ)`", free of any family/topology input.

## What is scoped — and why it is *not* a single axiom

`SWVariation r Δ` below is the precise **specification** of what the family layer must
output: a period map `U → Siegel`, a symplectic monodromy representation, and generators
around `Δ` acting by Picard–Lefschetz transvections.

Note we deliberately do **not** add an axiom `Nonempty (SWVariation r Δ)`: it would be
*vacuous* — a trivial model (constant period, `vanishingCharge = 0` so every monodromy is
`id`) satisfies the spec. The content of the family layer is precisely the *tie to the
actual curve* (the period map is the real period matrix, the vanishing charges are the
real vanishing cycles), which no placeholder can encode. So this layer must be **built**,
not axiomatized; the honest granular placeholder meanwhile is `AX_picard_lefschetz_local`
(`Monodromy.lean`), stated against the *actual* family's `localMonodromy`.

## Build plan / Mathlib status

* `symplecticMonoid`, `transvection_isSymplectic` — done here / `Monodromy.lean`.
* Period map `U → Siegel`, pointwise — `sw_coupling_mem_siegel` already gives `τ ∈ Siegel`
  at each smooth modulus; the gap is assembling these into a *holomorphic* map over `U`.
* Local system / `R¹π_*ℤ` / Gauss–Manin — **absent** from Mathlib and jacobian-challenge
  (no families of varieties, no VHS-over-a-base). The largest new piece.
* Picard–Fuchs ODE (SU(2)) — concrete and writable; the asymptotics route is
  `math-commons/picard-lefschetz` (already noted in `PLAN.md` Phase 3).

References: Seiberg–Witten hep-th/9407087 §3–4; Lerche hep-th/9611190 §3; the VHS /
Gauss–Manin framework (Griffiths; Voisin, *Hodge Theory and Complex Algebraic Geometry*).
-/
import SeibergWitten.Physics.Monodromy


namespace SeibergWitten.Physics

variable {r : ℕ}

/-! ## The target group: `Sp(2r,ℤ)` as symplectic self-maps of the charge lattice -/

/-- The identity is symplectic. -/
theorem isSymplectic_id : IsSymplectic (id : CycleLattice r → CycleLattice r) :=
  fun _ _ => rfl

/-- Symplectic maps are closed under composition. -/
theorem IsSymplectic.comp {f g : CycleLattice r → CycleLattice r}
    (hf : IsSymplectic f) (hg : IsSymplectic g) : IsSymplectic (f ∘ g) :=
  fun v w => (hf (g v) (g w)).trans (hg v w)

/-- **The symplectic monoid `Sp(2r,ℤ)`**, realized as the symplectic self-maps of the
charge lattice under composition. The monodromy representation of the SW family targets
this submonoid, and the budget `M_∞ = ∏ T_{γ_i}` is an equation in it. -/
def symplecticMonoid (r : ℕ) : Submonoid (Function.End (CycleLattice r)) where
  carrier := {f | IsSymplectic f}
  one_mem' := isSymplectic_id
  mul_mem' := fun hf hg => IsSymplectic.comp hf hg

@[simp] theorem mem_symplecticMonoid {f : Function.End (CycleLattice r)} :
    f ∈ symplecticMonoid r ↔ IsSymplectic f := Iff.rfl

/-! ## Specification of the family layer -/

/-- **The SW family / variation data over the punctured base** — a polarized integral
variation of Hodge structure of weight 1 over `U = ℂ^r ∖ Δ`. This is the *specification*
the family layer must produce (see the module docstring on why it is not axiomatized):

* `period` — the holomorphic period map `U → Siegel` (the Hodge filtration);
* `monodromy` — the representation `ρ : π₁(U) → GL(H₁)`, here with `Loop` standing in for
  `π₁(U)`, landing in the symplectic maps (`monodromy_symplectic`);
* `vanishingLoop`/`vanishingCharge`/`picard_lefschetz` — the generators around each
  component of `Δ` act by the Picard–Lefschetz transvection of the vanishing charge. -/
structure SWVariation (r : ℕ) (Δ : Set (Fin r → ℂ)) where
  /-- holomorphic period map `U = ℂ^r∖Δ → Siegel`. -/
  period : {u : Fin r → ℂ // u ∉ Δ} → SiegelUpperHalfSpace r
  /-- abstract stand-in for `π₁(U, u₀)`. -/
  Loop : Type
  /-- the monodromy representation on the charge lattice (`H₁`). -/
  monodromy : Loop → (CycleLattice r → CycleLattice r)
  /-- the representation preserves the intersection form: it lands in `Sp(2r,ℤ)`. -/
  monodromy_symplectic : ∀ ℓ, IsSymplectic (monodromy ℓ)
  /-- a generating loop encircling each component of the singular locus `Δ`. -/
  vanishingLoop : Δ → Loop
  /-- the BPS charge that becomes massless there (the vanishing cycle). -/
  vanishingCharge : Δ → CycleLattice r
  /-- Picard–Lefschetz: the generator's monodromy is the transvection of its charge. -/
  picard_lefschetz : ∀ d, monodromy (vanishingLoop d) = transvection (vanishingCharge d)

/-- Coherence: in any `SWVariation`, the generator monodromies are symplectic *via* the
proved `transvection_isSymplectic` — the structure's `monodromy_symplectic` is consistent
with the Picard–Lefschetz law, not an extra assumption on the generators. -/
theorem SWVariation.generator_isSymplectic {Δ : Set (Fin r → ℂ)} (V : SWVariation r Δ)
    (d : Δ) : IsSymplectic (V.monodromy (V.vanishingLoop d)) := by
  rw [V.picard_lefschetz]; exact transvection_isSymplectic _

/-- The monodromy representation of an `SWVariation` lands in `symplecticMonoid r`
(its image is a subset of `Sp(2r,ℤ)`). -/
theorem SWVariation.monodromy_mem_symplecticMonoid {Δ : Set (Fin r → ℂ)}
    (V : SWVariation r Δ) (ℓ : V.Loop) :
    (V.monodromy ℓ : Function.End (CycleLattice r)) ∈ symplecticMonoid r :=
  V.monodromy_symplectic ℓ

end SeibergWitten.Physics
