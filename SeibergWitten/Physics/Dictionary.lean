import SeibergWitten.Physics.PeriodLayer
import SeibergWitten.Physics.BetaFunction

/-!
# The physics ↔ mathematics dictionary

The project's discipline (modelled cleanly in `BetaFunction.lean`): *math axioms use only
mathematical vocabulary, and every physical concept is an explicit named definition of a
mathematical object — never a silent identification.* This module collects those identifications in
one inspectable place, so a reader can audit the physics↔math correspondence on its own.

## Catalogue (physics concept ≔ the math object it is *defined* to be)

| Physics | Math object | Where |
|---|---|---|
| moduli / Coulomb branch | `B.U = B.Δᶜ ⊆ ℂ^r` (smooth locus) | `Hypotheses.PeriodBase` |
| special coordinates `a, a_D` | holomorphic `ℂ^r → ℂ^r` on a chart | `Hypotheses.PeriodChart` |
| effective coupling `τ` | the period matrix `PeriodChart.tau` (into Siegel) | `Hypotheses` |
| BPS central charge `Z_n` | `∑ nₑ·a + ∑ n_m·a_D` | `PeriodChart.periodCombination` |
| BPS mass `M_n` | `√2 ‖Z_n‖` | `PeriodChart.periodNorm` |
| electric–magnetic duality | a `Z`-covariant symplectic lattice auto | `SymplecticReframing` |
| Argyres–Douglas point | two non-local charges massless together | `NonLocalDegenerationLocus` |
| beta function `Λ d/dΛ τ` | `Λ · ∂_Λ` of the coupling | `BetaFunction.betaFunction` |
| one-loop coefficient `b₀` | `2N − N_f` | `BetaFunction.oneLoopCoefficient` |

Each entry on the left is, in Lean, *defined* to be the object on the right — none is asserted by an
axiom. Below we add the two identifications the period axiom turns on — the **period frame**
and its bridge to **duality** — keeping the math (the `SL(2,ℤ)` relation of period vectors)
separate from the physics (`SymplecticReframing`).
-/

namespace SeibergWitten.Physics

open SeibergWitten.Physics.SU2

/-- **(Math.)** A **period frame** between two rank-1 charts: their period vectors `(a, a_D)` are
related by a single integral `SL(2,ℤ)` matrix on the overlap. A statement purely about the period
functions and `SL(2,ℤ)` — no physical vocabulary. (This is the conclusion the period axiom's
`rigidity` clause delivers.) -/
def IsPeriodFrame {B : PeriodBase 1} (s s' : PeriodChart B) (α β γ δ : ℤ) : Prop :=
  α * δ - β * γ = 1 ∧ ∀ u ∈ s.V ∩ s'.V,
    s'.a u 0 = α * s.a u 0 + β * s.aD u 0 ∧
    s'.aD u 0 = γ * s.a u 0 + δ * s.aD u 0

/-- **(Dictionary bridge, zero-axiom.)** A period frame *is* an electric–magnetic duality: the math
`SL(2,ℤ)` relation between the period vectors yields a `SymplecticReframing` (the duality),
via the proved
`su2_deck_of_periodFrame` (`det = 1` ⇒ symplectic + `Z`-covariant). This is the named link from the
mathematics (period frame) to the physics (duality) — standard-3, no axiom. -/
theorem dualityFrame_of_periodFrame {B : PeriodBase 1} (s s' : PeriodChart B)
    {α β γ δ : ℤ} (h : IsPeriodFrame s s' α β γ δ) : Nonempty (SymplecticReframing s s') :=
  su2_deck_of_periodFrame s s' α β γ δ h.1 h.2

/-- **(Dictionary.)** The EFT **effective coupling** of a chart *is* its period matrix. -/
noncomputable abbrev chartCoupling {r : ℕ} {B : PeriodBase r} (s : PeriodChart B) := s.tau

/-! ## Translation aliases (physics name ⟶ math primary)

The mathematical names are primary throughout the development; the physics names below are the
dictionary's translations, **machine-linked** to the primaries by `abbrev` (so they denote exactly
the same objects, while `#print axioms` and every proof use the math names). A physicist may read or
write with the right column; the trusted base and the statements use the left. -/

/-- Physics: the **Coulomb branch** (moduli with the singular locus removed). -/
abbrev CoulombBase (r : ℕ) : Type := PeriodBase r
/-- Physics: a **sheet** / single-valued chart of the low-energy effective theory. -/
abbrev Sheet {r : ℕ} (B : PeriodBase r) : Type := PeriodChart B
/-- Physics: an **electric–magnetic duality** between two charts. -/
abbrev Deck {r : ℕ} {B : PeriodBase r} (s s' : PeriodChart B) : Type := SymplecticReframing s s'
/-- Physics: a chart carries a **Seiberg–Witten effective theory** (the H1–H6 bundle). -/
abbrev IsSWEffectiveTheory {r : ℕ} {B : PeriodBase r} (s : PeriodChart B) (Λ : ℂ) (N : ℕ) : Prop :=
  IsPolarizedPeriodChart s Λ N
/-- Physics: the **period-level (Picard–Fuchs / Gauss–Manin) layer** the headline rests on. -/
abbrev SWPeriodLayer (N : ℕ) (Λ : ℂ) : Prop := PeriodRigidity N Λ
/-- Physics: the **charge lattice** — the homology `H₁(Σ,ℤ)` of electric+magnetic charges. -/
abbrev ChargeLattice (r : ℕ) : Type := CycleLattice r
/-- Physics: the **Dirac (electric–magnetic) pairing** — the intersection form on `H₁`. -/
abbrev diracPairing {r : ℕ} (n n' : CycleLattice r) : ℤ := intersectionForm n n'

end SeibergWitten.Physics
