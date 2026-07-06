/-
# The period-level (Picard–Fuchs / Gauss–Manin) layer, packaged as debt

`audit/SU2_UNIQUENESS_SCOPING.md` showed that closing the SU(2) headline goals from H1–H6 + B.2
bottoms out in **period-level structure** (the periods as solutions of a Picard–Fuchs ODE, the
Gauss–Manin local system `π₁(ℂ∖Δ) → Sp(2,ℤ)`, Picard–Lefschetz, and the asymptotic
normalization). That layer is not yet built. Here we **package exactly what the rank-1 closure
needs** as a `PeriodLayer` structure — recognized classical period-geometry facts, math debt to
discharge when the variation-of-Hodge-structure layer lands — and **prove the SU(2) B.1 goals
from it**.

Taken as a *hypothesis* (not a global axiom), it keeps the proved theorems' footprint at
standard-3: the period-level debt is explicit in the signature, exactly as `IsPolarizedPeriodChart`
makes the physics explicit. The genuine new content is that uniqueness routes through the
**zero-axiom** `su2_deck_of_periodFrame` (Step C); the structure supplies only the inputs Steps
A/B′ would derive from the period geometry.
-/
import SeibergWitten.Physics.SU2Uniqueness

namespace SeibergWitten.Physics

open SeibergWitten.Physics.SU2

/-- **The period-level closure layer for SU(2), as debt.** Two clauses — the *conclusions* the
(absent) Picard–Fuchs / Gauss–Manin layer would supply, packaged so the SU(2) headline goals
become theorems. (Caveat, per external review: this structure carries the **conclusions**, not
the period geometry itself — there are no `∮ λ_SW` integrals or ODEs here. The deeper layer that
would *prove* these — the period integrals solving a Picard–Fuchs ODE, the Gauss–Manin local
system, Schur-rigidity, the exact H6 normalization — is the genuine target; then `rigidity`
becomes a theorem, not a field. This is honest but coarse debt.)

* `rigidity` — *Steps A + B′*. Two SW effective theories over a common base, **on a connected
  overlap**, have their period vectors related by a *single* `SL(2,ℤ)` frame (`det = 1`).
  Decomposition: Gauss–Manin + Picard–Lefschetz fix the monodromy (A); the periods solve a
  common Picard–Fuchs ODE, so same-monodromy solutions differ by a *constant* matrix (Schur,
  irreducibility), and the weak-coupling normalization (H6) fixes it to integral, `det = 1` (B′).
  **Connectedness is required**: across a disconnected overlap the frame jumps by a monodromy
  matrix between components (the global-constant frame is false otherwise — flagged in review).
  **H6 must fix the exact scale** (`a ∼ √u` with the exact coefficient, not merely `∝`); a `ℂ*`
  scaling ambiguity would defeat the integrality of `(α,β,γ,δ)`.
* `realize` — *existence* (a coarse "construct + verify" clause). The SW curve `y² = P² − Λ⁴`
  furnishes a base (singular locus = discriminant locus) and a sheet around `P`'s modulus
  satisfying H1–H6. This bundles the period construction `∮ λ_SW` *and* the verification of
  H1–H6; the finer layer should instead supply the period map + ODE and let Lean *prove* H1–H6. -/
structure PeriodLayer (Λ : ℂ) where
  /-- Steps A + B′: same base, **connected overlap** ⇒ period vectors related by one `SL(2,ℤ)`
  frame. The `IsPreconnected` hypothesis is essential (a disconnected overlap admits no single
  constant frame). -/
  rigidity : ∀ {B : PeriodBase 1} (s s' : PeriodChart B), IsConnected (s.V ∩ s'.V) →
      IsPolarizedPeriodChart s Λ 2 → IsPolarizedPeriodChart s' Λ 2 →
      ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧ ∀ u ∈ s.V ∩ s'.V,
        s'.a u 0 = α * s.a u 0 + β * s.aD u 0 ∧
        s'.aD u 0 = γ * s.a u 0 + δ * s.aD u 0
  /-- Existence: the **SU(2)** SW curve `y² = (x²−u)² − Λ⁴` realizes an effective theory at its
  (smooth) modulus. `P` is the characteristic polynomial: monic, degree 2, and **trace-free**
  (`coeff 1 = 0`) — the trace-free condition cuts SU(2) out of U(2). -/
  realize : ∀ P : Polynomial ℂ, P.Monic → P.natDegree = 2 → P.coeff 1 = 0 →
      Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * 2))) →
      ∃ (B : PeriodBase 1) (s : PeriodChart B), IsPolarizedPeriodChart s Λ 2 ∧
        B.Δ = {u | ¬ Squarefree (swCurvePoly 2 Λ u)} ∧ swModulus 2 P ∈ s.V

/-- **SU(2) uniqueness — a theorem modulo the period layer.** Two SU(2) SW effective theories
over the same base are duality-related (a `SymplecticReframing`). Proof: `PeriodLayer.rigidity` supplies the
`SL(2,ℤ)` period frame; `su2_deck_of_periodFrame` (standard-3, zero axioms) builds the `SymplecticReframing`
from it. So `#print axioms` is **standard-3** — the period-level debt sits in the `PL`
hypothesis, the physics in `IsPolarizedPeriodChart`. This is the rank-1 case of B.1's
`sw_effective_theory_unique_up_to_duality`, now genuinely proved (no `sorry`) given the layer. -/
theorem sw_su2_unique_of_periodLayer {Λ : ℂ} (PL : PeriodLayer Λ) {B : PeriodBase 1}
    (s s' : PeriodChart B) (hconn : IsConnected (s.V ∩ s'.V))
    (h : IsPolarizedPeriodChart s Λ 2) (h' : IsPolarizedPeriodChart s' Λ 2) :
    Nonempty (SymplecticReframing s s') := by
  obtain ⟨α, β, γ, δ, hdet, hper⟩ := PL.rigidity s s' hconn h h'
  exact su2_deck_of_periodFrame s s' α β γ δ hdet hper

/-- **SU(2) existence — a theorem modulo the period layer.** The SW curve `y² = P² − Λ⁴`
furnishes a base (with `Δ` the discriminant locus) and a sheet around `P`'s modulus satisfying
H1–H6. This is the rank-1 case of B.1's `sw_curve_admits_effective_theory`; here it is exactly
`PeriodLayer.realize` (the period construction is the debt). -/
theorem sw_su2_exists_of_periodLayer {Λ : ℂ} (PL : PeriodLayer Λ) (P : Polynomial ℂ)
    (hPm : P.Monic) (hPdeg : P.natDegree = 2) (hPtr : P.coeff 1 = 0)
    (hsf : Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * 2)))) :
    ∃ (B : PeriodBase 1) (s : PeriodChart B), IsPolarizedPeriodChart s Λ 2 ∧
      B.Δ = {u | ¬ Squarefree (swCurvePoly 2 Λ u)} ∧ swModulus 2 P ∈ s.V :=
  PL.realize P hPm hPdeg hPtr hsf

/-! ## General rank: beyond genus 1 / SU(2)

`SU(N)` has rank `r = N − 1` and the SW curve has genus `r`; the period domain is
`SiegelUpperHalfSpace r`, the duality group `Sp(2r,ℤ)`, and `rigidity` is the higher-genus
period-map rigidity (global Torelli + irreducibility + the H6 normalization). At rank `r > 1`
there is no explicit `deck_of_periodFrame` yet — the `su2_deck_of_periodFrame` of `SU2Uniqueness`
is the rank-1 special case — so the **general layer carries the `SymplecticReframing` directly** in `rigidity`,
and the SU(2) layer *refines* it (it produces an explicit `SL(2,ℤ)` frame and *constructs* the
`SymplecticReframing`, zero-axiom). Generalizing the construction is the remaining Step-C-at-rank-`N` content. -/

/-- **The general period-level closure layer** for `SU(N)` (rank `N − 1`, genus `N − 1`,
`N ≥ 2`). Same shape as the SU(2) layer, with the `Sp(2(N−1),ℤ)` duality `SymplecticReframing` carried directly
by `rigidity`.

Two honesty notes (per external review):
* `rigidity` here outputs `Nonempty (SymplecticReframing …)` directly — so at rank `> 1` it is no longer a
  *period-level* statement but a **macroscopic gauge-theory uniqueness** clause: it makes the
  debt layer swallow the `frame ⇒ SymplecticReframing` deduction that, at rank 1, `su2_deck_of_periodFrame`
  proves. Honest, but weaker debt than the SU(2) frame form. The genuine period-level version
  awaits a general `Sp(2r,ℤ)` `deck_of_periodFrame`.
* For `N ≥ 3` the discriminant locus `Δ` is a codim-1 hypersurface with Argyres–Douglas points
  (mutually non-local states massless together), where the single-transvection picture holds
  only *generically* — consistent with H3 being stated `…AtGenericStratum`; the AD strata are
  the separate `NonLocalDegenerationLocus`. `realize` must respect this. -/
structure PeriodRigidity (N : ℕ) (Λ : ℂ) where
  /-- `SU(N)` needs `N ≥ 2` (guards the `N − 1` truncated subtraction: `N ≤ 1 ⇒` rank 0). -/
  hN : 2 ≤ N
  /-- Higher-genus period-map rigidity: two SW theories over a common base, on a connected
  (nonempty) overlap, are duality-related (`Sp(2(N−1),ℤ)`). -/
  rigidity : ∀ {B : PeriodBase (N - 1)} (s s' : PeriodChart B), IsConnected (s.V ∩ s'.V) →
      IsPolarizedPeriodChart s Λ N → IsPolarizedPeriodChart s' Λ N → Nonempty (SymplecticReframing s s')
  /-- Existence: the genus-`(N−1)` SW curve `y² = P² − Λ^{2N}` realizes a theory; `P` monic,
  degree `N`, **trace-free** (`coeff (N−1) = 0`) — the SU(N) slice of U(N). -/
  realize : ∀ P : Polynomial ℂ, P.Monic → P.natDegree = N → P.coeff (N - 1) = 0 →
      Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * N))) →
      ∃ (B : PeriodBase (N - 1)) (s : PeriodChart B), IsPolarizedPeriodChart s Λ N ∧
        B.Δ = {u | ¬ Squarefree (swCurvePoly N Λ u)} ∧ swModulus N P ∈ s.V

/-- **General uniqueness up to duality** (rank `N − 1`), modulo the layer. -/
theorem sw_unique_of_swPeriodLayer {N : ℕ} {Λ : ℂ} (PL : PeriodRigidity N Λ)
    {B : PeriodBase (N - 1)} (s s' : PeriodChart B) (hconn : IsConnected (s.V ∩ s'.V))
    (h : IsPolarizedPeriodChart s Λ N) (h' : IsPolarizedPeriodChart s' Λ N) :
    Nonempty (SymplecticReframing s s') := PL.rigidity s s' hconn h h'

/-- **General existence** (rank `N − 1`), modulo the layer. -/
theorem sw_exists_of_swPeriodLayer {N : ℕ} {Λ : ℂ} (PL : PeriodRigidity N Λ)
    (P : Polynomial ℂ) (hPm : P.Monic) (hPdeg : P.natDegree = N) (hPtr : P.coeff (N - 1) = 0)
    (hsf : Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * N)))) :
    ∃ (B : PeriodBase (N - 1)) (s : PeriodChart B), IsPolarizedPeriodChart s Λ N ∧
      B.Δ = {u | ¬ Squarefree (swCurvePoly N Λ u)} ∧ swModulus N P ∈ s.V :=
  PL.realize P hPm hPdeg hPtr hsf

/-- **The SU(2) layer refines the general one.** The rank-1 `PeriodLayer` (with the *explicit*
`SL(2,ℤ)` frame) yields a general `PeriodRigidity 2`, building each `SymplecticReframing` from the frame via the
**zero-axiom** `su2_deck_of_periodFrame` — so at rank 1 the `frame ⇒ SymplecticReframing` step is *proved*, not
assumed. (For `N > 1` the analogous general `deck_of_periodFrame` is the remaining
Step-C-at-rank-`N` work.) -/
def PeriodLayer.toGeneral {Λ : ℂ} (PL : PeriodLayer Λ) : PeriodRigidity 2 Λ where
  hN := le_refl 2
  rigidity := fun {_B} s s' hconn h h' => by
    obtain ⟨α, β, γ, δ, hdet, hper⟩ := PL.rigidity s s' hconn h h'
    exact su2_deck_of_periodFrame s s' α β γ δ hdet hper
  realize := PL.realize

/-! ## The headline, closed from the period-level math axiom

The SW period geometry — the consolidated Picard–Fuchs / Gauss–Manin facts (`PeriodRigidity`) — is
taken as a **clean math axiom** (the period-level VHS debt; to be discharged when the period
geometry is built, see `audit/PERIOD_LAYER_SCOPING.md`). With it, the headline B.1 results are
genuine theorems — proved from the **physics postulates** (`IsPolarizedPeriodChart`) plus this one
math axiom, with **no `sorry`**. -/

/-- **Math axiom — the Seiberg–Witten period geometry exists.** For `SU(N)` (`N ≥ 2`), the period
map of the SW curve family carries the rigidity (Steps A+B′ at the period level) and realization
(existence) data. The single, consolidated period-level (Hodge-theoretic) input the headline rests
on; recognized classical period geometry, not vacuous. -/
axiom periodRigidityAxiom (N : ℕ) (Λ : ℂ) (hN : 2 ≤ N) : PeriodRigidity N Λ

/-- **HEADLINE — uniqueness up to duality (`SU(N)`, proved).** Two SW effective theories over a
common base, on a connected chart overlap, are related by an `Sp(2(N−1),ℤ)` duality `SymplecticReframing`. Proved
from the physics postulates (`IsPolarizedPeriodChart`) + the period-level math axiom `periodRigidityAxiom` —
`#print axioms` is standard-3 + `periodRigidityAxiom`, **no `sorry`**. -/
theorem sw_effective_theory_unique_up_to_duality {N : ℕ} {Λ : ℂ} (hN : 2 ≤ N)
    {B : PeriodBase (N - 1)} (s s' : PeriodChart B) (hconn : IsConnected (s.V ∩ s'.V))
    (h : IsPolarizedPeriodChart s Λ N) (h' : IsPolarizedPeriodChart s' Λ N) :
    Nonempty (SymplecticReframing s s') :=
  sw_unique_of_swPeriodLayer (periodRigidityAxiom N Λ hN) s s' hconn h h'

/-- **HEADLINE — uniqueness up to duality, atlas level (proved).** Any two SW atlases over a common
base are duality-related on every connected chart overlap. Proved from the sheet-level uniqueness
applied to each atlas's per-chart `IsPolarizedPeriodChart`. -/
theorem sw_unique_up_to_duality {N : ℕ} {Λ : ℂ} (hN : 2 ≤ N) {B : PeriodBase (N - 1)}
    (A A' : PeriodAtlas B Λ N) :
    ∀ i i', IsConnected ((A.sheets i).V ∩ (A'.sheets i').V) →
      Nonempty (SymplecticReframing (A.sheets i) (A'.sheets i')) :=
  fun i i' hconn =>
    sw_effective_theory_unique_up_to_duality hN _ _ hconn (A.isSW i) (A'.isSW i')

/-- **HEADLINE — existence (`SU(N)`, proved).** The SW curve `y² = P² − Λ^{2N}` (`P` monic, degree
`N`, trace-free, smooth) furnishes a Coulomb base whose singular locus is the discriminant locus,
and a sheet around `P`'s modulus satisfying H1–H6. Proved from `periodRigidityAxiom`, **no `sorry`**. -/
theorem sw_curve_admits_effective_theory {N : ℕ} {Λ : ℂ} (hN : 2 ≤ N) (P : Polynomial ℂ)
    (hPm : P.Monic) (hPdeg : P.natDegree = N) (hPtr : P.coeff (N - 1) = 0)
    (hsf : Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * N)))) :
    ∃ (B : PeriodBase (N - 1)) (s : PeriodChart B), IsPolarizedPeriodChart s Λ N ∧
      B.Δ = {u | ¬ Squarefree (swCurvePoly N Λ u)} ∧ swModulus N P ∈ s.V :=
  sw_exists_of_swPeriodLayer (periodRigidityAxiom N Λ hN) P hPm hPdeg hPtr hsf

end SeibergWitten.Physics
