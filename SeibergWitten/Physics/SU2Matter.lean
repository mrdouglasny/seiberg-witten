import SeibergWitten.Physics.Hypotheses

/-!
# SU(2) with matter (N_f > 0): the Seiberg–Witten curves and the Argyres–Douglas points

The rank-1 / genus-1 Seiberg–Witten curves for `N=2` `SU(2)` SQCD with `N_f` fundamental
hypermultiplets (Seiberg–Witten II, Nucl. Phys. B431; Argyres–Plesser–Seiberg–Witten,
arXiv:hep-th/9511154), and the **Argyres–Douglas points** — where the curve develops a cusp
(`y² ∼ (x−a)³`), i.e. two singularities of the `u`-plane collide. These are *empty* for pure `SU(2)`
but appear once `N_f > 0`; see `audit/SU2_MATTER_PLAN.md` (milestones M0–M2 here, axiom-free).

Main results:
* `swCurveMatter` — the matter curve `(x²−u)² − Λ^{4−N_f} ∏ᵢ(x − mᵢ)`; `swCurveMatter 0 = ` pure.
* `swCurveMatter_nf1_ad` — the `N_f=1` `(A₁,A₂)` Argyres–Douglas point as an exact factorization
  with a **triple root** (the cusp); `swCurveMatter_nf1_ad_cusp` records the `(X+½Λ)³` divisor.
* `swCurveMatter_zero_factor` — pure `SU(2)` splits into two **distinct** quadratics (no triple
  root → no AD point).
-/

namespace SeibergWitten.Physics

open Polynomial Filter Topology

variable {Nf : ℕ}

/-- **M0 — the `SU(2)` `N_f`-flavor SW curve** (SW-II quartic form), masses `m`, scale `Λ`:
`y² = (x²−u)² − Λ^{4−N_f} ∏ᵢ (x − mᵢ)`. `N_f = 0` recovers the pure curve `(x²−u)² − Λ⁴`. -/
noncomputable def swCurveMatter (Nf : ℕ) (Λ : ℂ) (m : Fin Nf → ℂ) (u : ℂ) : ℂ[X] :=
  (X ^ 2 - C u) ^ 2 - C (Λ ^ (4 - Nf)) * ∏ i, (X - C (m i))

@[simp] theorem swCurveMatter_eval (Λ : ℂ) (m : Fin Nf → ℂ) (u x : ℂ) :
    (swCurveMatter Nf Λ m u).eval x = (x ^ 2 - u) ^ 2 - Λ ^ (4 - Nf) * ∏ i, (x - m i) := by
  simp [swCurveMatter, eval_prod]

/-- `N_f = 0` is the pure `SU(2)` curve `(x²−u)² − Λ⁴`. -/
theorem swCurveMatter_zero (Λ u : ℂ) (m : Fin 0 → ℂ) :
    swCurveMatter 0 Λ m u = (X ^ 2 - C u) ^ 2 - C (Λ ^ 4) := by
  simp [swCurveMatter]

/-- **M1 — the `N_f = 1` Argyres–Douglas point** (the `(A₁,A₂)` theory). At the tuned point
`(u, m) = (¾Λ², −¾Λ)` the curve acquires a **triple root** at `x = −Λ/2`, factoring as
`(x + Λ/2)³ (x − 3Λ/2)` — the cusp `y² ∼ (x + Λ/2)³`. -/
theorem swCurveMatter_nf1_ad (Λ : ℂ) :
    swCurveMatter 1 Λ ![-(3 / 4) * Λ] ((3 / 4) * Λ ^ 2)
      = (X + C ((1 / 2) * Λ)) ^ 3 * (X - C ((3 / 2) * Λ)) := by
  apply Polynomial.funext
  intro x
  simp
  ring

/-- The Argyres–Douglas cusp: `(X + Λ/2)³` divides the `N_f=1` curve at the AD point — a root of
multiplicity (at least) three. -/
theorem swCurveMatter_nf1_ad_cusp (Λ : ℂ) :
    (X + C ((1 / 2) * Λ)) ^ 3 ∣ swCurveMatter 1 Λ ![-(3 / 4) * Λ] ((3 / 4) * Λ ^ 2) := by
  rw [swCurveMatter_nf1_ad]; exact dvd_mul_right _ _

/-- **M2 — pure `SU(2)` has no Argyres–Douglas point.** The curve factors into two quadratics
`(x²−(u+Λ²))(x²−(u−Λ²))`, **distinct** for `Λ ≠ 0`; its only collisions are simple double roots
(at `u = ±Λ²`), never a triple root. -/
theorem swCurveMatter_zero_factor (Λ u : ℂ) (m : Fin 0 → ℂ) :
    swCurveMatter 0 Λ m u = (X ^ 2 - C (u + Λ ^ 2)) * (X ^ 2 - C (u - Λ ^ 2)) := by
  apply Polynomial.funext
  intro x
  simp
  ring

/-- **M5 — the `N_f = 2` Argyres–Douglas point** (equal masses). At
`(u, m₁, m₂) = (Λ²/4, Λ/2, Λ/2)` the curve acquires a **triple root** at `x = Λ/2`, factoring as
`(x − Λ/2)³ (x + 3Λ/2)` — a second AD point, beyond `N_f = 1`. -/
theorem swCurveMatter_nf2_ad (Λ : ℂ) :
    swCurveMatter 2 Λ ![(1 / 2) * Λ, (1 / 2) * Λ] ((1 / 4) * Λ ^ 2)
      = (X - C ((1 / 2) * Λ)) ^ 3 * (X + C ((3 / 2) * Λ)) := by
  apply Polynomial.funext
  intro x
  simp [Fin.prod_univ_two]
  ring

/-- The `N_f = 2` Argyres–Douglas cusp: `(X − Λ/2)³` divides the curve at the AD point. -/
theorem swCurveMatter_nf2_ad_cusp (Λ : ℂ) :
    (X - C ((1 / 2) * Λ)) ^ 3 ∣
      swCurveMatter 2 Λ ![(1 / 2) * Λ, (1 / 2) * Λ] ((1 / 4) * Λ ^ 2) := by
  rw [swCurveMatter_nf2_ad]; exact dvd_mul_right _ _

/-! ## M3 — the carrier extension: flavor charges, masses, and the central charge

Matter adds flavor (quark-number) charges and masses; the central charge gains a flavor-linear term,
while the Dirac–Schwinger–Zwanziger pairing — hence mutual non-locality and the Argyres–Douglas
condition — stays purely gauge. This connects the matter curves above to the existing
`NonLocalDegenerationLocus` / `intersectionForm` machinery without touching the pure-`SU(2)` carrier. -/

/-- The **matter charge lattice**: gauge charges `(electric, magnetic)` together with the flavor
(quark-number) charges `Sᵢ` of `N_f` hypermultiplets. -/
abbrev MatterCycleLattice (r Nf : ℕ) : Type := CycleLattice r × (Fin Nf → ℤ)

/-- The DSZ pairing of matter charges uses **only the gauge part** — flavor charges are global, so
they never enter it. -/
def matterIntersectionForm {r Nf : ℕ} (N N' : MatterCycleLattice r Nf) : ℤ :=
  intersectionForm N.1 N'.1

@[simp] theorem matterIntersectionForm_eq {r Nf : ℕ} (N N' : MatterCycleLattice r Nf) :
    matterIntersectionForm N N' = intersectionForm N.1 N'.1 := rfl

/-- **Mutual non-locality is flavor-independent**: changing the flavor charges of a matter charge
does not change its DSZ pairing with any other. So the Argyres–Douglas condition (two mutually
non-local states colliding) is governed entirely by the gauge charges, exactly as in the pure
theory. -/
theorem matterIntersectionForm_flavor_indep {r Nf : ℕ} (g : Fin Nf → ℤ)
    (N N' : MatterCycleLattice r Nf) :
    matterIntersectionForm ((N.1, g) : MatterCycleLattice r Nf) N' = matterIntersectionForm N N' :=
  rfl

/-- The **matter central charge** `Z = nₑ·a + n_m·a_D + Σᵢ Sᵢ mᵢ` (masses `m`; the convention
constant `1/√2` absorbed). The gauge part is `PeriodChart.periodCombination`; matter adds a flavor-linear
term. -/
noncomputable def matterPeriodCombination {r : ℕ} {B : PeriodBase r} (s : PeriodChart B) {Nf : ℕ}
    (m : Fin Nf → ℂ) (u : Fin r → ℂ) (N : MatterCycleLattice r Nf) : ℂ :=
  s.periodCombination u N.1 + ∑ i, (N.2 i : ℂ) * m i

/-- With all masses zero, the matter central charge reduces to the pure gauge central charge. -/
@[simp] theorem matterPeriodCombination_massless {r : ℕ} {B : PeriodBase r} (s : PeriodChart B) {Nf : ℕ}
    (u : Fin r → ℂ) (N : MatterCycleLattice r Nf) :
    matterPeriodCombination s (fun _ => 0) u N = s.periodCombination u N.1 := by
  simp [matterPeriodCombination]

/-! ## M4 — the matter period layer (pure algebraic geometry) ⇒ `NonLocalDegenerationLocus ≠ ∅`

The deferred Gauss–Manin / Picard–Lefschetz input for the family `y² = swCurveMatter`, stated as
**algebraic geometry only**. The framework conclusion `NonLocalDegenerationLocus ≠ ∅` is obtained from it
by composing with the dictionary: the intersection form **is** `intersectionForm` (M3), and the period
`∮_n λ` **is** `PeriodChart.periodCombination n` (so a period integral tending to `0` is, definitionally,
`PeriodChart.PeriodVanishesAt`). No physical input enters the layer; the only physics — that this curve
is the theory — is the SW ansatz already in the hypotheses. -/

/-- A modulus `u₀` is a **(strict `A₂`) cusp** of `y² = swCurveMatter` when the curve there factors
with a **triple root and a distinct simple root** (`y² ∼ (x−a)³(x−b)`, `a ≠ b`) — the Kodaira
type-II degeneration proved at the AD points (`swCurveMatter_nf1_ad`, `swCurveMatter_nf2_ad`). The
`a ≠ b` keeps it strictly `A₂` (a triple-and-distinct root), excluding the `A₃` case `(x−a)⁴`. -/
def IsCuspOf (Nf : ℕ) (Λ : ℂ) (m : Fin Nf → ℂ) (u₀ : Fin 1 → ℂ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ swCurveMatter Nf Λ m (u₀ 0) = (X - C a) ^ 3 * (X - C b)

/-- The `N_f = 1` Argyres–Douglas modulus `u = ¾Λ²` is a strict `A₂` cusp (from
`swCurveMatter_nf1_ad`): triple root `−Λ/2`, distinct simple root `3Λ/2` (for `Λ ≠ 0`). -/
theorem isCuspOf_nf1 (Λ : ℂ) (hΛ : Λ ≠ 0) :
    IsCuspOf 1 Λ ![-(3 / 4) * Λ] ![(3 / 4) * Λ ^ 2] := by
  refine ⟨-((1 / 2) * Λ), (3 / 2) * Λ, ?_, ?_⟩
  · intro h; exact hΛ (by linear_combination (-1 / 2 : ℂ) * h)
  · rw [Matrix.cons_val_zero, swCurveMatter_nf1_ad]
    simp [map_neg, sub_neg_eq_add]

/-- **M4 — the matter period layer**, as a *property of a given chart* `s` (not a global axiom over
a conjured sheet — so it attaches to the actual physical `PeriodChart`). It says `s`'s periods realize the
singular-fiber dictionary: at every cusp there are two **vanishing cycles** `γ, γ'` whose
**intersection number is a unit**, `(intersectionForm γ γ').natAbs = 1` (Picard–Lefschetz gives `±1`),
and whose **period integrals** `u ↦ periodCombination u γ`, `… γ'` tend to `0`. Pure algebraic
geometry — `intersectionForm` is the intersection form and `periodCombination` the period (`Tendsto … 0`
being, definitionally, `PeriodChart.PeriodVanishesAt`). The deferred Gauss–Manin debt, of the
same kind as `periodRigidityAxiom`, carried as a **hypothesis** on the chart; to be discharged by the
genus-1 period construction extended to the matter curves and the cusp fiber. -/
structure MatterPeriodRigidityData {B : PeriodBase 1} (s : PeriodChart B)
    (Nf : ℕ) (Λ : ℂ) (m : Fin Nf → ℂ) : Prop where
  cusp : ∀ u₀ : Fin 1 → ℂ, IsCuspOf Nf Λ m u₀ →
    u₀ ∈ closure s.V ∩ B.Δ ∧
      ∃ γ γ' : CycleLattice 1, γ ≠ 0 ∧ γ' ≠ 0 ∧ (intersectionForm γ γ').natAbs = 1 ∧
        Tendsto (fun u => s.periodCombination u γ) (𝓝[s.V] u₀) (𝓝 0) ∧
        Tendsto (fun u => s.periodCombination u γ') (𝓝[s.V] u₀) (𝓝 0)

/-- **M4 — the Argyres–Douglas locus is nonempty (`N_f = 1`), from the period layer.** Standard-3:
the period-layer debt is an explicit hypothesis on the actual chart `s` (no global axiom). Composing
it with the dictionary (intersection form = `intersectionForm`; period-limit = `PeriodVanishesAt`), the
AD point of M1 lies in `NonLocalDegenerationLocus` — two mutually non-local charges become massless. -/
theorem argyresDouglasLocus_nonempty_of_matterPeriodLayer {B : PeriodBase 1} (s : PeriodChart B)
    (Λ : ℂ) (hΛ : Λ ≠ 0) (h : MatterPeriodRigidityData s 1 Λ ![-(3 / 4) * Λ]) :
    s.NonLocalDegenerationLocus.Nonempty := by
  obtain ⟨hmem, γ, γ', hγ, hγ', hpair, hmγ, hmγ'⟩ := h.cusp _ (isCuspOf_nf1 Λ hΛ)
  have hne : intersectionForm γ γ' ≠ 0 := by
    intro h0; rw [h0] at hpair; simp at hpair
  exact ⟨![(3 / 4) * Λ ^ 2], hmem, γ, γ', hγ, hγ', hne, hmγ, hmγ'⟩

/-- **M2 strengthened — pure `SU(2)` has no cusp, for any `u`.** The pure curve `(x²−u)²−Λ⁴` is
**even**, so its `X¹` and `X³` coefficients vanish; a triple-root factorization `(X−a)³(X−b)` then
forces `3a+b = 0` and `a³+3a²b = 0`, hence `a = b = 0` — contradicting `a ≠ b`. So `IsCuspOf 0 …`
is impossible: pure `SU(2)` admits no Argyres–Douglas point (no cusp to feed M4), for every `u`. -/
theorem not_isCuspOf_nf0 (Λ u : ℂ) (m : Fin 0 → ℂ) : ¬ IsCuspOf 0 Λ m ![u] := by
  rintro ⟨a, b, hab, h⟩
  rw [Matrix.cons_val_zero] at h
  have hL : swCurveMatter 0 Λ m u = X ^ 4 - C (2 * u) * X ^ 2 + C (u ^ 2 - Λ ^ 4) := by
    simp only [swCurveMatter, Fin.prod_univ_zero, mul_one, Nat.sub_zero, map_mul, map_pow,
      map_sub, map_ofNat]
    ring
  have hR : (X - C a) ^ 3 * (X - C b)
      = X ^ 4 - C (3 * a + b) * X ^ 3 + C (3 * a ^ 2 + 3 * a * b) * X ^ 2
        - C (a ^ 3 + 3 * a ^ 2 * b) * X + C (a ^ 3 * b) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  rw [hL, hR] at h
  have e3 := Polynomial.ext_iff.1 h 3
  have e1 := Polynomial.ext_iff.1 h 1
  simp (config := { decide := true }) only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow,
    coeff_C, coeff_X, mul_one, mul_zero, if_true, if_false] at e3 e1
  -- e3 ⟹ 3a+b = 0 ; e1 ⟹ a³+3a²b = 0 ; together a = 0, b = 0
  have ha3 : a ^ 3 = 0 := by linear_combination (-1 / 8 : ℂ) * e1 + (3 * a ^ 2 / 8) * e3
  have ha : a = 0 := (pow_eq_zero_iff (by norm_num)).1 ha3
  have hb : b = 0 := by linear_combination e3 - 3 * ha
  exact hab (by rw [ha, hb])

/-! ## M6 — the matter SW theory: tying the period layer to a physical sheet

So far the AD result was conditional on an abstract chart carrying the period structure. M6 ties it
to an actual `SU(2)` SQCD effective theory: a predicate `IsMatterPolarizedPeriodChart` fixing the chart
to the matter curve (special geometry; singular locus = the matter discriminant), and an existence
axiom (the matter analogue of `periodRigidityAxiom`'s `realize` + period debt) asserting such a theory
exists with its period geometry. The AD locus is then **unconditionally** nonempty for a genuine
matter theory. -/

/-- The `SU(2)` `N_f`-flavor Seiberg–Witten effective theory, as a predicate on a chart `s`: special
geometry (H1) and the moduli-space singular locus being exactly the **discriminant locus** of the
matter curve family, `B.Δ = {u | swCurveMatter … (u 0) is not squarefree}`. (A fuller version adds
the matter asymptotics H6 `b₀ = 4−N_f`, the matter R/flavor symmetry H5, …; recorded here is the
part the Argyres–Douglas result rests on — the tie of the chart to *this* curve.) -/
structure IsMatterPolarizedPeriodChart {B : PeriodBase 1} (s : PeriodChart B)
    (Nf : ℕ) (Λ : ℂ) (m : Fin Nf → ℂ) : Prop where
  specialGeometry : s.SpecialGeometry
  singularLocus : B.Δ = {u : Fin 1 → ℂ | ¬ Squarefree (swCurveMatter Nf Λ m (u 0))}

/- `matterPeriodRigidityAxiom` (the M6 existence umbrella) was DISCHARGED 2026-07-06:
the statement at its consumed instantiation is now the constructed theorem
`matterPeriodRigidity_nf1_ad` (`MatterChart.lean`), and the M6 result
`matter_argyresDouglasLocus_nonempty` now lives there, axiom-free. See
`audit/MPRA_DISCHARGE_PLAN.md` — including the disclosure that the discharge
exploits the predicate's acknowledged weakness (H1 + Δ-tie only). -/

end SeibergWitten.Physics
