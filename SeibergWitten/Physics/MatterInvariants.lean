/-
# Weierstrass invariants of the matter quartics (MC1 of the matter classical route)

`audit/MATTER_CLASSICAL_PLAN.md`: the matter curves `y² = (x²−u)² − Λ^{4−N_f}∏(x−mᵢ)`
are anchored through the **j-invariant**, rational in the quartic's coefficients and
symmetric in the branch points — no root ordering, no choices. This file is **MC1**,
the axiom-free invariant layer:

* `quarticG2`, `quarticG3`, `quarticJ` — the classical invariants of a quartic
  `a x⁴ + b x³ + c x² + d x + e`, read off `Polynomial.coeff` (so they apply to
  `swCurveMatter` with no re-derivation);
* closed forms at `N_f = 1` (`quarticG2_nf1`, `quarticG3_nf1`);
* the **triple-root criterion**: any `(X+a)³(X−b)` has `g₂ = g₃ = 0`
  (`quarticG2_of_triple_root`, `quarticG3_of_triple_root`) — the invariant-theoretic
  face of an `A₂` cusp;
* the **Argyres–Douglas point as an invariant statement**: at
  `(u, m) = (¾Λ², −¾Λ)` both invariants vanish (`matter_nf1_ad_invariants`).

Conventions pinned numerically first (`audit/numerical/validate_matterj.py`,
19/19 at 40 digits), including the Landen factor-2 finding recorded in the plan.
-/
import SeibergWitten.Physics.SU2Matter
import SeibergWitten.Physics.ThetaLambda
import SeibergWitten.Physics.SU2Rigidity

namespace SeibergWitten.Physics

open Polynomial

/-- The classical quartic invariant `g₂ = a e − b d/4 + c²/12` of
`a x⁴ + b x³ + c x² + d x + e`, read off the polynomial's coefficients. -/
noncomputable def quarticG2 (P : ℂ[X]) : ℂ :=
  P.coeff 4 * P.coeff 0 - P.coeff 3 * P.coeff 1 / 4 + P.coeff 2 ^ 2 / 12

/-- The classical quartic invariant
`g₃ = a c e/6 + b c d/48 − a d²/16 − b² e/16 − c³/216`. -/
noncomputable def quarticG3 (P : ℂ[X]) : ℂ :=
  P.coeff 4 * P.coeff 2 * P.coeff 0 / 6 + P.coeff 3 * P.coeff 2 * P.coeff 1 / 48
    - P.coeff 4 * P.coeff 1 ^ 2 / 16 - P.coeff 3 ^ 2 * P.coeff 0 / 16
    - P.coeff 2 ^ 3 / 216

/-- The j-invariant `j = 1728 g₂³/(g₂³ − 27 g₃²)` (junk at the discriminant locus,
per Lean division conventions — exactly where the curve degenerates). -/
noncomputable def quarticJ (P : ℂ[X]) : ℂ :=
  1728 * quarticG2 P ^ 3 / (quarticG2 P ^ 3 - 27 * quarticG3 P ^ 2)

/-- The `N_f = 1` matter curve in expanded (coefficient) form. -/
theorem swCurveMatter_nf1_expand (Λ m₁ u : ℂ) :
    swCurveMatter 1 Λ ![m₁] u
      = X ^ 4 + C (-(2 * u)) * X ^ 2 + C (-(Λ ^ 3)) * X + C (u ^ 2 + Λ ^ 3 * m₁) := by
  apply Polynomial.funext
  intro x
  simp [swCurveMatter]
  ring

/-- Coefficients of the expanded `N_f = 1` curve. -/
theorem swCurveMatter_nf1_coeff (Λ m₁ u : ℂ) :
    (swCurveMatter 1 Λ ![m₁] u).coeff 4 = 1 ∧
    (swCurveMatter 1 Λ ![m₁] u).coeff 3 = 0 ∧
    (swCurveMatter 1 Λ ![m₁] u).coeff 2 = -(2 * u) ∧
    (swCurveMatter 1 Λ ![m₁] u).coeff 1 = -(Λ ^ 3) ∧
    (swCurveMatter 1 Λ ![m₁] u).coeff 0 = u ^ 2 + Λ ^ 3 * m₁ := by
  rw [swCurveMatter_nf1_expand]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      norm_num

/-- **`g₂` of the `N_f = 1` curve in closed form:** `g₂ = (4/3)u² + Λ³ m₁`. -/
theorem quarticG2_nf1 (Λ m₁ u : ℂ) :
    quarticG2 (swCurveMatter 1 Λ ![m₁] u) = 4 / 3 * u ^ 2 + Λ ^ 3 * m₁ := by
  obtain ⟨h4, h3, h2, h1, h0⟩ := swCurveMatter_nf1_coeff Λ m₁ u
  rw [quarticG2, h4, h3, h2, h1, h0]
  ring

/-- **`g₃` of the `N_f = 1` curve in closed form:**
`g₃ = −(8/27)u³ − (1/3)u Λ³ m₁ − Λ⁶/16`. -/
theorem quarticG3_nf1 (Λ m₁ u : ℂ) :
    quarticG3 (swCurveMatter 1 Λ ![m₁] u)
      = -(8 / 27) * u ^ 3 - 1 / 3 * u * Λ ^ 3 * m₁ - Λ ^ 6 / 16 := by
  obtain ⟨h4, h3, h2, h1, h0⟩ := swCurveMatter_nf1_coeff Λ m₁ u
  rw [quarticG3, h4, h3, h2, h1, h0]
  ring

/-- Expansion of a triple-root quartic `(X+a)³(X−b)`. -/
theorem triple_root_expand (a b : ℂ) :
    (X + C a) ^ 3 * (X - C b)
      = X ^ 4 + C (3 * a - b) * X ^ 3 + C (3 * a ^ 2 - 3 * a * b) * X ^ 2
        + C (a ^ 3 - 3 * a ^ 2 * b) * X + C (-(a ^ 3 * b)) := by
  apply Polynomial.funext
  intro x
  simp
  ring

/-- **The triple-root criterion, `g₂` half:** any quartic with a triple root has
`g₂ = 0` — the invariant-theoretic face of the `A₂` cusp. -/
theorem quarticG2_of_triple_root (a b : ℂ) :
    quarticG2 ((X + C a) ^ 3 * (X - C b)) = 0 := by
  rw [triple_root_expand, quarticG2]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num
  ring

/-- **The triple-root criterion, `g₃` half.** -/
theorem quarticG3_of_triple_root (a b : ℂ) :
    quarticG3 ((X + C a) ^ 3 * (X - C b)) = 0 := by
  rw [triple_root_expand, quarticG3]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num
  ring

/-- **The `N_f = 1` Argyres–Douglas point as an invariant statement:** at
`(u, m) = (¾Λ², −¾Λ)` both Weierstrass invariants of the curve vanish — the
coordinate-free characterization of the cusp (`g₂ = g₃ = 0 ⟺` triple root),
complementing the factorization witness `swCurveMatter_nf1_ad`. Axiom-free. -/
theorem matter_nf1_ad_invariants (Λ : ℂ) :
    quarticG2 (swCurveMatter 1 Λ ![-(3 / 4) * Λ] ((3 / 4) * Λ ^ 2)) = 0 ∧
    quarticG3 (swCurveMatter 1 Λ ![-(3 / 4) * Λ] ((3 / 4) * Λ ^ 2)) = 0 := by
  constructor
  · rw [quarticG2_nf1]
    ring
  · rw [quarticG3_nf1]
    ring

/-- Cross-check through the factored form: the same vanishing via
`swCurveMatter_nf1_ad` and the general triple-root criterion (two independent
routes to the same invariant statement). -/
theorem matter_nf1_ad_invariants' (Λ : ℂ) :
    quarticG2 (swCurveMatter 1 Λ ![-(3 / 4) * Λ] ((3 / 4) * Λ ^ 2)) = 0 ∧
    quarticG3 (swCurveMatter 1 Λ ![-(3 / 4) * Λ] ((3 / 4) * Λ ^ 2)) = 0 := by
  rw [show swCurveMatter 1 Λ ![-(3 / 4) * Λ] ((3 / 4) * Λ ^ 2)
      = (X + C ((1 / 2) * Λ)) ^ 3 * (X - C ((3 / 2) * Λ)) from swCurveMatter_nf1_ad Λ]
  exact ⟨quarticG2_of_triple_root _ _, quarticG3_of_triple_root _ _⟩


/-! ## MC2 — the λ-side j and the matter developing condition

The `j`-anchor's τ-side: `jλ(λ) = 256(1−λ+λ²)³/(λ²(1−λ)²)`, invariant under the
anharmonic `S₃` (which is why root ordering drops out of the curve side), composed
with the proved `λ = θ₂⁴/θ₃⁴` layer. **Dictionary item (the MC0 Landen finding):**
the quartic's intrinsic modulus is `2·τ_SW`, so the developing condition anchors
`λ(2·f u)` — the doubling is explicit in the statement, never silent. -/

/-- The `j`-invariant as a function of the λ-modulus:
`jλ(λ) = 256(1−λ+λ²)³/(λ²(1−λ)²)` (junk at `λ ∈ {0,1}`, the cusps). -/
noncomputable def jLambda (l : ℂ) : ℂ :=
  256 * (1 - l + l ^ 2) ^ 3 / (l ^ 2 * (1 - l) ^ 2)

/-- Anharmonic invariance, generator `λ ↦ 1−λ`. -/
theorem jLambda_one_sub (l : ℂ) : jLambda (1 - l) = jLambda l := by
  simp only [jLambda]
  ring_nf

/-- Anharmonic invariance, generator `λ ↦ 1/λ` (away from the cusp `λ = 0`). -/
theorem jLambda_inv {l : ℂ} (hl : l ≠ 0) : jLambda l⁻¹ = jLambda l := by
  simp only [jLambda]
  field_simp
  ring

/-- **The matter developing condition (MC2):** on a chart `D`, a candidate coupling
`f` develops the `N_f` matter curve when the `j`-invariant of `λ(2·f u)` — the
**doubled** argument is the MC0 Landen dictionary item: the quartic's intrinsic
modulus is `2·τ_SW` — equals the curve's coefficient-side `j` at every `u ∈ D`.
Anchored to the geometry through two proved layers (`modularLambdaFn = θ₂⁴/θ₃⁴`;
`quarticJ` off `Polynomial.coeff`), mirroring `DevelopsSWCrossRatio`.
*Non-vacuity status:* witnessed numerically (`validate_matterj.py` check D); a Lean
existence witness is MC3 work and, per the D3 lesson, nothing may consume this
definition as if existence were established. -/
def DevelopsMatterJ (Nf : ℕ) (Λ : ℂ) (m : Fin Nf → ℂ) (D : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ u ∈ D, jLambda (modularLambdaFn (2 * f u)) = quarticJ (swCurveMatter Nf Λ m u)

/-- A matter developing map: analytic, ℍ-valued, and developing the curve's `j`
(all three clauses load-bearing, as in the pure case — `DIFFICULT_POINTS.md` B4). -/
def IsMatterDevelopingMap (Nf : ℕ) (Λ : ℂ) (m : Fin Nf → ℂ) (D : Set ℂ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f D ∧ (∀ u ∈ D, 0 < (f u).im) ∧ DevelopsMatterJ Nf Λ m D f

/-- Two candidate matter couplings carry the same monodromy iff both develop the
curve's `j` — a definition, mirroring the pure-case demotion of `SameSWMonodromy`. -/
def SameMatterMonodromy (Nf : ℕ) (Λ : ℂ) (m : Fin Nf → ℂ) (D : Set ℂ) (f g : ℂ → ℂ) : Prop :=
  IsMatterDevelopingMap Nf Λ m D f ∧ IsMatterDevelopingMap Nf Λ m D g


/-! ## MC3, obligation (1): the anharmonic factorization of the `jλ` fibre

Review-independent (no axiom, no covering input): the cleared form of
`jλ(x) = jλ(y)` factors into the six anharmonic branches. This is what replaces a
(false-as-glossed) j-level lift-uniqueness axiom in the MC3 design — the `j`
covering is branched at the elliptic points, so the fibre is computed
*algebraically* instead of assumed. -/

/-- The cleared `jλ`-fibre polynomial factors into the six anharmonic linear
factors (degree six in `y`; pinned numerically before formalization, sign `+1`). -/
theorem jLambda_fiber_factorization (x y : ℂ) :
    (1 - x + x ^ 2) ^ 3 * (y ^ 2 * (1 - y) ^ 2)
      - (1 - y + y ^ 2) ^ 3 * (x ^ 2 * (1 - x) ^ 2)
    = (y - x) * (y - (1 - x)) * (y * x - 1) * (y * (1 - x) - 1)
      * (y * (x - 1) - x) * (y * x - (x - 1)) := by
  ring

/-- **The fibre of `jλ` is the anharmonic orbit** (away from the cusps `{0,1}`):
`jλ(x) = jλ(y)` forces `y` into the six-element anharmonic orbit of `x`, stated in
cleared (division-free) form. Axiom-free. -/
theorem jLambda_eq_anharmonic {x y : ℂ} (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hy0 : y ≠ 0) (hy1 : y ≠ 1) (h : jLambda x = jLambda y) :
    y = x ∨ y = 1 - x ∨ y * x = 1 ∨ y * (1 - x) = 1
      ∨ y * (x - 1) = x ∨ y * x = x - 1 := by
  have hx1' : (1 : ℂ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hy1' : (1 : ℂ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy1)
  have hdx : x ^ 2 * (1 - x) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 hx1')
  have hdy : y ^ 2 * (1 - y) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hy0) (pow_ne_zero 2 hy1')
  rw [jLambda, jLambda, div_eq_div_iff hdx hdy] at h
  have hE : (1 - x + x ^ 2) ^ 3 * (y ^ 2 * (1 - y) ^ 2)
      - (1 - y + y ^ 2) ^ 3 * (x ^ 2 * (1 - x) ^ 2) = 0 := by
    linear_combination (1 / 256 : ℂ) * h
  rw [jLambda_fiber_factorization] at hE
  rcases mul_eq_zero.mp hE with h5 | h6
  · rcases mul_eq_zero.mp h5 with h4 | h5'
    · rcases mul_eq_zero.mp h4 with h3 | h4'
      · rcases mul_eq_zero.mp h3 with h2 | h3'
        · rcases mul_eq_zero.mp h2 with h1 | h2'
          · exact Or.inl (sub_eq_zero.mp h1)
          · exact Or.inr (Or.inl (sub_eq_zero.mp h2'))
        · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h3')))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h4'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h5')))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h6)))))


/-! ## MC3, obligation (2): constancy of a finite branch selection

Generic point-set brick (review-independent, axiom-free): on a preconnected set, a
continuous function that pointwise equals one of finitely many continuous,
pointwise-*distinct* branches equals a single branch globally. The branch sets are
closed by continuity, disjoint by distinctness, cover by hypothesis; each is then
clopen (finite complement union), and preconnectedness collapses the partition. -/

theorem eqOn_branch_of_preconnected {n : ℕ} {D : Set ℂ} (hD : IsPreconnected D)
    {k : ℂ → ℂ} {F : Fin n → ℂ → ℂ}
    (hk : ContinuousOn k D) (hF : ∀ i, ContinuousOn (F i) D)
    (hdist : ∀ u ∈ D, ∀ i j, i ≠ j → F i u ≠ F j u)
    (hcover : ∀ u ∈ D, ∃ i, k u = F i u)
    {u₀ : ℂ} (hu₀ : u₀ ∈ D) :
    ∃ i, Set.EqOn k (F i) D := by
  haveI : PreconnectedSpace D := Subtype.preconnectedSpace hD
  obtain ⟨i₀, hi₀⟩ := hcover u₀ hu₀
  set S : Fin n → Set D := fun i => {x : D | k x = F i x} with hS
  have hSclosed : ∀ i, IsClosed (S i) := fun i =>
    isClosed_eq (hk.restrict) ((hF i).restrict)
  have hScover : ∀ x : D, ∃ i, x ∈ S i := fun x => hcover x x.2
  have hSdisj : ∀ (x : D) (i j : Fin n), i ≠ j → x ∈ S i → x ∉ S j := by
    intro x i j hij hxi hxj
    exact hdist x x.2 i j hij (by
      have h1 : k x = F i x := hxi
      have h2 : k x = F j x := hxj
      rw [← h1, h2])
  have hopen : IsOpen (S i₀) := by
    have hcompl : (S i₀)ᶜ = ⋃ (j : Fin n), ⋃ (_ : j ≠ i₀), S j := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, hj⟩ := hScover x
        have hjne : j ≠ i₀ := fun h => hx (h ▸ hj)
        exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjne, hj⟩⟩
      · intro hx hxi
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hjne, hxj⟩ := Set.mem_iUnion.mp hj
        exact hSdisj x i₀ j (Ne.symm hjne) hxi hxj
    rw [← isClosed_compl_iff, hcompl]
    exact isClosed_iUnion_of_finite fun j =>
      isClosed_iUnion_of_finite fun _ => hSclosed j
  have huniv : S i₀ = Set.univ :=
    IsClopen.eq_univ ⟨hSclosed i₀, hopen⟩ ⟨⟨u₀, hu₀⟩, hi₀⟩
  refine ⟨i₀, fun u hu => ?_⟩
  have hx : (⟨u, hu⟩ : D) ∈ S i₀ := huniv ▸ Set.mem_univ _
  exact hx


/-! ## MC3, Q1 settled by computation: the anharmonic coincidence inventory

The review prompt's Q1 asks whether the fixed-point set
`E = {1/2, −1, 2, e^{±iπ/3}}` is complete for six-branch distinctness. Rather than
wait for an opinion, compute: the fifteen cleared pairwise differences factor into
exactly `{2x−1, (x−1)(x+1), x(x−2), x²−x+1}` — so off `E` (and the cusps) the six
anharmonic values are pairwise distinct. This is the distinctness input of
`eqOn_branch_of_preconnected`. -/

/-- The six anharmonic maps (the `S₃`-orbit of the identity under
`x ↦ 1−x`, `x ↦ 1/x`). -/
noncomputable def anharmonic : Fin 6 → ℂ → ℂ
  | 0 => fun x => x
  | 1 => fun x => 1 - x
  | 2 => fun x => x⁻¹
  | 3 => fun x => (1 - x)⁻¹
  | 4 => fun x => x / (x - 1)
  | 5 => fun x => (x - 1) / x

/-- **Off the coincidence locus the six anharmonic values are pairwise distinct.**
The exclusions are exactly the factors of the fifteen cleared differences:
`2x−1`, `x+1`, `x−2`, and `x²−x+1` (plus the cusps `0, 1` for the denominators). -/
theorem anharmonic_pairwise_ne {x : ℂ} (h0 : x ≠ 0) (h1 : x ≠ 1)
    (hh : 2 * x - 1 ≠ 0) (hn : x + 1 ≠ 0) (ht : x - 2 ≠ 0)
    (hq : x ^ 2 - x + 1 ≠ 0) :
    ∀ i j : Fin 6, i ≠ j → anharmonic i x ≠ anharmonic j x := by
  have h1' : (1 : ℂ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr h1
  intro i j hij h
  fin_cases i <;> fin_cases j <;> simp only [anharmonic] at h <;>
    first
      | exact hij rfl
      | (field_simp at h
         first
           | exact hh (by first | linear_combination h | linear_combination -h)
           | exact hq (by first | linear_combination h | linear_combination -h)
           | exact hn (by first | linear_combination h | linear_combination -h)
           | exact ht (by first | linear_combination h | linear_combination -h)
           | exact h0 (by first | linear_combination h | linear_combination -h)
           | exact hx1 (by first | linear_combination h | linear_combination -h)
           | exact h1' (by first | linear_combination h | linear_combination -h)
           | exact h1 (by first | linear_combination h | linear_combination -h)
           | (have hf : (x - 1) * (x + 1) = 0 := by
                first | linear_combination h | linear_combination -h
              rcases mul_eq_zero.mp hf with hf | hf
              · exact hx1 hf
              · exact hn hf)
           | (have hf : x * (x - 2) = 0 := by
                first | linear_combination h | linear_combination -h
              rcases mul_eq_zero.mp hf with hf | hf
              · exact h0 hf
              · exact ht hf))


/-! ## MC3 assembly, stage A: coset realization

The six anharmonic maps as τ-level Möbius words in `S : τ ↦ −1/τ` and
`T : τ ↦ τ+1`, with the composed λ-laws (from the proved `modularLambda_S` and
`modularLambda_add_one`) and ℍ-preservation. Indexing matches `anharmonic`:
`0 ↦ id`, `1 ↦ S`, `2 ↦ STS`, `3 ↦ ST`, `4 ↦ T`, `5 ↦ TS`. The λ-law is stated at
regular points (`λ(τ) ∉ {0,1}`), which is where the assembly uses it — the θ-layer
axioms do not exclude the junk value `λ = 1` (`θ₄ = 0`) globally. -/

/-- `Im(−1/τ) > 0` for `Im τ > 0` (ℂ-level form of the ℍ inversion). -/
theorem im_neg_inv_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  have h := (⟨τ, hτ⟩ : UpperHalfPlane).im_inv_neg_coe_pos
  rwa [show (-1 / τ : ℂ) = (-τ)⁻¹ from by rw [neg_div, one_div, neg_inv]]

/-- The six τ-level Möbius words realizing the anharmonic `S₃`. -/
noncomputable def anharmonicWord : Fin 6 → ℂ → ℂ
  | 0 => fun τ => τ
  | 1 => fun τ => -1 / τ
  | 2 => fun τ => -1 / (-1 / τ + 1)
  | 3 => fun τ => -1 / (τ + 1)
  | 4 => fun τ => τ + 1
  | 5 => fun τ => -1 / τ + 1

/-- Every word preserves the upper half-plane. -/
theorem anharmonicWord_im_pos (i : Fin 6) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < (anharmonicWord i τ).im := by
  fin_cases i
  · exact hτ
  · exact im_neg_inv_pos hτ
  · have h1 : 0 < (-1 / τ + 1).im := by
      rw [Complex.add_im, Complex.one_im, add_zero]
      exact im_neg_inv_pos hτ
    exact im_neg_inv_pos h1
  · have h1 : 0 < (τ + 1).im := by
      rw [Complex.add_im, Complex.one_im, add_zero]
      exact hτ
    exact im_neg_inv_pos h1
  · show 0 < (τ + 1).im
    rw [Complex.add_im, Complex.one_im, add_zero]
    exact hτ
  · show 0 < (-1 / τ + 1).im
    rw [Complex.add_im, Complex.one_im, add_zero]
    exact im_neg_inv_pos hτ

/-- **The composed λ-laws:** at regular points, `λ(Wᵢ τ) = σᵢ(λ(τ))` — each word's
λ-image is the corresponding anharmonic image, from the proved `S` and `T` laws. -/
theorem anharmonicWord_lambda (i : Fin 6) {τ : ℂ} (hτ : 0 < τ.im)
    (hx0 : modularLambdaFn τ ≠ 0) (hx1 : modularLambdaFn τ ≠ 1) :
    modularLambdaFn (anharmonicWord i τ) = anharmonic i (modularLambdaFn τ) := by
  have hS := modularLambda_S ⟨τ, hτ⟩
  have hT := modularLambda_add_one ⟨τ, hτ⟩
  have hx1' : modularLambdaFn τ - 1 ≠ 0 := sub_ne_zero.mpr hx1
  fin_cases i
  · rfl
  · exact hS
  · -- STS: λ(−1/(−1/τ+1)) = 1/λ
    have him : 0 < (-1 / τ + 1).im := by
      rw [Complex.add_im, Complex.one_im, add_zero]
      exact im_neg_inv_pos hτ
    have hTS := modularLambda_add_one ⟨-1 / τ, im_neg_inv_pos hτ⟩
    have hSTS := modularLambda_S ⟨-1 / τ + 1, him⟩
    show modularLambdaFn (-1 / (-1 / τ + 1)) = (modularLambdaFn τ)⁻¹
    rw [hSTS]
    show 1 - modularLambdaFn ((-1 / τ) + 1) = _
    rw [hTS, hS]
    have hd : (1 - modularLambdaFn τ) - 1 = -(modularLambdaFn τ) := by ring
    rw [hd]
    field_simp
    ring
  · -- ST: λ(−1/(τ+1)) = (1−λ)⁻¹
    have him : 0 < (τ + 1).im := by
      rw [Complex.add_im, Complex.one_im, add_zero]
      exact hτ
    have hST := modularLambda_S ⟨(τ : ℂ) + 1, him⟩
    have h1x : (1 : ℂ) - modularLambdaFn τ ≠ 0 := fun h => hx1 (by linear_combination -h)
    show modularLambdaFn (-1 / (τ + 1)) = (1 - modularLambdaFn τ)⁻¹
    rw [hST, hT]
    field_simp [h1x]
    ring
  · exact hT
  · -- TS: λ(−1/τ + 1) = (λ−1)/λ
    have hTS := modularLambda_add_one ⟨-1 / τ, im_neg_inv_pos hτ⟩
    show modularLambdaFn ((-1 / τ) + 1) = (modularLambdaFn τ - 1) / modularLambdaFn τ
    rw [hTS, hS]
    have hd : (1 - modularLambdaFn τ) - 1 = -(modularLambdaFn τ) := by ring
    rw [hd]
    field_simp
    ring


/-! ## MC3 assembly, stage B: the matter frame-alignment theorem

Branch selection + the v2 rigidity axiom. Ingredients: λ-continuity on ℍ (from
Mathlib's `continuousAt_jacobiTheta₂` + `AX_theta3_ne_zero`), the fibre theorem
(`jLambda_eq_anharmonic`), distinctness off the coincidence locus
(`anharmonic_pairwise_ne`), branch constancy (`eqOn_branch_of_preconnected`),
coset realization (stage A), and `AX_developing_map_rigidity` (v2). -/

/-- The regularity condition at which the whole anharmonic apparatus operates:
off the cusps and the coincidence locus. -/
def AnharmonicRegular (x : ℂ) : Prop :=
  x ≠ 0 ∧ x ≠ 1 ∧ 2 * x - 1 ≠ 0 ∧ x + 1 ≠ 0 ∧ x - 2 ≠ 0 ∧ x ^ 2 - x + 1 ≠ 0

/-- A point of ℍ is nonzero. -/
theorem ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : z ≠ 0 := by
  intro h
  rw [h] at hz
  simp at hz

/-- Doubling preserves ℍ. -/
theorem im_two_mul_pos {z : ℂ} (hz : 0 < z.im) : 0 < ((2 : ℂ) * z).im := by
  have h : ((2 : ℂ) * z).im = 2 * z.im := by
    simp [Complex.mul_im]
  rw [h]
  linarith

/-- **λ is continuous on ℍ** — each θ-null is continuous there
(`continuousAt_jacobiTheta₂`), and `θ₃ ≠ 0` (the axiom) makes the quotient
continuous. -/
theorem continuousAt_modularLambdaFn {τ : ℂ} (hτ : 0 < τ.im) :
    ContinuousAt modularLambdaFn τ := by
  have h3 : ContinuousAt theta3 τ := by
    have h := continuousAt_jacobiTheta₂ 0 hτ
    exact h.comp (Continuous.continuousAt (by fun_prop : Continuous fun τ : ℂ => ((0 : ℂ), τ)))
  have h2 : ContinuousAt theta2 τ := by
    have hj : ContinuousAt (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (τ / 2, τ) :=
      continuousAt_jacobiTheta₂ (τ / 2) hτ
    have hpair : Continuous fun τ : ℂ => (τ / 2, τ) := by fun_prop
    have hcomp : ContinuousAt (fun τ : ℂ => jacobiTheta₂ (τ / 2) τ) τ := by
      have h := ContinuousAt.comp (f := fun τ : ℂ => (τ / 2, τ)) hj hpair.continuousAt
      simpa [Function.comp_def] using h
    exact (Complex.continuous_exp.continuousAt.comp
      (Continuous.continuousAt (by fun_prop))).mul hcomp
  have hne : theta3 τ ^ 4 ≠ 0 := pow_ne_zero 4 (AX_theta3_ne_zero ⟨τ, hτ⟩)
  exact ((h2.pow 4).div (h3.pow 4) hne)

/-- Möbius words are analytic along ℍ-valued analytic maps (denominators are
nonzero by imaginary-part positivity). -/
theorem analyticOnNhd_anharmonicWord_comp (i : Fin 6) {D : Set ℂ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F D) (hH : ∀ u ∈ D, 0 < (F u).im) :
    AnalyticOnNhd ℂ (fun u => anharmonicWord i (F u)) D := by
  intro u hu
  have hFu := hF u hu
  have him := hH u hu
  have hne : F u ≠ 0 := ne_zero_of_im_pos him
  have hne1 : F u + 1 ≠ 0 := by
    apply ne_zero_of_im_pos
    rw [Complex.add_im, Complex.one_im, add_zero]
    exact him
  have hneS1 : -1 / F u + 1 ≠ 0 := by
    apply ne_zero_of_im_pos
    rw [Complex.add_im, Complex.one_im, add_zero]
    exact im_neg_inv_pos him
  fin_cases i
  · exact hFu
  · exact analyticAt_const.div hFu hne
  · exact analyticAt_const.div
      ((analyticAt_const.div hFu hne).add analyticAt_const) hneS1
  · exact analyticAt_const.div (hFu.add analyticAt_const) hne1
  · exact hFu.add analyticAt_const
  · exact (analyticAt_const.div hFu hne).add analyticAt_const

/-- **MC3 stage B — matter frame alignment.** Two matter developing maps on an
open preconnected chart, regular for the anharmonic apparatus, agree near any
point up to a `Γ(2)` frame *and* one explicit anharmonic word: there is a branch
`i` and `γ ∈ Γ(2)` with `2g ≈ γ·(Wᵢ(2f))` as germs at `u₀`. Footprint: standard-3
+ the θ pair + the covering pair (no matter-specific axiom). -/
theorem matter_frame_alignment {Nf : ℕ} {Λ : ℂ} {m : Fin Nf → ℂ}
    {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    {u₀ : ℂ} (hu₀ : u₀ ∈ D) {f g : ℂ → ℂ}
    (hmono : SameMatterMonodromy Nf Λ m D f g)
    (hreg : ∀ u ∈ D, AnharmonicRegular (modularLambdaFn (2 * f u)))
    (hcusp : ∀ u ∈ D,
      modularLambdaFn (2 * g u) ≠ 0 ∧ modularLambdaFn (2 * g u) ≠ 1) :
    ∃ i : Fin 6, ∃ γ ∈ Gamma2,
      (fun u => 2 * g u) =ᶠ[nhds u₀]
        fun u => SU2.moebiusOn γ (anharmonicWord i (2 * f u)) := by
  classical
  obtain ⟨⟨hfA, hfH, hfJ⟩, hgA, hgH, hgJ⟩ := hmono
  -- doubled maps and their properties
  have hFA : AnalyticOnNhd ℂ (fun u => (2 : ℂ) * f u) D :=
    fun u hu => analyticAt_const.mul (hfA u hu)
  have hGA : AnalyticOnNhd ℂ (fun u => (2 : ℂ) * g u) D :=
    fun u hu => analyticAt_const.mul (hgA u hu)
  have hFH : ∀ u ∈ D, 0 < ((2 : ℂ) * f u).im := fun u hu => im_two_mul_pos (hfH u hu)
  have hGH : ∀ u ∈ D, 0 < ((2 : ℂ) * g u).im := fun u hu => im_two_mul_pos (hgH u hu)
  -- step 1: pointwise, y is in the anharmonic orbit of x
  have hcover : ∀ u ∈ D, ∃ i : Fin 6,
      modularLambdaFn (2 * g u) = anharmonic i (modularLambdaFn (2 * f u)) := by
    intro u hu
    obtain ⟨hx0, hx1, -, -, -, -⟩ := hreg u hu
    obtain ⟨hy0, hy1⟩ := hcusp u hu
    have hx1' : modularLambdaFn (2 * f u) - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have hjeq : jLambda (modularLambdaFn (2 * f u))
        = jLambda (modularLambdaFn (2 * g u)) := by
      rw [hfJ u hu, hgJ u hu]
    rcases jLambda_eq_anharmonic hx0 hx1 hy0 hy1 hjeq with h | h | h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, eq_inv_of_mul_eq_one_left h⟩
    · exact ⟨3, eq_inv_of_mul_eq_one_left h⟩
    · exact ⟨4, (eq_div_iff hx1').mpr h⟩
    · exact ⟨5, (eq_div_iff hx0).mpr h⟩
  -- step 2: continuity of the selection data
  have hxcont : ContinuousOn (fun u => modularLambdaFn (2 * f u)) D := by
    intro u hu
    have h := ContinuousAt.comp (f := fun w : ℂ => (2 : ℂ) * f w)
      (continuousAt_modularLambdaFn (hFH u hu))
      ((hfA u hu).continuousAt.const_mul (2 : ℂ))
    rw [Function.comp_def] at h
    exact h.continuousWithinAt
  have hkcont : ContinuousOn (fun u => modularLambdaFn (2 * g u)) D := by
    intro u hu
    have h := ContinuousAt.comp (f := fun w : ℂ => (2 : ℂ) * g w)
      (continuousAt_modularLambdaFn (hGH u hu))
      ((hgA u hu).continuousAt.const_mul (2 : ℂ))
    rw [Function.comp_def] at h
    exact h.continuousWithinAt
  have hFcont : ∀ i : Fin 6,
      ContinuousOn (fun u => anharmonic i (modularLambdaFn (2 * f u))) D := by
    intro i
    fin_cases i
    · exact hxcont
    · exact continuousOn_const.sub hxcont
    · exact hxcont.inv₀ fun u hu => (hreg u hu).1
    · exact (continuousOn_const.sub hxcont).inv₀
        fun u hu => sub_ne_zero.mpr (Ne.symm (hreg u hu).2.1)
    · exact hxcont.div (hxcont.sub continuousOn_const)
        fun u hu => sub_ne_zero.mpr (hreg u hu).2.1
    · exact (hxcont.sub continuousOn_const).div hxcont fun u hu => (hreg u hu).1
  -- step 3: distinctness off the coincidence locus, and branch constancy
  have hdist : ∀ u ∈ D, ∀ i j : Fin 6, i ≠ j →
      anharmonic i (modularLambdaFn (2 * f u))
        ≠ anharmonic j (modularLambdaFn (2 * f u)) := by
    intro u hu
    obtain ⟨h0, h1, hh, hn, ht, hq⟩ := hreg u hu
    exact anharmonic_pairwise_ne h0 h1 hh hn ht hq
  obtain ⟨i, hEqOn⟩ := eqOn_branch_of_preconnected hDc hkcont hFcont hdist hcover hu₀
  -- step 4: hand off to the (generalized) lift-uniqueness axiom
  refine ⟨i, ?_⟩
  have hWA : AnalyticOnNhd ℂ (fun u => anharmonicWord i (2 * f u)) D :=
    analyticOnNhd_anharmonicWord_comp i hFA hFH
  have hWH : ∀ u ∈ D, 0 < (anharmonicWord i (2 * f u)).im :=
    fun u hu => anharmonicWord_im_pos i (hFH u hu)
  have hbase : ∀ u ∈ D,
      modularLambdaFn (2 * g u) = modularLambdaFn (anharmonicWord i (2 * f u)) := by
    intro u hu
    obtain ⟨hx0, hx1, -, -, -, -⟩ := hreg u hu
    exact (hEqOn hu).trans (anharmonicWord_lambda i (hFH u hu) hx0 hx1).symm
  exact SU2.AX_developing_map_rigidity
    AX_thrice_punctured_uniformization.some hDo hu₀ hGA hGH hWA hWH hbase


/-- **MC3 complete — matter coupling rigidity on the chart.** Two matter developing
maps on an open preconnected chart (regular for the anharmonic apparatus) agree on
the **whole chart** up to a `Γ(2)` frame and one explicit anharmonic word: the
stage-B germ propagated by the identity theorem (`holo_eqOn_of_germ`), both sides
being analytic (`analyticOnNhd_moebius_comp` for the Möbius side). Footprint:
standard-3 + the θ pair + the covering pair — the matter coupling's uniqueness
rests on exactly the same classical basis as the pure theory's, with
`matterPeriodRigidityAxiom` nowhere on it. -/
theorem matter_coupling_rigidity {Nf : ℕ} {Λ : ℂ} {m : Fin Nf → ℂ}
    {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    {u₀ : ℂ} (hu₀ : u₀ ∈ D) {f g : ℂ → ℂ}
    (hmono : SameMatterMonodromy Nf Λ m D f g)
    (hreg : ∀ u ∈ D, AnharmonicRegular (modularLambdaFn (2 * f u)))
    (hcusp : ∀ u ∈ D,
      modularLambdaFn (2 * g u) ≠ 0 ∧ modularLambdaFn (2 * g u) ≠ 1) :
    ∃ i : Fin 6, ∃ γ ∈ Gamma2,
      Set.EqOn (fun u => 2 * g u)
        (fun u => SU2.moebiusOn γ (anharmonicWord i (2 * f u))) D := by
  obtain ⟨i, γ, hγ, hgerm⟩ :=
    matter_frame_alignment hDo hDc hu₀ hmono hreg hcusp
  obtain ⟨⟨hfA, hfH, -⟩, hgA, hgH, -⟩ := hmono
  have hFA : AnalyticOnNhd ℂ (fun u => (2 : ℂ) * f u) D :=
    fun u hu => analyticAt_const.mul (hfA u hu)
  have hGA : AnalyticOnNhd ℂ (fun u => (2 : ℂ) * g u) D :=
    fun u hu => analyticAt_const.mul (hgA u hu)
  have hFH : ∀ u ∈ D, 0 < ((2 : ℂ) * f u).im := fun u hu => im_two_mul_pos (hfH u hu)
  have hWA : AnalyticOnNhd ℂ (fun u => anharmonicWord i (2 * f u)) D :=
    analyticOnNhd_anharmonicWord_comp i hFA hFH
  have hWH : ∀ u ∈ D, 0 < (anharmonicWord i (2 * f u)).im :=
    fun u hu => anharmonicWord_im_pos i (hFH u hu)
  have hMA : AnalyticOnNhd ℂ
      (fun u => SU2.moebiusOn γ (anharmonicWord i (2 * f u))) D :=
    SU2.analyticOnNhd_moebius_comp hWA hWH
  exact ⟨i, γ, hγ, SU2.holo_eqOn_of_germ hDc hu₀ hGA hMA hgerm⟩

end SeibergWitten.Physics
