/-
# Why exactly three punctures: the singularity-count pinch (n = 1)

`audit/SINGULARITY_COUNT_PLAN.md`. Seiberg–Witten *assume* the u-plane has exactly one
monopole–dyon pair of strong-coupling singularities. This file makes the count a theorem
from two named physical postulates, with **zero new axioms** — everything below is
polynomial-degree arithmetic over ℂ:

* **(P1) fiber transcription** (`IsKodairaI`): each finite singularity is Kodaira type
  `I_k` — `rootMultiplicity Δ = k` and `g₂ ≠ 0` there. Physics: k mutually local BPS
  states go massless (k = 1 in the physical Γ⁰(4) frame; k = 2 in the doubled Γ(2) frame,
  the Landen 2-isogeny of the matter route). Dictionary: Kodaira's table, `I_k ⟺
  v(Δ) = k, v(g₂) = 0 ⟺ monodromy ~ Tᵏ` — cited, not formalized; no Lean statement
  here mentions monodromy.
* **(P2) infinity transcription** (`InftyIStar`): the weak-coupling fiber is `I*_m`
  in the twist-`l` chart — `deg g₂ + 2 = 4l`, `deg g₃ + 3 = 6l`, `deg Δ + (m+6) = 12l`.
  Physics: the one-loop monodromy `M∞ = −Tᵐ` (the −1 from the Weyl ℤ₂ / `a ~ √u`).
* **(P3) homogeneity pinch** (`hdeg : g₂.natDegree ≤ 2`): holomorphy in Λ (Seiberg) +
  mass dimensions `[u] = 2, [g₂] = 4` + Λ entering only through the instanton factor
  `Λ⁴` (ℤ₈ anomaly) put `g₂ ∈ span{u², Λ⁴}`.

The two-ingredient pinch (`singularity_count_pinch`):

* counting alone (`finite_singularity_count`, `count_mod_twelve`): #finite singularities
  `= 12l − (m+6)` — for `I₄*` this is `≡ 2 (mod 12)`, i.e. `n ≡ 1 (mod 6)` pairs. The
  `l = 2` loophole (an elliptic **K3**: `I₄*` + *fourteen* `I₁`) is real — explicit witness
  in `audit/numerical/validate_singcount.py` §D — so monodromy + positivity alone can
  NEVER give `n = 1`;
* (P3) forces the twist `l = 1` (`twist_eq_one`), killing the loophole: exactly **2**
  finite singularities — one monopole–dyon pair.

Instantiated on the pure-`SU(2)` curve in both frames (closed forms pinned by the oracle,
33/33 at 40 digits; depression identities tie the Weierstrass data to the literal curve):
`Γ(2)` frame `y² = (x²−Λ⁴)(x−u)`: `I₂*` at ∞ + `I₂` at `±Λ²` (Euler 8+2+2 = 12);
`Γ⁰(4)` frame `y² = x³ − ux² + (Λ⁴/4)x` (SW's second form): `I₄*` at ∞ + `I₁` at `±Λ²`
(10+1+1 = 12, the rational elliptic surface). Consistent with `su2_singular_locus`
(`SU2Singularities.lean`): the singular values are exactly `{Λ², −Λ²}`.

Scope (recorded in the plan's scrutiny): the count is pinned *within the algebraic
Weierstrass ansatz class* (`g₂, g₃` polynomial in `u`); the ansatz-free statement is the
rank-1 classification program (Argyres–Lotito–Lü–Martone), out of scope here.
-/
import SeibergWitten.Physics.SU2Singularities
import Mathlib.Tactic.ComputeDegree

namespace SeibergWitten.Physics
namespace SingularityCount

open Polynomial

/-- The Weierstrass discriminant normalization `Δ = g₂³ − 27 g₃²` of `y² = 4x³ − g₂x − g₃`
(equal to 16 × the discriminant of the monic cubic). -/
noncomputable def wDisc (g₂ g₃ : ℂ[X]) : ℂ[X] := g₂ ^ 3 - 27 * g₃ ^ 2

/-- **(P1)** Kodaira type `I_k` at a finite point `u₀`: the discriminant vanishes to order
exactly `k` and `g₂(u₀) ≠ 0` (equivalently, the j-invariant `1728 g₂³/Δ` has a pole of
order `k`). Physics: `k` mutually local BPS states become massless at `u₀`; dictionary to
the monodromy conjugacy class `Tᵏ` by Kodaira's table (cited in `FAITHFULNESS.md`). -/
def IsKodairaI (g₂ g₃ : ℂ[X]) (k : ℕ) (u₀ : ℂ) : Prop :=
  rootMultiplicity u₀ (wDisc g₂ g₃) = k ∧ g₂.eval u₀ ≠ 0

/-- **(P2)** Fiber `I*_m` at `u = ∞` in the twist-`l` chart: the orders of vanishing at
infinity `(4l − deg g₂, 6l − deg g₃, 12l − deg Δ)` equal Kodaira's `(2, 3, m+6)` — stated
additively (no ℕ-subtraction). Physics: the weak-coupling one-loop monodromy `M∞ = −Tᵐ`.
`g₂ = 0` or `g₃ = 0` are self-excluded (`2 = 4l`, `3 = 6l` have no solutions); `Δ ≠ 0` is
carried explicitly. -/
def InftyIStar (g₂ g₃ : ℂ[X]) (l m : ℕ) : Prop :=
  wDisc g₂ g₃ ≠ 0 ∧
  g₂.natDegree + 2 = 4 * l ∧ g₃.natDegree + 3 = 6 * l ∧
  (wDisc g₂ g₃).natDegree + (m + 6) = 12 * l

/-- **(P3) The anomaly grading** — formerly the one *non-manifest* physical input of the
count, now a THEOREM given the R-spurion covariance of the curve family
(`anomalyGraded_of_rSpurionCovariant` below; the fiber transcriptions (P1)/(P2) record
manifest IR data: which BPS states sit where, the one-loop running). Seiberg holomorphy in `Λ`, the mass dimensions `[u] = 2`, `[g₂] = 4`,
and ℤ₈ anomaly quantization (`Λ` enters only through the instanton factor `Λ⁴`) leave
`g₂ ∈ span{u², Λ⁴}` at fixed `Λ`: degree at most two **and** no linear term (a `u¹` term
would need a weight-2 partner `Λ²`, forbidden by the anomaly). This is the fixed-`Λ`
shadow of the graded family statement, exactly as `Instantonic`'s homogeneity clause is
the fixed-`Λ` shadow of scale covariance (H6/B6); the pinch consumes only the degree
bound, but the postulate is stated faithfully. The analogous grading of `g₃`
(`span{u³, uΛ⁴}`) holds for the SW curve but is not needed. -/
def AnomalyGraded (g₂ : ℂ[X]) : Prop :=
  g₂.natDegree ≤ 2 ∧ g₂.coeff 1 = 0

/-- The counting identity: with `I*_m` at infinity, the number of finite singularities
*with multiplicity* is `12l − (m+6)` — over ℂ the discriminant's degree is its root count.
This is the polynomial face of "the total Euler number of an elliptic surface over ℙ¹ is
`12·deg L`" (`e(I*_m) = m + 6`, `e(I_k) = k`). -/
theorem finite_singularity_count {g₂ g₃ : ℂ[X]} {l m : ℕ} (h : InftyIStar g₂ g₃ l m) :
    Multiset.card (wDisc g₂ g₃).roots + (m + 6) = 12 * l := by
  obtain ⟨hΔ, -, -, hd⟩ := h
  have hcard : Multiset.card (wDisc g₂ g₃).roots = (wDisc g₂ g₃).natDegree := by
    rw [← Polynomial.splits_iff_card_roots]
    exact IsAlgClosed.splits _
  omega

/-- **The obstruction, isolated.** Counting alone: with `I₄*` at infinity (pure `SU(2)`
one-loop, `M∞ = −T⁴`) the finite singularity count is `≡ 2 (mod 12)` — `n ≡ 1 (mod 6)`
monopole–dyon pairs, **not** `n = 1`. The `l = 2` case (`14` singularities, an elliptic K3)
satisfies every hypothesis of this lemma: explicit witness in
`audit/numerical/validate_singcount.py` §D. Monodromy data + positivity can never do
better; closing the gap is exactly the homogeneity postulate (P3) below. -/
theorem count_mod_twelve {g₂ g₃ : ℂ[X]} {l : ℕ} (h : InftyIStar g₂ g₃ l 4) :
    Multiset.card (wDisc g₂ g₃).roots % 12 = 2 := by
  have := finite_singularity_count h
  omega

/-- **(P3) ⟹ the twist is 1.** The homogeneity bound `deg g₂ ≤ 2` (holomorphy + dimensions
+ ℤ₈ anomaly: `g₂ ∈ span{u², Λ⁴}`) forces `l = 1` in `InftyIStar`: `4l = deg g₂ + 2 ≤ 4`.
This is what kills the K3 loophole (`l = 2` needs `deg g₂ = 6`). -/
theorem twist_eq_one {g₂ g₃ : ℂ[X]} {l m : ℕ} (hdeg : AnomalyGraded g₂)
    (h : InftyIStar g₂ g₃ l m) : l = 1 := by
  obtain ⟨-, h₂, -, -⟩ := h
  have := hdeg.1
  omega

/-- If every root of `p` has the same multiplicity `k`, the number of *distinct* roots
times `k` is the root count with multiplicity. -/
theorem toFinset_card_mul_of_const_count {p : ℂ[X]} {k : ℕ}
    (h : ∀ a ∈ p.roots, p.roots.count a = k) :
    p.roots.toFinset.card * k = Multiset.card p.roots := by
  have h1 := Multiset.toFinset_sum_count_eq p.roots
  rw [Finset.sum_congr rfl (fun a ha => h a (Multiset.mem_toFinset.mp ha))] at h1
  simpa [Finset.sum_const, mul_comm] using h1

/-- **The pinch — exactly one monopole–dyon pair.** With `I*_m` at infinity, every finite
fiber of type `I_k`, the frame bookkeeping `2k + m = 6` (physical frame `(k,m) = (1,4)`;
doubled `Γ(2)`/Landen frame `(k,m) = (2,2)`), and the homogeneity bound (P3), the u-plane
has **exactly two** singular values: the count `12l − (m+6)` collapses to `6 − m = 2k` at
`l = 1`, and constant multiplicity `k` makes that two distinct points. Neither ingredient
suffices alone: without (P3) the K3 loophole gives 14 points; without the mod-12 identity
the dimension count still allows `n = 2` (total Euler number 14). -/
theorem singularity_count_pinch {g₂ g₃ : ℂ[X]} {l k m : ℕ} (hk : k ≠ 0)
    (hdeg : AnomalyGraded g₂)
    (hinf : InftyIStar g₂ g₃ l m)
    (hfib : ∀ u₀ ∈ (wDisc g₂ g₃).roots, IsKodairaI g₂ g₃ k u₀)
    (hkm : 2 * k + m = 6) :
    (wDisc g₂ g₃).roots.toFinset.card = 2 := by
  have hl : l = 1 := twist_eq_one hdeg hinf
  have hcount := finite_singularity_count hinf
  have hconst : ∀ a ∈ (wDisc g₂ g₃).roots, (wDisc g₂ g₃).roots.count a = k := by
    intro a ha
    rw [Polynomial.count_roots]
    exact (hfib a ha).1
  have h2 := toFinset_card_mul_of_const_count hconst
  have hroots : Multiset.card (wDisc g₂ g₃).roots = 2 * k := by omega
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hk) (h2.trans hroots)

/-! ## Instantiation: the pure-`SU(2)` curve, both frames

Closed forms pinned by `audit/numerical/validate_singcount.py` §A (40 digits). The
depression identities tie each `(g₂, g₃)` to the literal curve, so the data is not
free-floating. -/

/-- `Γ(2)`-frame `g₂` of `y² = (x²−Λ⁴)(x−u)`: `g₂(u) = (4/3)u² + 4Λ⁴`. -/
noncomputable def swG2 (Λ : ℂ) : ℂ[X] := C (4 / 3) * X ^ 2 + C (4 * Λ ^ 4)

/-- `Γ(2)`-frame `g₃`: `g₃(u) = (8/27)u³ − (8/3)uΛ⁴`. -/
noncomputable def swG3 (Λ : ℂ) : ℂ[X] := C (8 / 27) * X ^ 3 - C (8 / 3 * Λ ^ 4) * X

/-- `Γ⁰(4)`-frame `g₂` of SW's second form `y² = x³ − ux² + (Λ⁴/4)x`:
`g₂(u) = (4/3)u² − Λ⁴`. -/
noncomputable def swG2' (Λ : ℂ) : ℂ[X] := C (4 / 3) * X ^ 2 - C (Λ ^ 4)

/-- `Γ⁰(4)`-frame `g₃`: `g₃(u) = (8/27)u³ − (1/3)uΛ⁴`. -/
noncomputable def swG3' (Λ : ℂ) : ℂ[X] := C (8 / 27) * X ^ 3 - C (Λ ^ 4 / 3) * X

/-- Faithfulness anchor, `Γ(2)` frame: `(swG2, swG3)` really is the depressed Weierstrass
form of the curve — `(x²−Λ⁴)(x−u) = x'³ − (g₂(u)/4)x' − g₃(u)/4` with `x' = x − u/3`. -/
theorem swG_depression (Λ u x : ℂ) :
    (x ^ 2 - Λ ^ 4) * (x - u)
      = (x - u / 3) ^ 3 - (swG2 Λ).eval u / 4 * (x - u / 3) - (swG3 Λ).eval u / 4 := by
  simp only [swG2, swG3, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- Faithfulness anchor, `Γ⁰(4)` frame. -/
theorem swG_depression' (Λ u x : ℂ) :
    x ^ 3 - u * x ^ 2 + Λ ^ 4 / 4 * x
      = (x - u / 3) ^ 3 - (swG2' Λ).eval u / 4 * (x - u / 3) - (swG3' Λ).eval u / 4 := by
  simp only [swG2', swG3', eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- `Γ(2)`-frame discriminant in factored form: `Δ = 64Λ⁴ (u − Λ²)²(u + Λ²)²` —
**double** zeros at `±Λ²` (`I₂`, the Landen-doubled frame). -/
theorem sw_wDisc (Λ : ℂ) :
    wDisc (swG2 Λ) (swG3 Λ)
      = C (64 * Λ ^ 4) * ((X - C (Λ ^ 2)) * (X - C (-Λ ^ 2))) ^ 2 := by
  apply Polynomial.funext
  intro x
  simp only [wDisc, swG2, swG3, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
    eval_ofNat]
  ring

/-- `Γ⁰(4)`-frame discriminant: `Δ = Λ⁸ (u − Λ²)(u + Λ²)` — **simple** zeros at `±Λ²`
(`I₁`, the physical frame; the rational-elliptic-surface story `10 + 1 + 1 = 12`). -/
theorem sw_wDisc' (Λ : ℂ) :
    wDisc (swG2' Λ) (swG3' Λ)
      = C (Λ ^ 8) * ((X - C (Λ ^ 2)) * (X - C (-Λ ^ 2))) := by
  apply Polynomial.funext
  intro x
  simp only [wDisc, swG2', swG3', eval_sub, eval_mul, eval_pow, eval_C, eval_X,
    eval_ofNat]
  ring

theorem swG2_natDegree (Λ : ℂ) : (swG2 Λ).natDegree = 2 := by
  unfold swG2
  compute_degree!

theorem swG3_natDegree (Λ : ℂ) : (swG3 Λ).natDegree = 3 := by
  unfold swG3
  compute_degree!

theorem swG2'_natDegree (Λ : ℂ) : (swG2' Λ).natDegree = 2 := by
  unfold swG2'
  compute_degree!

theorem swG3'_natDegree (Λ : ℂ) : (swG3' Λ).natDegree = 3 := by
  unfold swG3'
  compute_degree!

/-- The `Γ(2)`-frame `g₂ = (4/3)u² + 4Λ⁴` satisfies the full anomaly grading (degree
bound **and** vanishing linear term) — the postulate is non-vacuous, not just consumable. -/
theorem sw_anomalyGraded (Λ : ℂ) : AnomalyGraded (swG2 Λ) := by
  refine ⟨le_of_eq (swG2_natDegree Λ), ?_⟩
  simp only [swG2, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C]
  norm_num

/-- The `Γ⁰(4)`-frame `g₂ = (4/3)u² − Λ⁴` satisfies the full anomaly grading. -/
theorem sw_anomalyGraded' (Λ : ℂ) : AnomalyGraded (swG2' Λ) := by
  refine ⟨le_of_eq (swG2'_natDegree Λ), ?_⟩
  simp only [swG2', coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C]
  norm_num

private lemma pairProd_ne_zero (Λ : ℂ) :
    ((X : ℂ[X]) - C (Λ ^ 2)) * (X - C (-Λ ^ 2)) ≠ 0 :=
  mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)

private lemma pairProd_natDegree (Λ : ℂ) :
    (((X : ℂ[X]) - C (Λ ^ 2)) * (X - C (-Λ ^ 2))).natDegree = 2 := by
  rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), natDegree_X_sub_C,
    natDegree_X_sub_C]

/-- The `Γ(2)`-frame data has `I₂*` at infinity with twist `l = 1`:
valuations `(2, 3, 8)`, Euler `8 + 2 + 2 = 12`. -/
theorem sw_inftyIStar (Λ : ℂ) (hΛ : Λ ≠ 0) : InftyIStar (swG2 Λ) (swG3 Λ) 1 2 := by
  have hc : (64 : ℂ) * Λ ^ 4 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hΛ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sw_wDisc]
    exact mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ (pairProd_ne_zero Λ))
  · rw [swG2_natDegree]
  · rw [swG3_natDegree]
  · rw [sw_wDisc, natDegree_C_mul hc, natDegree_pow, pairProd_natDegree]

/-- The `Γ⁰(4)`-frame data has `I₄*` at infinity with twist `l = 1`:
valuations `(2, 3, 10)`, Euler `10 + 1 + 1 = 12` — the rational elliptic surface. -/
theorem sw_inftyIStar' (Λ : ℂ) (hΛ : Λ ≠ 0) : InftyIStar (swG2' Λ) (swG3' Λ) 1 4 := by
  have hc : (Λ : ℂ) ^ 8 ≠ 0 := pow_ne_zero _ hΛ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sw_wDisc']
    exact mul_ne_zero (C_ne_zero.mpr hc) (pairProd_ne_zero Λ)
  · rw [swG2'_natDegree]
  · rw [swG3'_natDegree]
  · rw [sw_wDisc', natDegree_C_mul hc, pairProd_natDegree]

private lemma sq_ne_neg_sq {Λ : ℂ} (hΛ : Λ ≠ 0) : Λ ^ 2 ≠ -Λ ^ 2 := by
  intro h
  apply hΛ
  have h2 : (2 : ℂ) * Λ ^ 2 = 0 := by linear_combination h
  have := mul_eq_zero.mp h2
  simpa [pow_eq_zero_iff] using this.resolve_left (by norm_num)

/-- `Γ(2)`-frame roots of the discriminant: `±Λ²`, each with multiplicity two. -/
theorem sw_roots (Λ : ℂ) (hΛ : Λ ≠ 0) :
    (wDisc (swG2 Λ) (swG3 Λ)).roots = {Λ ^ 2, -Λ ^ 2, Λ ^ 2, -Λ ^ 2} := by
  have hc : (64 : ℂ) * Λ ^ 4 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hΛ)
  rw [sw_wDisc, roots_C_mul _ hc, pow_two,
    roots_mul (mul_ne_zero (pairProd_ne_zero Λ) (pairProd_ne_zero Λ)),
    roots_mul (pairProd_ne_zero Λ), roots_X_sub_C, roots_X_sub_C]
  simp only [Multiset.singleton_add, Multiset.cons_add, Multiset.insert_eq_cons]

/-- `Γ⁰(4)`-frame roots: `{Λ², −Λ²}`, simple. -/
theorem sw_roots' (Λ : ℂ) (hΛ : Λ ≠ 0) :
    (wDisc (swG2' Λ) (swG3' Λ)).roots = {Λ ^ 2, -Λ ^ 2} := by
  have hc : (Λ : ℂ) ^ 8 ≠ 0 := pow_ne_zero _ hΛ
  rw [sw_wDisc', roots_C_mul _ hc, roots_mul (pairProd_ne_zero Λ), roots_X_sub_C,
    roots_X_sub_C]
  rfl

private lemma swG2_eval_ne_zero (Λ : ℂ) (hΛ : Λ ≠ 0) {s : ℂ} (hs : s = Λ ^ 2 ∨ s = -Λ ^ 2) :
    (swG2 Λ).eval s ≠ 0 := by
  have h4 : (Λ : ℂ) ^ 4 ≠ 0 := pow_ne_zero _ hΛ
  have : (swG2 Λ).eval s = 16 / 3 * Λ ^ 4 := by
    rcases hs with rfl | rfl <;>
      · simp only [swG2, eval_add, eval_mul, eval_pow, eval_C, eval_X]
        ring
  rw [this]
  exact mul_ne_zero (by norm_num) h4

private lemma swG2'_eval_ne_zero (Λ : ℂ) (hΛ : Λ ≠ 0) {s : ℂ}
    (hs : s = Λ ^ 2 ∨ s = -Λ ^ 2) : (swG2' Λ).eval s ≠ 0 := by
  have h4 : (Λ : ℂ) ^ 4 ≠ 0 := pow_ne_zero _ hΛ
  have : (swG2' Λ).eval s = 1 / 3 * Λ ^ 4 := by
    rcases hs with rfl | rfl <;>
      · simp only [swG2', eval_sub, eval_mul, eval_pow, eval_C, eval_X]
        ring
  rw [this]
  exact mul_ne_zero (by norm_num) h4

/-- Every finite singularity of the `Γ(2)`-frame data is `I₂` (two mutually local states —
one hypermultiplet seen through the Landen 2-isogeny). -/
theorem sw_fibers (Λ : ℂ) (hΛ : Λ ≠ 0) :
    ∀ u₀ ∈ (wDisc (swG2 Λ) (swG3 Λ)).roots, IsKodairaI (swG2 Λ) (swG3 Λ) 2 u₀ := by
  intro u₀ hu₀
  have hmem := hu₀
  rw [sw_roots Λ hΛ] at hmem
  have hcases : u₀ = Λ ^ 2 ∨ u₀ = -Λ ^ 2 := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
    tauto
  constructor
  · rw [← Polynomial.count_roots, sw_roots Λ hΛ]
    have hne := sq_ne_neg_sq hΛ
    rcases hcases with rfl | rfl <;>
      simp [hne, Ne.symm hne]
  · exact swG2_eval_ne_zero Λ hΛ hcases

/-- Every finite singularity of the `Γ⁰(4)`-frame data is `I₁` (one massless BPS
hypermultiplet: the monopole at `Λ²`, the dyon at `−Λ²`). -/
theorem sw_fibers' (Λ : ℂ) (hΛ : Λ ≠ 0) :
    ∀ u₀ ∈ (wDisc (swG2' Λ) (swG3' Λ)).roots, IsKodairaI (swG2' Λ) (swG3' Λ) 1 u₀ := by
  intro u₀ hu₀
  have hmem := hu₀
  rw [sw_roots' Λ hΛ] at hmem
  have hcases : u₀ = Λ ^ 2 ∨ u₀ = -Λ ^ 2 := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
    tauto
  constructor
  · rw [← Polynomial.count_roots, sw_roots' Λ hΛ]
    have hne := sq_ne_neg_sq hΛ
    rcases hcases with rfl | rfl <;>
      simp [hne, Ne.symm hne]
  · exact swG2'_eval_ne_zero Λ hΛ hcases

/-- **The headline, physical frame, via the abstract pinch:** the pure-`SU(2)` u-plane has
exactly two singular values — one monopole–dyon pair, `n = 1`. Consumes
`singularity_count_pinch` with `(k, m) = (1, 4)`; hypotheses discharged by the
instantiation lemmas above. -/
theorem sw_exactly_two_singularities' (Λ : ℂ) (hΛ : Λ ≠ 0) :
    (wDisc (swG2' Λ) (swG3' Λ)).roots.toFinset.card = 2 :=
  singularity_count_pinch one_ne_zero (sw_anomalyGraded' Λ)
    (sw_inftyIStar' Λ hΛ) (sw_fibers' Λ hΛ) (by norm_num)

/-- Doubled-frame version via the pinch at `(k, m) = (2, 2)`. -/
theorem sw_exactly_two_singularities (Λ : ℂ) (hΛ : Λ ≠ 0) :
    (wDisc (swG2 Λ) (swG3 Λ)).roots.toFinset.card = 2 :=
  singularity_count_pinch two_ne_zero (sw_anomalyGraded Λ)
    (sw_inftyIStar Λ hΛ) (sw_fibers Λ hΛ) (by norm_num)

/-- The two singular values are exactly the monopole and dyon points `{Λ², −Λ²}` —
consistent with `su2_singular_locus` (`SU2Singularities.lean`). -/
theorem sw_singular_values (Λ : ℂ) (hΛ : Λ ≠ 0) :
    (wDisc (swG2' Λ) (swG3' Λ)).roots.toFinset = {Λ ^ 2, -Λ ^ 2} := by
  rw [sw_roots' Λ hΛ]
  simp

/-! ## The anomaly grading derived: `RSpurionCovariant ⟹ AnomalyGraded`

The postulate demotes one level. `RSpurionCovariant` is the curve-level shadow of
H5+H6, three manifestly physical clauses: (i) **scale covariance** of the family — the
curve at `(t²u, tΛ)` is the `t⁴`-rescaled curve at `(u, Λ)` (mass dimensions `[u] = 2`,
`[g₂] = 4`, `[Λ] = 1`); (ii) **anomaly quantization** — the family at `iΛ` equals the
family at `Λ`: the anomalous `U(1)_R` is exact with the instanton factor `Λ⁴` as
spurion, and the anomaly coefficient is one-loop exact (Adler–Bardeen), so `Λ` enters
only through `Λ⁴`; (iii) **weak-coupling regularity** — each coefficient has a limit
as `Λ → 0` (Seiberg holomorphy). From these `AnomalyGraded` is a THEOREM
(`anomalyGraded_of_rSpurionCovariant`): the odd coefficients die algebraically
(`t = i` in the scaling law contradicts quantization unless they vanish — the
half-instanton argument), and coefficients above `u²` die because scaling would force
them to blow up at weak coupling. Both frames of the SW curve satisfy the postulate
(`rSpurionCovariant_swG2`, `'`) — non-vacuity. -/

private lemma coeff_comp_C_mul_X (P : ℂ[X]) (a : ℂ) (n : ℕ) :
    (P.comp (C a * X)).coeff n = P.coeff n * a ^ n := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.add_comp, hp, hq, add_mul]
  | monomial i c =>
    rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
      ← Polynomial.C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_monomial]
    rcases eq_or_ne n i with rfl | hne
    · simp
    · simp [hne, Ne.symm hne]

/-- **The R-spurion covariance of the curve family** — the curve-level shadow of H5+H6
(anomalous `U(1)_R` exact with the instanton factor `Λ⁴` as spurion; Seiberg holomorphy
and weak-coupling regularity). -/
structure RSpurionCovariant (G₂ : ℂ → ℂ[X]) : Prop where
  scale : ∀ (t Λ : ℂ), t ≠ 0 → ∀ u : ℂ,
    (G₂ (t * Λ)).eval (t ^ 2 * u) = t ^ 4 * (G₂ Λ).eval u
  quantized : ∀ Λ : ℂ, G₂ (Complex.I * Λ) = G₂ Λ
  regular : ∀ j : ℕ, ∃ L : ℂ,
    Filter.Tendsto (fun Λ => (G₂ Λ).coeff j) (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds L)

/-- Coefficient form of the scaling clause: `c_j(tΛ)·t^{2j} = t⁴·c_j(Λ)`. -/
theorem RSpurionCovariant.coeff_scale {G₂ : ℂ → ℂ[X]} (h : RSpurionCovariant G₂)
    (t Λ : ℂ) (ht : t ≠ 0) (j : ℕ) :
    (G₂ (t * Λ)).coeff j * (t ^ 2) ^ j = t ^ 4 * (G₂ Λ).coeff j := by
  have hpoly : (G₂ (t * Λ)).comp (C (t ^ 2) * X) = C (t ^ 4) * G₂ Λ := by
    apply Polynomial.funext
    intro u
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    exact h.scale t Λ ht u
  have h1 := coeff_comp_C_mul_X (G₂ (t * Λ)) (t ^ 2) j
  rw [hpoly, Polynomial.coeff_C_mul] at h1
  exact h1.symm

/-- **The anomaly grading is a theorem** given R-spurion covariance: the count's one
non-manifest input dissolves into H5+H6-shaped physics. -/
theorem anomalyGraded_of_rSpurionCovariant {G₂ : ℂ → ℂ[X]} (h : RSpurionCovariant G₂)
    {Λ : ℂ} (hΛ : Λ ≠ 0) : AnomalyGraded (G₂ Λ) := by
  have hnormΛ : (0 : ℝ) < ‖Λ‖ := norm_pos_iff.mpr hΛ
  constructor
  · -- degree ≤ 2: a coefficient above u² would blow up at weak coupling
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    by_contra hc
    have hcpos : (0 : ℝ) < ‖(G₂ Λ).coeff j‖ := norm_pos_iff.mpr hc
    obtain ⟨L, hL⟩ := h.regular j
    obtain ⟨δ, hδ0, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hL) 1 one_pos
    -- pick the scale r₀ and the point s := r₀·Λ
    set B : ℝ := ‖(G₂ Λ).coeff j‖ / (2 * (‖L‖ + 1)) with hBdef
    have hBpos : 0 < B := by
      rw [hBdef]
      have : (0:ℝ) < ‖L‖ + 1 := by positivity
      positivity
    set r₀ : ℝ := min (min (1 / 2) (δ / (2 * ‖Λ‖))) (Real.sqrt B) with hr₀def
    have hr₀pos : 0 < r₀ := by
      rw [hr₀def]
      refine lt_min (lt_min (by norm_num) (by positivity)) (Real.sqrt_pos.mpr hBpos)
    have hr₀half : r₀ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hr₀δ : r₀ ≤ δ / (2 * ‖Λ‖) := (min_le_left _ _).trans (min_le_right _ _)
    have hr₀B : r₀ ^ 2 ≤ B := by
      have h1 : r₀ ≤ Real.sqrt B := min_le_right _ _
      calc r₀ ^ 2 ≤ Real.sqrt B ^ 2 := by
            exact pow_le_pow_left₀ hr₀pos.le h1 2
        _ = B := Real.sq_sqrt hBpos.le
    -- the scaled coefficient
    have hscale := h.coeff_scale (r₀ : ℂ) Λ (by exact_mod_cast hr₀pos.ne') j
    have hnorm : ‖(G₂ ((r₀ : ℂ) * Λ)).coeff j‖ * r₀ ^ (2 * j)
        = r₀ ^ 4 * ‖(G₂ Λ).coeff j‖ := by
      have := congrArg norm hscale
      simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr₀pos, ← pow_mul] using this
    -- the point is in the δ-window
    have hs0 : (r₀ : ℂ) * Λ ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hr₀pos.ne') hΛ
    have hsδ : dist ((r₀ : ℂ) * Λ) 0 < δ := by
      rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr₀pos]
      calc r₀ * ‖Λ‖ ≤ δ / (2 * ‖Λ‖) * ‖Λ‖ := by gcongr
        _ = δ / 2 := by field_simp
        _ < δ := by linarith
    have hbound : ‖(G₂ ((r₀ : ℂ) * Λ)).coeff j‖ ≤ ‖L‖ + 1 := by
      have h1 := hδ (by simpa using hs0) hsδ
      have h2 := norm_le_norm_add_norm_sub' ((G₂ ((r₀ : ℂ) * Λ)).coeff j) L
      rw [dist_eq_norm] at h1
      calc ‖(G₂ ((r₀ : ℂ) * Λ)).coeff j‖
          ≤ ‖L‖ + ‖(G₂ ((r₀ : ℂ) * Λ)).coeff j - L‖ := h2
        _ ≤ ‖L‖ + 1 := by linarith
    -- assemble the contradiction: r₀⁴‖c_j(Λ)‖ ≤ (‖L‖+1)·r₀^{2j} ≤ (‖L‖+1)·r₀⁶
    have hexp : r₀ ^ (2 * j) ≤ r₀ ^ 6 := by
      apply pow_le_pow_of_le_one hr₀pos.le (by linarith) (by omega)
    have hkey : r₀ ^ 4 * ‖(G₂ Λ).coeff j‖ ≤ (‖L‖ + 1) * r₀ ^ 6 := by
      calc r₀ ^ 4 * ‖(G₂ Λ).coeff j‖
          = ‖(G₂ ((r₀ : ℂ) * Λ)).coeff j‖ * r₀ ^ (2 * j) := hnorm.symm
        _ ≤ (‖L‖ + 1) * r₀ ^ (2 * j) :=
            mul_le_mul_of_nonneg_right hbound (by positivity)
        _ ≤ (‖L‖ + 1) * r₀ ^ 6 :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
    have hfinal : ‖(G₂ Λ).coeff j‖ ≤ (‖L‖ + 1) * r₀ ^ 2 := by
      have h4 : (0:ℝ) < r₀ ^ 4 := by positivity
      have hkey2 : r₀ ^ 4 * ‖(G₂ Λ).coeff j‖ ≤ r₀ ^ 4 * ((‖L‖ + 1) * r₀ ^ 2) := by
        calc r₀ ^ 4 * ‖(G₂ Λ).coeff j‖ ≤ (‖L‖ + 1) * r₀ ^ 6 := hkey
          _ = r₀ ^ 4 * ((‖L‖ + 1) * r₀ ^ 2) := by ring
      exact le_of_mul_le_mul_left hkey2 h4
    have hcontr : ‖(G₂ Λ).coeff j‖ ≤ ‖(G₂ Λ).coeff j‖ / 2 := by
      have h1 : (‖L‖ + 1) * r₀ ^ 2 ≤ (‖L‖ + 1) * B := by
        have : (0:ℝ) ≤ ‖L‖ + 1 := by positivity
        nlinarith [hr₀B]
      have h2 : (‖L‖ + 1) * B = ‖(G₂ Λ).coeff j‖ / 2 := by
        have hL1 : (0:ℝ) < ‖L‖ + 1 := by positivity
        rw [hBdef]
        field_simp
      linarith [hfinal]
    linarith
  · -- coeff 1 = 0: the half-instanton argument, purely algebraic
    have hscale := h.coeff_scale Complex.I Λ Complex.I_ne_zero 1
    rw [h.quantized Λ] at hscale
    have hI2 : (Complex.I ^ 2) ^ 1 = -1 := by
      simp [Complex.I_sq]
    have hI4 : Complex.I ^ 4 = 1 := by
      have : Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
      rw [this, Complex.I_sq]
      norm_num
    rw [hI2, hI4, one_mul, mul_neg_one] at hscale
    linear_combination -hscale / 2

/-- Non-vacuity: the `Γ⁰(4)`-frame SW family is R-spurion covariant. -/
theorem rSpurionCovariant_swG2' : RSpurionCovariant (fun Λ => swG2' Λ) where
  scale t Λ ht u := by
    simp only [swG2', Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  quantized Λ := by
    simp only [swG2']
    congr 1
    rw [mul_pow]
    have hI4 : Complex.I ^ 4 = 1 := by
      have : Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
      rw [this, Complex.I_sq]; norm_num
    rw [hI4, one_mul]
  regular j := by
    refine ⟨(swG2' 0).coeff j, ?_⟩
    have hcont : Continuous fun Λ : ℂ => (swG2' Λ).coeff j := by
      rcases eq_or_ne j 0 with rfl | hj0
      · simp only [swG2', Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_C]
        norm_num
        fun_prop
      · simp only [swG2', Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hj0]
        exact continuous_const

    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Non-vacuity: the `Γ(2)`-frame SW family is R-spurion covariant. -/
theorem rSpurionCovariant_swG2 : RSpurionCovariant (fun Λ => swG2 Λ) where
  scale t Λ ht u := by
    simp only [swG2, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  quantized Λ := by
    simp only [swG2]
    congr 1
    rw [mul_pow]
    have hI4 : Complex.I ^ 4 = 1 := by
      have : Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
      rw [this, Complex.I_sq]; norm_num
    rw [hI4, one_mul]
  regular j := by
    refine ⟨(swG2 0).coeff j, ?_⟩
    have hcont : Continuous fun Λ : ℂ => (swG2 Λ).coeff j := by
      rcases eq_or_ne j 0 with rfl | hj0
      · simp only [swG2, Polynomial.coeff_add, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_C]
        norm_num
        fun_prop
      · simp only [swG2, Polynomial.coeff_add, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hj0]
        exact continuous_const

    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

end SingularityCount
end SeibergWitten.Physics
