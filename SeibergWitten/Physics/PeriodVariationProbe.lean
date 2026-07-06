/-
# P1/P2 probe: is the holomorphic variation of a period integral reachable from Mathlib?

`audit/PERIOD_LAYER_SCOPING.md` identifies **P1/P2** — that period integrals `∮ λ_SW` vary
*holomorphically* with the modulus `u` (the Gauss–Manin connection) — as the one piece of the
period layer with no Lean precedent. This file probes it: a Seiberg–Witten period is an integral
`a(u) = ∫_γ F(u, x) dx` whose integrand is holomorphic in `u`; the question is whether the
*integral* is then holomorphic in `u`.

**Measured finding.** Yes — Mathlib's `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
delivers exactly this. Below it is discharged end-to-end for a model integrand `exp(u·t)` (entire
in `u`, like the SW integrand away from its branch points), giving `HasDerivAt`/`Differentiable`
of the parameter integral with **no axioms** (standard-3). The friction is entirely in the
*domination* hypothesis (a uniform integrable bound on `∂F/∂u` over a neighbourhood of `u₀`),
discharged here from compactness of the contour + continuity.

**What remains SW-specific** (not a fundamental obstruction, standard analysis):
* the integrand `((x²−u)²−Λ⁴)^(−1/2)` is holomorphic in `u` on the smooth locus — `cpow` away
  from its branch cut (a per-`x` statement);
* the domination across the *integrable* `√`-singularity at the branch points (the A-cycle runs
  between turning points), rather than the bounded model integrand here.
Both plug into the same lemma; the machinery itself is confirmed reachable.
-/
import Mathlib

namespace SeibergWitten.Physics

open MeasureTheory Complex Filter Topology

/-- **The machinery works (P1/P2).** The parameter integral of a `u`-holomorphic family has a
complex derivative in `u` — here for the model integrand `exp(u·t)` over a fixed contour `[0,1]`,
via Mathlib's dominated-derivative lemma for interval integrals. The derivative is the integral
of the `u`-derivative (differentiation under the integral sign), exactly the statement P1/P2 needs
for the Seiberg–Witten periods. -/
theorem model_period_hasDerivAt (u₀ : ℂ) :
    HasDerivAt (fun u : ℂ => ∫ t in (0:ℝ)..1, Complex.exp (u * t))
      (∫ t in (0:ℝ)..1, (t : ℂ) * Complex.exp (u₀ * t)) u₀ := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0:ℝ)) (b := 1) (μ := volume)
    (F := fun (u : ℂ) (t : ℝ) => Complex.exp (u * t))
    (F' := fun (u : ℂ) (t : ℝ) => (t : ℂ) * Complex.exp (u * t))
    (x₀ := u₀) (s := Metric.ball u₀ 1) (bound := fun _ => Real.exp (‖u₀‖ + 1))
    (Metric.ball_mem_nhds u₀ one_pos)
    (Eventually.of_forall fun u =>
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable 0 1)
    ((Complex.continuous_ofReal.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable)
    (by
      refine ae_of_all _ fun t ht u hu => ?_
      rw [Set.mem_uIoc] at ht
      have ht01 : t ∈ Set.Icc (0:ℝ) 1 := by
        rcases ht with ⟨h1,h2⟩|⟨h1,h2⟩ <;> constructor <;> linarith
      rw [norm_mul, Complex.norm_real, Complex.norm_exp]
      have hre : (u * (t:ℂ)).re = u.re * t := by simp [Complex.mul_re]
      rw [hre]
      have hure : u.re ≤ ‖u₀‖ + 1 := by
        have hlt : ‖u‖ < ‖u₀‖ + 1 := by
          have hb := Metric.mem_ball.mp hu; rw [Complex.dist_eq] at hb
          calc ‖u‖ ≤ ‖u - u₀‖ + ‖u₀‖ := by simpa using norm_add_le (u - u₀) u₀
            _ < 1 + ‖u₀‖ := by linarith
            _ = ‖u₀‖ + 1 := by ring
        exact le_of_lt (lt_of_le_of_lt (Complex.re_le_norm u) hlt)
      have hbound : u.re * t ≤ ‖u₀‖ + 1 := by
        rcases le_total 0 u.re with h | h
        · nlinarith [mul_le_mul_of_nonneg_left ht01.2 h, hure]
        · nlinarith [mul_nonpos_of_nonpos_of_nonneg h ht01.1, norm_nonneg u₀]
      have htabs : |t| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [ht01.1], ht01.2⟩
      calc |t| * Real.exp (u.re * t) ≤ 1 * Real.exp (‖u₀‖ + 1) := by gcongr
        _ = Real.exp (‖u₀‖ + 1) := one_mul _)
    (intervalIntegral.intervalIntegrable_const)
    (ae_of_all _ fun t _ u _ => by
      simpa [mul_comm] using (((hasDerivAt_id u).mul_const (t:ℂ)).cexp))
  exact key.2

/-- The model period is holomorphic (`Differentiable ℂ`) in the modulus — P1/P2 for the model. -/
theorem model_period_differentiable :
    Differentiable ℂ (fun u : ℂ => ∫ t in (0:ℝ)..1, Complex.exp (u * t)) :=
  fun u₀ => (model_period_hasDerivAt u₀).differentiableAt

end SeibergWitten.Physics
