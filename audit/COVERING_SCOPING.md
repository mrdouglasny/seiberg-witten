# Scoping: the covering surjectivity / fibres of `λ`

*The remaining content of `AX_thrice_punctured_uniformization` (`ModularLambda.lean`)
after its `Γ(2)`-invariance clause was proved (`modularLambda_{add_two,S,ST2S}`). This is
the clause that actually gates axiom-free `sw_su2_unique`. Decomposes the proof, maps each
step to Mathlib, and identifies the critical path. Companion to [`PROOF_STATUS.md`](PROOF_STATUS.md).*

## What remains to prove

`ThricePuncturedUniformization` (the structure) still needs, for the concrete
`modularLambdaFn = θ₂⁴/θ₃⁴`:

- **(R) range** — `λ : ℍ → ℂ∖{0,1}` is well-defined: `λ(τ) ∉ {0,1}` for all `τ ∈ ℍ`;
- **(S) surjectivity** — `λ` is onto `ℂ∖{0,1}`;
- **(F) fibres** — `λ(τ) = λ(τ') ↔ ∃ γ ∈ Γ(2), γ·τ = τ'`.

(The `Γ(2)`-invariance — the `←` of (F) restricted to generators — is proved.)

## The classical proof route (fundamental-domain / Schwarz reflection)

The standard argument (Ahlfors *Conformal Invariants* §7; Diamond–Shurman §1):

1. `Γ(2)` has fundamental domain the ideal "double triangle" with vertices the cusps
   `0, 1, ∞`. `λ` maps the open right half of it biholomorphically onto the **upper** half
   plane, with the three cusps `→ 1, ∞, 0` (the boundary `ℝ ∪ {∞}` going to `ℝ`).
2. **Schwarz reflection** across the boundary edges extends this to a biholomorphism of the
   full fundamental domain onto `ℂ ∖ {0,1}` (upper ∪ lower half planes glued along `ℝ`).
3. Tiling `ℍ` by `Γ(2)`-translates of the fundamental domain ⇒ `λ` is a covering map
   `ℍ → ℂ∖{0,1}`; `ℍ` simply connected ⇒ it is the **universal cover** with deck group
   `Γ(2)`. (S) and (F) then follow from covering-space theory.

An equivalent route inverts `λ` as a **Schwarz triangle / hypergeometric** map of the ideal
`(0,0,0)` triangle; same missing ingredients.

## Decomposition → Mathlib availability

| Step | Statement | Mathlib status |
|---|---|---|
| (R0) | `θ₂ ≠ 0`, `θ₄ ≠ 0` on `ℍ` ⇒ `λ ∉ {0,1}` (via `oneMinusLambda`) | **gap** — non-vanishing; triple-product-adjacent (cf. `AX_theta3_ne_zero`). η-route blocked (connecting sum-θ to product-η *is* the triple product). |
| (H) | `λ` holomorphic on `ℍ` | reachable — `jacobiTheta₂` is differentiable (`jacobiTheta₂_fderiv`); quotient by `θ₃⁴≠0`. |
| (O) | `λ(ℍ)` is **open** | **reachable** — `AnalyticOnNhd.is_constant_or_isOpenMap` + `λ` non-constant. *First buildable increment.* |
| (L) | `λ` is a **local biholomorphism** (`λ′ ≠ 0`) off the cusps | hard — needs `λ′` non-vanishing; no direct Mathlib lemma. |
| (FD) | fundamental domain of `Γ(2)` | **absent** — Mathlib has the **SL(2,ℤ)** domain (`ModularGroup.fd`, `exists_smul_mem_fd`), not `Γ(2)`. |
| (SR) | Schwarz reflection across `ℝ` | **absent** — no Schwarz reflection / reflection principle in Mathlib. |
| (RMT)| Riemann mapping (alt. route) | **absent**. |
| (CM) | `λ` is a covering map `ℍ → ℂ∖{0,1}` | **gap** — `IsCoveringMap` *exists* (`Topology/Covering`), but proving `λ` is one needs (FD)+(SR) or (RMT). |
| (S) | surjectivity from (CM) + connectedness | reachable *given* (CM): image open (O) + closed (properness) on a connected base. Properness is the work. |
| (Γgen) | `Γ(2) = ⟨T², ST²S⁻¹⟩` (free) | **absent** — no `Γ(2)` generator/presentation result. Needed for *full* invariance and for deck `= Γ(2)`. |
| (F) | fibres `=` `Γ(2)`-orbits from (CM) + simply-connected `ℍ` | **gap** — needs deck-group/Galois-correspondence theory (`ℍ` universal ⇒ deck acts simply-transitively on fibres) + (Γgen); Mathlib's covering-Galois layer is thin. |

## Critical path & assessment

The blockers, roughly in order of how much they hold things up:

1. **Schwarz reflection / Riemann mapping** (SR/RMT) — the analytic heart; **absent from
   Mathlib**. Without one of these (or an equivalent), step 1–2 of the route can't run.
2. **`Γ(2)` fundamental domain** (FD) and **generators/presentation** (Γgen) — **absent**;
   the SL(2,ℤ) versions exist but don't transfer directly.
3. **Covering-space Galois correspondence** (deck group, universal-cover classification,
   fibres = deck orbits) — only **partial** in Mathlib.

This is **the hardest of the three residual gaps** (more than the triple product, more than
the family layer): it is not one development but a *cluster* of absent complex-analysis and
modular-geometry machinery (Schwarz reflection, `Γ(2)` domain + generators, covering Galois),
each a standalone contribution. Realistic effort: **multi-month**, and most of it is general
upstream Mathlib work, not SW-specific.

## Recommended increments (what is actually buildable here)

1. **(O) `λ(ℍ)` is open** — provable now from the open mapping theorem once `λ`'s
   analyticity on `ℍ` (H) is set up; a genuine first step toward (S). Low-risk.
2. **(H) `λ` holomorphic on `ℍ`** — assemble from `jacobiTheta₂` differentiability + `θ₃≠0`.
3. The deep pieces (SR, FD, Γgen, CM, F) should be pursued as **upstream Mathlib
   contributions** (Schwarz reflection and the `Γ(2)` fundamental domain are the highest-
   leverage and broadly useful), not inlined here.

## Recommendation

If the priority is axiom-free `sw_su2_unique`, the covering is a **multi-month, multi-piece**
effort dominated by missing upstream machinery — the largest single investment of the three
gaps. The **Schwarz reflection principle** is the keystone and the right first upstream
target (it also unlocks much else). Within this repo, only (O)/(H) are buildable now and
worth doing as the proved foothold; the rest should wait on (or drive) the Mathlib additions.
Compared with the triple product (self-contained, days–weeks), the covering is the more
fundamental but far larger commitment.
