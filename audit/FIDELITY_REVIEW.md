# Fidelity review — does each Lean statement faithfully capture its source?

Forward-chaining fidelity review (convention:
[`formalization-assurance/FIDELITY_REVIEW.md`](https://github.com/math-commons/formalization-assurance/blob/main/FIDELITY_REVIEW.md)).
The proofs are real; the risk is that a `proved`, axiom-clean theorem is the **wrong
statement** (dropped hypothesis, narrowed domain, branch/sign/normalization error). This
file records the verdict per entry and the numeric tier that backs it. Companions:
[`CORRESPONDENCE_INDEX.md`](CORRESPONDENCE_INDEX.md) (coverage), [`PROOF_STATUS.md`](PROOF_STATUS.md)
(remaining gaps), [`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md).

## Numeric tier — independent oracle (mpmath / numpy)

Script [`numerical/validate_lambda.py`](numerical/validate_lambda.py), output
[`validate_lambda.out.txt`](numerical/validate_lambda.out.txt): **44/44 pass** at
`dps=40`, residuals `≲ 1e-40`. The oracle shares no provenance with the Lean (independent
θ-series in Python). It checks, at high-precision sample points in `ℍ`:

| Lean entry | identity checked | role |
|---|---|---|
| `AX_jacobi_quartic` | `θ₃⁴ = θ₂⁴ + θ₄⁴` | **axiom vetting** — the assumed axiom is numerically true |
| `AX_theta3_ne_zero` | `θ₃ ≠ 0` | axiom vetting (partial — sampled points only) |
| `oneMinusLambda` | `1 − λ = θ₄⁴/θ₃⁴` | statement faithfulness |
| `modularLambda_add_two` | `λ(τ+2) = λ(τ)` | statement faithfulness (catches a wrong shift / factor) |
| `modularLambda_S` | `λ(-1/τ) = 1 − λ(τ)` | statement faithfulness (catches `1−λ` vs `λ−1`, sign) |
| `modularLambda_ST2S` | `λ(-1/(-1/τ+2)) = λ(τ)` | statement faithfulness (the 2nd `Γ(2)` generator) |
| `modularLambdaFn` convention | `λ(i) = 1/2` | pins the θ-null normalization to the standard one |
| `su2_singular_locus` | `(x²−u)²−Λ⁴` has a repeated root ⟺ `u=±Λ²` | statement faithfulness (numpy root gaps) |

**What this rules out:** that our `θ₂,θ₃,θ₄` are mis-normalized, that the quartic axiom is
false, that any λ transformation law has a wrong sign/shift, or that the singularity
locus is mis-stated. **What it does not:** logical-structure faithfulness — quantifier
scope, hypothesis strength, vacuity, and the *global* truth of `θ₃≠0` (sampling is
necessary, not sufficient; per NUMERICAL_VALIDATION.md §boundary).

### Finding (recorded): the oracle caught a branch bug — in the oracle

First implementation computed `θ₂ = Σ q^{(n+½)²}` with reduced nome `q = exp(πiτ)`, routing
the **half-integer power** through a principal fractional power; at transformed arguments
(`-1/τ`, `τ+2`) this picked the wrong branch and the transformation laws *failed*
numerically. Fix: evaluate each term as a single-valued `exp(πiτ·k)` of the full argument.
A second artifact — feeding *double-precision* sample points limited residuals to `~1e-16`
(the transformed args inherit input error) — was fixed by using `mpmath` complex samples.
Both were bugs in the **oracle**, not the Lean; the episode is the method demonstrating its
own value (a sign/branch sensitivity check that actually bites). The corrected oracle agrees
with the Lean statements to full working precision.

## Statement-faithfulness verdicts

All entries reviewed by self-audit against the pinned sources; the load-bearing
type-level conventions are noted. No `flagged` entries.

- **`genus_swCurve`, `genus_swCurve_su2`** — faithful. The curve is the
  `HyperellipticEvenProj` of `f = P² − C(Λ^{2N})`; genus `= N−1` by degree count. The
  smoothness hypothesis is the honest `Squarefree f` (not glossed).
- **`su2_singular_locus`** — faithful. Singularity ⟺ `¬Squarefree` is the standard
  hyperelliptic criterion; the `Λ ≠ 0` hypothesis is real (at `Λ=0` the curve is
  everywhere singular). Numeric: ✓ (root-gap at `±Λ²` vanishes, bounded away elsewhere).
- **`sw_coupling_mem_siegel*`, `sw_metric_posDef`** — faithful at the type level: `Im τ ≻ 0`
  is `Matrix.PosDef` of the entrywise imaginary part, the correct special-Kähler positivity.
  Existence statements (∃ τ ∈ Siegel), so no numeric content.
- **`transvection_isSymplectic`** — faithful: `IsSymplectic f := ∀ v w, ⟨f v, f w⟩ = ⟨v,w⟩`
  with `⟨·,·⟩ = diracPairing`, and `transvection γ v = v + ⟨v,γ⟩•γ` is the Picard–Lefschetz
  reflection. Note: stated for the **generic** stratum (`PicardLefschetzAtGenericSingularities`),
  correctly excluding the Argyres–Douglas strata.
- **`modularLambdaFn` and the λ laws** — faithful; numeric ✓ (table above). The θ-null
  definitions match Mathlib's `jacobiTheta₂` convention (`q = exp(πiτ)`); `λ(i)=1/2` confirms
  they are the standard nulls, so `AX_jacobi_quartic` etc. are statements about the *real* λ.
- **`sw_su2_unique`** — faithful as a *conditional* statement: it is the rank-1 case of
  `sw_effective_theory_unique_up_to_duality`, with the uniformization input named explicitly
  (`AX_su2_modular_frame_alignment`) and the monodromy hypothesis as `SameSWMonodromy`. The
  "up to `Sp(2,ℤ)`" is essential (periods are frame-dependent) and is present.

## Codified-lore axioms (physics inputs — vetted, not removed)

The `Physics/Hypotheses.lean` axioms are deliberate codified lore (see
[`../docs/foundations-for-physical-reasoning.md`](../docs/foundations-for-physical-reasoning.md)),
reviewed by Gemini (`GR`, 2026-06-24) for correct typing / non-vacuity — the cover/Liouville,
Picard–Lefschetz-generic-stratum, and R-symmetry corrections came from that review. They are
*not* in scope for numeric vetting (abstract/structural, no computable content).
