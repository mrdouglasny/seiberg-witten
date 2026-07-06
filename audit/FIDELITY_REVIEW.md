# Fidelity review — does each Lean statement faithfully capture its source?

Forward-chaining fidelity review (convention:
[`formalization-assurance/FIDELITY_REVIEW.md`](https://github.com/math-commons/formalization-assurance/blob/main/FIDELITY_REVIEW.md)).
The proofs are real; the risk is that a `proved`, axiom-clean theorem is the **wrong
statement** (dropped hypothesis, narrowed domain, branch/sign/normalization error). This
file records the verdict per entry and the numeric tier that backs it. The
**human-checkable digest** — informal claim next to verbatim Lean statement, quotes
machine-verified by [`check_faithfulness.py`](check_faithfulness.py) — is
[`FAITHFULNESS.md`](FAITHFULNESS.md); a reviewer should start there, not here.
Companions:
[`CORRESPONDENCE_INDEX.md`](CORRESPONDENCE_INDEX.md) (coverage), [`PROOF_STATUS.md`](PROOF_STATUS.md)
(remaining gaps), [`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md).

## Numeric tier — independent oracle (mpmath / numpy)

Nine suites in [`numerical/`](numerical/), **278 checks in all** at 30–40-digit
precision, each with its `.out.txt` committed (the oracle shares no provenance with the
Lean — independent θ-series / quadrature in Python):

| suite | checks | vets |
|---|---|---|
| `validate_lambda` | 44/44 | θ pair axioms; the λ laws; `λ(i)=½` normalization; `su2_singular_locus` |
| `validate_elliptic` | 92/92 | the elliptic-integral layer (`AX_elliptic_inversion` etc.), Legendre, cusp constants |
| `validate_swcrossratio` | 16/16 | the modulus map `m(u) = 2Λ²/(u+Λ²)` **determined** against curve periods (six Möbius candidates) |
| `validate_specialcoords` | 14/14 | the closed-form `a, a_D` against `∮λ_SW` quadrature (unique-match bracket) |
| `validate_taulayer` | 21/21 | the τ-derivative layer: Wronskian, `dτ/du`, one-loop running |
| `validate_matterj` | 26/26 | the matter `j`-route: anharmonic invariance, Landen factor 2 (+ must-fail), AD point |
| `validate_singcount` | 33/33 | the Kodaira transcriptions: valuations, Euler totals, `j`-pole dictionary, the **K3 loophole witness** |
| `validate_devbase` | 13/13 | `SWModulusData` non-vacuity + the degree-2 must-fail at `u = −3Λ²` |
| `validate_cuspdata` | 19/19 | the λ-frame monodromies: **parabolicity (trace) and fixed cusps** (added after the B7 finding), invariance, width-2 |

The founding suite's coverage in detail:

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

### Finding (recorded): a transcription slip the oracle missed — B7

The first λ-frame dyon monodromy was **hyperbolic** (trace −6) in a parabolic slot. It
passed every oracle check then present — determinant, mod-2 reduction, the factorization,
numerical λ-invariance — because a hyperbolic `Γ(2)` element satisfies all the properties
the *proofs consume*. Caught during the endgame design (the fixed point came out real);
repaired with the parabolic pair, proved trace lemmas (`swM*_trace`), and new oracle
checks (trace, fixed cusps). Lesson (`DIFFICULT_POINTS.md` B7): *pin the invariants that
classify a transcribed object, not just the ones downstream proofs use.* This is the
fidelity axis's sharpest lesson to date: statement-level classification checks belong in
the oracle alongside value checks.

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
  smoothness hypothesis is the honest `Squarefree f` (not glossed). *Scope note
  (2026-07-06): lives in the unbuilt `HigherGenus/` layer since the jacobian-challenge
  decoupling; not on any certified footprint.*
- **`su2_singular_locus`** — faithful. Singularity ⟺ `¬Squarefree` is the standard
  hyperelliptic criterion; the `Λ ≠ 0` hypothesis is real (at `Λ=0` the curve is
  everywhere singular). Numeric: ✓ (root-gap at `±Λ²` vanishes, bounded away elsewhere).
- **`sw_coupling_mem_siegel*`, `sw_metric_posDef`** — faithful at the type level: `Im τ ≻ 0`
  is `Matrix.PosDef` of the entrywise imaginary part, the correct special-Kähler positivity.
  Existence statements (∃ τ ∈ Siegel), so no numeric content. *Scope note (2026-07-06):
  `HigherGenus/`, as above.*
- **`transvection_isSymplectic`** — faithful: `IsSymplectic f := ∀ v w, ⟨f v, f w⟩ = ⟨v,w⟩`
  with `⟨·,·⟩ = diracPairing`, and `transvection γ v = v + ⟨v,γ⟩•γ` is the Picard–Lefschetz
  reflection. Note: stated for the **generic** stratum (`PicardLefschetzAtGenericSingularities`),
  correctly excluding the Argyres–Douglas strata.
- **`modularLambdaFn` and the λ laws** — faithful; numeric ✓ (table above). The θ-null
  definitions match Mathlib's `jacobiTheta₂` convention (`q = exp(πiτ)`); `λ(i)=1/2` confirms
  they are the standard nulls, so `AX_jacobi_quartic` etc. are statements about the *real* λ.
- **`sw_su2_unique`** — faithful as a *conditional* statement: it is the rank-1 case of
  `sw_effective_theory_unique_up_to_duality`, with the uniformization input named explicitly
  (`AX_thrice_punctured_uniformization`, `AX_developing_map_rigidity`) and the monodromy hypothesis as the *defined* `SameSWMonodromy` (demoted from an axiom 2026-07-04). The
  "up to `Sp(2,ℤ)`" is essential (periods are frame-dependent) and is present.

- **The Kodaira transcriptions** (`IsKodairaI`, `InftyIStar`; SingularityCount.lean) —
  faithful *as dictionary entries*: the physics↔valuations bridge is Kodaira's table,
  cited not formalized; validated four ways (instantiation on both frames with the
  Landen consistency; oracle joints; agreement with the direct discriminant computation;
  parabolic monodromy matrices carrying the assigned classes). The paper's §5
  "Validating a transcription" paragraph is this entry's write-up. Residual trust:
  Kodaira's table; H3 ⇒ local monodromy class.
- **`AnomalyGraded` / `RSpurionCovariant` / H7 (`SpurionCovariantFamily`)** — faithful
  chain: H7 states the family covariance with the Witten-effect shift pinned to an
  integer symmetric matrix *constant across the family* (existential outside all
  quantifiers — the B6 anti-absorption pattern); `RSpurionCovariant` is its curve-level
  shadow; `AnomalyGraded` is a theorem from it. Non-vacuity Lean-proved on both frames.
- **`SWModulusData` → `swModulusData_eq_crossRatio`** — faithful and *qualitative*: three
  limits and two omitted values only; degree, rates, and the `2Λ²` normalization are
  conclusions. Both-ways numeric vetting (`validate_devbase`: the degree-2 candidate
  fails exactly the omit-1 clause at a smooth point).
- **The cusp-data layer** (`IsSWCouplingAtlas`, `IsGenuineCuspLift`,
  `swModulusData_of_atlas_and_lifts`) — faithful transcriptions of H4 (pointwise gluing,
  weaker than locally-constant: hypothesis-weakening only), H3 (parabolic equivariance
  `T(w+1)=T(w)+k`, `k` free), H2/H6-qual (non-extension, NOT a rate — the D3 trap
  deliberately avoided).
- **`matter_coupling_rigidity`** — faithful (the `j`-anchored developing condition; the
  Landen factor 2 numerically pinned with a must-fail witness).
- **`matterPeriodRigidity_nf1_ad` / `matter_argyresDouglasLocus_nonempty`** — faithful
  *with a stated caveat*: the constructed chart is a disclosed **non-SQCD witness**;
  the theorem exhibits *a* theory with the AD phenomenon, and the predicate's
  under-specification (H1 + Δ-tie) is now a formal fact, not a gloss.

## Physics inputs — predicates, not axioms (updated 2026-07-06)

There are **no physics axioms** in the development: the H0–H7 content is carried as
named predicates and structures in theorem types (`SameSWMonodromy`, the last physical
axiom, was demoted to a definition 2026-07-04; `matterPeriodRigidityAxiom`, the last
matter-side axiom, was discharged 2026-07-06). The `axiom` declarations that remain are
classical mathematics (covering pair, Jacobi inversion, θ pair) plus the higher-rank
`periodRigidityAxiom` (future work); each is numerically vetted where it has computable
content (tables above) and tracked per theorem by the golden trace. The original
codified-lore review (Gemini `GR`, 2026-06-24 — the cover/Liouville,
Picard–Lefschetz-generic-stratum, and R-symmetry corrections) applied to the
predecessors of today's predicates and remains the provenance of those fields' typing.
