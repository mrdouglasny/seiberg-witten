# Reviewer's guide — checking this project's claims

*Entry point for a human (physicist) reviewer. Everything below is checkable without
trusting the authors: the kernel checks the proofs, a script checks the axiom
inventory, and an independent oracle checks the numbers. Last updated 2026-07-06.*

The claim (scoped per the 2026-07-06 external claim review, archived in the local `history/`): **for SU(2), the main compiled
Lean development proves the listed Seiberg–Witten consequences without `sorry` and
without hidden physics axioms — physics enters through explicit H0–H7 predicates,
structures, definitions, and stated dictionary transcriptions; the remaining trusted
inputs beyond standard-3 are explicitly named classical-mathematical axioms, tracked
per theorem by `audit/axiom-report.txt`. The higher-rank headline is a proved skeleton
modulo the coarse period-geometry axiom `periodRigidityAxiom`, whose discharge is
future work.** The companion paper (`docs/paper1.tex`) argues the physics; this guide
indexes the evidence.

## The claims, and what each rests on

"standard-3" = the three logical axioms every classical Lean proof uses
(`propext`, `Classical.choice`, `Quot.sound`). They are part of Lean's logic, not
project assumptions. Everything else a theorem uses is listed in the golden trace
[`axiom-report.txt`](axiom-report.txt), machine-generated from
[`axiom_report.lean`](axiom_report.lean) — the counts below are read from it.

| Claim (physics language) | Lean theorem | Beyond standard-3 |
|---|---|---|
| The SW curve realizes an N=2 U(1)^{N-1} effective theory satisfying H0–H6 | `sw_curve_admits_effective_theory` | `periodRigidityAxiom` |
| H0–H6 fix that theory **uniquely up to Sp(2(N−1),ℤ) EM duality** | `sw_effective_theory_unique_up_to_duality`, atlas-level `sw_unique_up_to_duality` | `periodRigidityAxiom` |
| Rank-1 (SU(2)) uniqueness, finer footprint | `sw_su2_unique` | `AX_thrice_punctured_uniformization`, `AX_developing_map_rigidity` (classical math; the physics — `SameSWMonodromy` — is a *defined* hypothesis, no longer an axiom) |
| The SU(N) curve has genus N−1 | `genus_swCurve` | — (axiom-free) |
| Special-Kähler positivity: τ = τᵀ, Im τ ≻ 0 | `sw_metric_posDef`, `sw_coupling_mem_siegel*` | `AX_PeriodCycleBasis` (inherited, see below) |
| SU(2) curve singular **exactly** at u = ±Λ² (monopole/dyon) | `su2_singular_locus` | — (axiom-free) |
| **`matterPeriodRigidityAxiom` discharged**: the first constructed `PeriodChart` (tangent ball at the AD point; exact two-point singular locus via the quartic-discriminant bridge; unique cusp; both unit charges' central charges vanish) — with the DISCLOSURE that the witness is non-SQCD, making the predicate's under-specification formal | `matterPeriodRigidity_nf1_ad`, `matter_argyresDouglasLocus_nonempty` | — (**axiom-free**, was + matterPeriodRigidityAxiom) |
| **The cusp data derived from H-level inputs**: atlas gluing (H4) + parabolic cusp lifts with non-extension (H2/H3, H6-qual) ⇒ `SWModulusData`; parabolicity now a *proved* faithfulness check (`swM*_trace` — the v1 dyon slip is B7) | `swModulusData_of_atlas_and_lifts`, `cusp_dichotomy` | dichotomy axiom-free; rest θ-pair (`validate_cuspdata.py` 19/19) |
| **The monodromy postulate demoted to a theorem**: the pinned developing formula follows from qualitative cusp data (`SWModulusData`: 3 limits, 2 omitted values) via removability + polynomial-growth Liouville; the `2Λ²` normalization is derived, not chosen | `swModulusData_eq_crossRatio`, `sw_su2_unique_of_modulusData` | — derivation axiom-free; headline: covering pair only (`validate_devbase.py` 13/13) |
| **Exactly one monopole–dyon pair** (`n = 1`, not assumed): counting (`12l−(m+6)`; alone gives only `n ≡ 1 mod 6` — K3 loophole witnessed) + homogeneity (`deg g₂ ≤ 2` from holomorphy + dimensions + ℤ₈ anomaly) pinch the count | `singularity_count_pinch`, `sw_exactly_two_singularities'`, `sw_singular_values` | — (axiom-free; `validate_singcount.py` 33/33) |
| Picard–Lefschetz monodromy is symplectic (why Sp(2r,ℤ)) | `transvection_isSymplectic` | — (axiom-free) |
| N_f=1 SQCD has an Argyres–Douglas cusp at (u,m)=(¾Λ², −¾Λ); pure SU(2) has none | `swCurveMatter_nf1_ad`, `not_isCuspOf_nf0` | — (axiom-free, pure algebra) |
| The AD locus (mutually non-local massless states) is nonempty with matter | `matter_argyresDouglasLocus_nonempty` | `matterPeriodRigidityAxiom` |
| One-loop beta function b₀ = 4 − N_f (existential form — see caveat in AXIOM_AUDIT) | `betaFunction_weakCoupling` | — (**axiom-free**; the log-running input was discharged 2026-07-05 by an explicit witness, exposing that the statement never tied `F` to the curve) |
| **SU(2) coupling exists** (explicit elliptic construction, open nonempty chart) | `su2_coupling_exists` | `AX_elliptic_inversion` (classical: Jacobi inversion) |
| **SU(2) coupling unique up to Γ(2)** — every developing map = `swTau` up to a Möbius frame | `su2_coupling_canonical` | `AX_elliptic_inversion` + the covering pair — classical only |
| The Legendre relation `E·K′+E′·K−K·K′ = π/2` (was axiom C2 — **discharged**) | `legendre_relation` | — (**axiom-free**; the C3 cusp clause it consumed was discharged 2026-07-05) |
| Closed-form `da/du`, `da_D/du` on the SU(2) chart | `swA_hasDerivAt`, `swAD_hasDerivAt` | — (axiom-free) |
| **Special geometry `da_D/da = τ`** (H1's relation, explicit SU(2) solution) | `swAD_deriv_eq_swTau_mul_swA_deriv` | `AX_elliptic_inversion` (only its `K ≠ 0` clause) |
| Coupling derivative in closed form: `dτ/du = iπ/(4(u+Λ²)(1−m)K²)` (Wronskian/Legendre) | `swTau_hasDerivAt` | `AX_elliptic_inversion` (`K ≠ 0`) |
| **Faithful one-loop log-running**: `u·τ′(u) → i/π` for the *actual* coupling (curve-tied; λ-normalization) | `swTau_logDeriv_weakCoupling` | `AX_elliptic_inversion` |
| **Matter (N_f > 0) coupling rigidity**: two `j`-developing couplings agree on the chart up to `Γ(2)` × an anharmonic word | `matter_coupling_rigidity` | θ pair + covering pair — **no matter-specific axiom** |
| The N_f=1 AD point as the invariant statement `g₂ = g₃ = 0` | `matter_nf1_ad_invariants` | — (axiom-free, two independent proofs) |

The physical hypotheses H0–H6 do **not** appear in these lists because they are not
global axioms: they are predicates carried in each theorem's statement (bundled as
`IsPolarizedPeriodChart`), so they are visible in the theorem's type, not hidden in
the trusted base. Their Lean definitions are in
`SeibergWitten/Physics/Hypotheses.lean`; their physical justification is §4.2 and
Appendix A of the paper.

## Verify it yourself — three commands

1. **The proofs are real** (kernel check; needs a sibling `jacobian-challenge`
   checkout — see [`../BUILD.md`](../BUILD.md)):
   ```bash
   lake build SeibergWitten
   ```
2. **The axiom inventory is exactly as stated** (regenerates the `#print axioms`
   trace and diffs it against the golden file):
   ```bash
   bash audit/gen_axiom_report.sh --check
   ```
3. **The computable content is true** (independent mpmath/numpy oracle, no shared
   provenance with the Lean; 44/44 checks at 40-digit precision):
   ```bash
   cd audit/numerical && python3 validate_lambda.py   # needs mpmath, numpy
   ```
4. **The faithfulness digest quotes the real code** (every Lean statement quoted in
   `FAITHFULNESS.md` is diffed verbatim against the source tree):
   ```bash
   python3 audit/check_faithfulness.py
   ```

## Where each verdict lives

- [`FAITHFULNESS.md`](FAITHFULNESS.md) — **start here**: informal claim placed
  directly next to the verbatim Lean statement (machine-checked against the source
  by `check_faithfulness.py`), with the specific place misformalization could hide
  called out per entry. Covers all three layers: the physics hypotheses H0–H6
  (Part I), the mathematical axioms (Part II — where the statement *is* the entire
  content), and the proved theorems E1–E11 (Part III, cross-referenced to the
  paper's numbering). The informal ↔ formal comparison is the one judgment only a
  human can make; this file is built so it takes minutes, not a repo excavation.
- [`CORRESPONDENCE_INDEX.md`](CORRESPONDENCE_INDEX.md) — the claim-by-claim map:
  informal source (SW / KLYT / Argyres–Faraggi / Lerche) ↔ Lean declaration ↔
  proved/absent ↔ fidelity ↔ numeric check (exhaustive index behind the digest).
- [`FIDELITY_REVIEW.md`](FIDELITY_REVIEW.md) — does each Lean statement say what the
  source says (sign, branch, normalization, quantifier strength), and what the
  numerical oracle does and does not rule out.
- [`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md) — every axiom with its rating, source,
  and discharge plan; the H5 (R-symmetry order) correction history.
- `docs/paper1.tex` — the physics case for H0–H6 and the math–physics separation.

## Known gaps — read before objecting

Stated here so the reviewer does not have to discover them:

- **The big one:** `periodRigidityAxiom` — the existence/rigidity of the period
  geometry of the curve family (Gauss–Manin / Picard–Fuchs variation). This is
  honest mathematical debt, classical but absent from Lean's libraries; discharge is
  in progress ([`PERIOD_LAYER_DISCHARGE.md`](PERIOD_LAYER_DISCHARGE.md)). The
  headline theorems are conditional on it — indeed largely *stated* by it (see
  `FAITHFULNESS.md` Part II B.1).
- **Every mathematical axiom has a documented discharge route** — see the
  discharge map in [`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md) (axiom → route → plan
  document → effort).
- The prepotential/periods row of the correspondence index is **absent** (coverage
  7/9): `a, a_D = ∮λ_SW` with `a_D = ∂F/∂a` is built only through the genus-1
  analytic engine so far.
- The numerical oracle covers the θ/λ layer, the SU(2) singularity locus, the
  elliptic-integral axioms (`validate_elliptic.py`, 92/92), the pinned modulus
  (`validate_swcrossratio.py`), and the special coordinates against honest `∮ λ_SW`
  quadrature (`validate_specialcoords.py`, 14/14, `da_D/da = swTau` to `1e−15`), and
  the proved τ-derivative layer (`validate_taulayer.py`, 21/21: the Wronskian
  formula, the closed-form `dτ/du`, and the `u·τ′ → i/π` constant with its `O(1/u)`
  rate, on- and off-axis), and the matter j-invariant layer
  (`validate_matterj.py`, 26/26: coefficient-side = root-side = τ-side `j` for
  `N_f = 0, 1`; the Landen factor-2 witness; `g₂ = g₃ = 0` at the AD point; the
  MC3 chart hypotheses satisfiable with margins ~0.06).
- `SameSWMonodromy` (which monopole/dyon monodromies occur) was demoted from an
  axiom to a definition (2026-07-04): both couplings develop the curve's pinned
  modulus `swCrossRatio`. No physics axiom remains on the rank-1 footprint.
- `AX_PeriodCycleBasis` is inherited from the `jacobian-challenge` dependency (a
  symplectic cycle basis for hyperelliptic curves); the trusted base spans that
  repository too.

## What to poke at — walk the difficult-points register

The kernel guarantees the *derivations*, not the *statements*. The specific places
where an error can still hide are catalogued, with how each is addressed and which
review caught it, in **[`DIFFICULT_POINTS.md`](DIFFICULT_POINTS.md)** — start your
skeptical pass there rather than rediscovering them. The recurring classes:

1. **Analytic structure** — a pointwise `∃` licenses no holomorphic choice;
   boundary limits must be supplied in the right filter; branch/domain conventions.
2. **Lean conventions** — junk values (`x/0 = 0`, `Nat` subtraction) making
   assertions implicit; vacuously satisfiable or unsatisfiable-as-stated predicates.
3. **Topology** — existence of a cover/group without the *labels* downstream
   theorems consume; uninterpreted placeholder predicates; a bespoke axiom that
   restates the theorem.
4. **The dictionary** (`Dictionary.lean`, §4.1 of the paper) — a wrong physics↔math
   identification poisons everything while every proof stays valid.

A cautionary datum recorded in the register: the C-route axiom signatures passed
62/62 numeric checks and were still NO-GO under adversarial review — three
statement-level gaps invisible to sampling. A review is not complete without a
**derivability walk-through**: for each target theorem, trace which clause of which
hypothesis or axiom supplies each step.

Findings of any of these kinds are exactly what this discipline is designed to make
visible; they would be corrections to named lines, not to a diffuse argument.
