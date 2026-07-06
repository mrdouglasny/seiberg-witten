# Difficult points — where this formalization can actually go wrong

*The register a human reviewer should walk. Each entry: the difficulty, where it
bites, how it is addressed (or that it is open), and which review caught it. This
file exists because generic review ("read the hypotheses, check the axioms") missed
concrete subtleties that targeted adversarial review later found (the C-route
review, 2026-07-04, is the case study — three blocking gaps in signatures that had
already passed 62/62 numeric checks). Review effort should start from this list,
not rediscover it. Companion to [`REVIEWER.md`](REVIEWER.md) and
[`FAITHFULNESS.md`](FAITHFULNESS.md); status `resolved` / `planned` / `open`.*

## A. Analytic-structure traps (the hardest class)

**A1. A pointwise `∃` carries no analytic structure.** An axiom asserting
"for every `m` there exists `τ` with …" licenses no *holomorphic choice* `m ↦ τ(m)`
— and rigidity/developing-map arguments need the function, not the fibers.
*Bit us in:* C-route C1 v1 (rigidity was unprovable from it). *Caught by:* GR
adversarial review 2026-07-04 (`C_ROUTE_REVIEW_PROMPT.md` Q8 (archived in local `history/audit/`)) — after 62/62 numeric
passes; numerics cannot see quantifier structure. *Addressed:* the holomorphy lemma
target C1h (`GENUS1_PERIODS_PLAN.md` v2, archived in local `history/audit/`); **status: planned**. *Standing check:*
every existence-form axiom (`AX_elliptic_inversion`, `periodRigidityAxiom.realize`,
`AX_thrice_punctured_uniformization`) — does any consumer need continuity/holomorphy
of a selection? If yes, where does it come from?

**A2. Limits at excluded boundary points.** Statements on an open domain (the cut
plane, `V ⊆ U`) say nothing at the boundary points where the physics happens (the
monopole/dyon points ARE the excluded singularities). H2 needs behavior *at* `Δ`,
so every cusp-limit fact must be supplied explicitly, in the right filter
(`𝓝[domain] 0`, not `𝓝 0`). *Bit us in:* C3 v1 had the `K` limit but not the `E`
limits, making H2's `a_D → 0` underivable. *Caught by:* GR review (Q9).
*Addressed:* C3 v2; **status: planned**. *Standing check:* for each boundary
statement (H2's `PeriodVanishesAt`, the cusp limits), is the filter the within-domain
one, and are *all* the functions entering `a, a_D` covered?

**A3. Branch and domain conventions.** Principal `cpow`/`log`, cut placement, and
convergence domains are silent in prose and fatal in formal statements. *Bit us
in:* `AX_jacobi_quartic` was stated on all of `ℂ`, relating junk values off `ℍ`
(caught writing `FAITHFULNESS.md`; restricted 2026-07-04, commit `193f0ca`); the
numerical oracle itself first had a branch bug (θ₂ via a principal fractional power
— caught because the transformation laws failed numerically; `FIDELITY_REVIEW.md`).
*Addressed:* ℍ-restriction; `EllipticParamDomain` cut plane with `m ↔ 1−m`
symmetry; oracle samples in all four quadrants; **status: resolved for current
statements; standing check for every new one.**

**A4. Global facts from local proofs.** Local (disk-of-convergence) identities do
not globalize for free — but on a simply connected domain the identity theorem
does it, and the repo has the tool (`holo_eqOn_of_germ`, proved, standard-3; the
cut plane is star-shaped about `m = ½`). *Bit us in:* review Q14 flagged the
G-route's globalization as "exceedingly difficult"; the disposition is that it is
existing machinery here. **Status: resolved (as method); each use still a proof.**

## B. Type-system and Lean-convention traps

**B1. Junk values make assertions implicit.** `x/0 = 0`, junk `cpow` off-domain,
`Nat` subtraction truncation. An axiom can *silently assert* a nonvanishing (C1's
`τ = i·K′/K ∈ ℍ` forces `K ≠ 0` only via a contradiction argument) — technically
sound, terrible for use and for review legibility. *Caught by:* GR review (Q2).
*Addressed:* explicit `K ≠ 0` clause in C1 v2; guards `2 ≤ N`, `N_f ≤ 3`, `Λ ≠ 0`
throughout (see `FAITHFULNESS.md` "deliberate design choices"). **Status:
resolved; standing check:** does any statement rely on a junk-value convention to
be true, or to be usable?

**B2. Vacuously satisfiable hypotheses.** The kernel accepts an assumption that
says nothing; the headline then asserts less. *Bit us in:* H3 v1
(`∃ g, g = transvection n` — true by fiat), H2 without `n ≠ 0`, H5's trivial
witnesses. *Caught by:* external review + the discipline of asking "could this be
satisfied trivially?" (paper §4.4). *Addressed:* hardened predicates (actual deck
transformation; nonzero charge; nontrivial `ℂ`-linear `ω ≠ id`); non-vacuity
witnesses proved where possible (`hasFiniteOrderAutomorphism_of_neg_invariant`).
**Status: resolved for H0–H6; standing check for every new predicate.**

**B3. Unsatisfiable-as-stated physics.** The dual failure to B2: a faithful-looking
predicate false in the intended model. *Bit us in:* H5 "order exactly 2N" —
unsatisfiable on the SU(2) *moduli* (the `ℤ_{4N}` on fields acts through `ℤ_{2N}`
on `φ` and a smaller quotient on Casimirs). *Caught by:* trying to verify the
predicate. *Addressed:* "order dividing 2N" + proved witness; `AXIOM_AUDIT.md`
(resolved 2026-06-30). **Status: resolved.**

**B4. Substituting a definition for an opaque relation changes an axiom's strength.**
An axiom `A (h : R x) : C x` with `R` uninterpreted is as strong as the *intended* `R`;
define `R` weaker than intended and `A` silently strengthens — possibly to falsity. *Bit
us in:* the `SameSWMonodromy` demotion (2026-07-04), twice in one afternoon: (i) the bare
pointwise relation admits **choice-built discontinuous lifts** (toggle the proved
`τ ↦ τ+2` on an arbitrary set; inhabit via C1's `∃τ` + choice) — refuting the
lift-uniqueness axiom; (ii) after adding analyticity, **junk-value inhabitants** remained
(off `ℍ` the θ-series are junk and `λ ≡ 0`, so at `Λ = 0` lower-half-plane analytic maps
satisfy the developing equation vacuously) — refuting it again; (iii) the germ point
`u₀` was unconstrained, so `D = ∅` (hypothesis trivially true) or `D = {u₀}` (pointwise
data cannot pin a germ) refuted it a third time — fixed by `IsOpen D` + `u₀ ∈ D`.
*Caught by:* self-review
while preparing the external review prompt (the derivability walk-through applied to the
axiom's *falsifiers*, not just its consumers). *Addressed:* `IsSWDevelopingMap` bundles
holomorphy + ℍ-valuedness + the developing equation; `SameSWMonodromy` demands it of both
maps. **Status: resolved; standing check:** after every demotion or
definition-substitution, re-ask "what inhabits the hypothesis *now*?" — junk-value and
choice-built inhabitants included.

**B5. An unused axiom argument means structure was abstracted away — usually from the
conclusion.** `AX_developing_map_rigidity` took `U : ThricePuncturedUniformization` but
never used it, and correspondingly its conclusion `∃ m : ℂ → ℂ` had forgotten the `Γ(2)`
deck structure the covering was supposed to supply — true but too weak to mean "unique up
to duality". *Caught by:* external review round 2 (GR, 2026-07-04) — "the unused `U` is
the smoking gun". *Addressed:* conclusion strengthened to `∃ γ ∈ Gamma2` acting by
`moebiusOn`, with the proved bridge `analyticOnNhd_moebius_comp`. **Status: resolved;
standing check:** an axiom parameter unused in the proposition body is a lint-level red
flag — ask what the conclusion should be saying about it. *Companion lesson:* the same
review's other finding (C4 "mathematically false") was **wrong** and was rejected with a
derivation + a discriminating numeric test — dispositions need proofs in both directions;
external review verdicts are inputs, not rulings.

## C. Topological/geometric traps

**C1. Existence of a structure does not label it.** The covering axiom gives a
`Γ(2)` cover; it does not say *which* parabolic generator sits at which cusp — and
H3's explicit `M_±` (monopole vs dyon monodromy) need exactly the labels. An
abstract-nonsense axiom can be true and useless. *Caught by:* GR review (Q10).
*Addressed:* the C4 cusp-labeling axiom in log-remainder form, numerically verified
both ways (`T²` jump `+2` at `m = 0`; `ST²S⁻¹` at `m = 1`); **status: planned.**
*Standing check:* whenever an axiom supplies a group/cover/torsor, ask what
*labeling* downstream theorems consume.

**C2. Uninterpreted placeholders.** `SameSWMonodromy` (a `Prop` with no
definition) and `localMonodromy` (a function with no definition) are honest
interfaces for pending layers — but theorems quantifying over them are rigidity
*relative to an opaque relation*, and a reviewer must not read more into them.
*Caught by:* writing the faithfulness digest (Part II labels them). *Addressed:*
labeled; `SameSWMonodromy` **demoted to a definition (2026-07-04)** via the pinned
`DevelopsSWCrossRatio` (review Q11: pinning to the geometry beats the symmetric
relation) — `sw_su2_unique`'s kernel footprint now carries no physics axiom.
`localMonodromy` remains the labeled placeholder. **Status: demotion done;
localMonodromy open.**

**C3. A bespoke axiom can restate the theorem.** `periodRigidityAxiom`'s fields
essentially *are* E5/E6 — the headline is a thin corollary, and the machine-checked
content is the *separation*, not the mathematics. *Caught by:* writing
`FAITHFULNESS.md` B.1 side-by-side (and pressed by the author). *Addressed:* stated
plainly in the digest and `REVIEWER.md`; the C-route replaces it at rank 1 with
classical axioms that do not resemble the headline. **Status: disclosed; fix
planned.**

## D. Dictionary/identification traps

**D1. Physics names must denote, not suggest.** Every physics term is an `abbrev`
of a math object (`Dictionary.lean`); the identification of moduli with curve-family
coefficients is itself part of the claim, fixed only up to scheme redefinitions
(paper §3). *Standing check:* review the dictionary once — a wrong identification
poisons everything downstream while every proof stays valid.

**D2. Naming drift across artifacts.** Plan/audit documents written before a
renaming silently contradict the code (`swPeriodLayer`, `IsMatterPeriodLayer`,
"order 2N" glosses). *Caught by:* reviewer-guide construction, 2026-07-04.
*Addressed:* un-staling passes; the quote-checker (`check_faithfulness.py`) pins
digest↔code; **status: resolved; recurring risk** — prose↔prose drift has no
checker.

### D3 — an existential axiom that never named its subject (found by discharging it)

**Where.** `periodRatio_logDeriv_asymptotic` (BetaFunction.lean), input to E10.

**The point.** The docstring said "the curve's period ratio has a logarithmic
singularity"; the formal statement said only `∃ F : ℂ → ℂ, Differentiable ℂ F ∧
s·F′(s) → (4−Nf)/(2πi)` — no clause connects `F` to any period integral. The gap
went unnoticed while it was an *axiom*; it surfaced the moment the discharge loop
asked what a *proof* would require, and the answer was: any entire function with the
right tail (witness: the `Ein` primitive `∫₀¹(1−e^{−tz})/t dt`). Discharging it was
therefore both a trusted-base reduction and a fidelity **finding**: E10's formal
content is weaker than its physics gloss, and was so from the start — the axiom
asserted no more. Remedy queued: the faithful version for the actual ratio
`i·K(1−m)/K(m)` at the curve's modulus (R4), now within reach of the proved
Legendre/cusp layer.

**Class.** Statement-level under-specification — the dual of "a bespoke axiom
restates the theorem": an axiom that states *less* than its name. Detection
heuristic: for every axiom, ask "what object does the conclusion pin down, and is
it the object the docstring talks about?" — an `∃` with no defining clause is the
red flag.

### B6 — a coefficient that could absorb anything (H6's vacuity, author-caught)

**Where.** `Instantonic` (Hypotheses.lean), the sharp form of H6.

**The point.** The original statement — remainder `= ∑ c_{k+1}(a)·Λ^{2N(k+1)}` with
holomorphic coefficients, at fixed `Λ` — was vacuous: `c₁(a) :=
(F(a) − F_cl(a) − F₁(Λ,a))/Λ^{2N}` fits *any* differentiable `F`. The docstring even
asserted the opposite ("holomorphy of the coefficients keeps this from being
vacuous"). The intended physics — the instanton coefficients do not depend on
`Λ` — is a statement about the `Λ`-*family*, invisible at a single `Λ` unless
re-expressed. The fix: the family's scale covariance (`a ↦ ta, Λ ↦ tΛ, F ↦ t²F`)
converts `Λ`-independence into the **weighted homogeneity**
`c_k(t·a) = t^{2−2Nk}·c_k(a)` — a fixed-`Λ` clause that only remainders with the
discrete homogeneous decomposition satisfy (an `a³` deviation at `N=2` fits no `k`).

**Class.** B4's sibling: a hypothesis vacuously satisfiable not through junk values
but through an **unconstrained existential parameter** — the freedom the words
implicitly deny ("the coefficients", suggesting canonical objects) but the formula
grants. Detection heuristic: for every `∃` inside a hypothesis, ask what stops the
witness from being reverse-engineered from the thing being constrained.

### B7 — a hyperbolic matrix in a parabolic slot (oracle gap, self-caught)

The first version of the λ-frame dyon monodromy (`CuspData.lean`, step A of the
cusp-data campaign) was `[[-1,2],[2,-5]]` — trace `−6`, **hyperbolic**. The oracle
checked determinant, mod-2 reduction, the factorization `M_mono·M_dyon = M_∞`, and
numerical λ-invariance — and a hyperbolic Γ(2) element passes ALL of those. But a
monodromy around a point where a single BPS state goes massless must be **parabolic**
(conjugate to `Tᵏ`, |trace| = 2); the slip came from choosing the wrong sign of the
monopole representative (`ST⁻²S⁻¹` instead of `ST²S⁻¹`) and defining the dyon by the
factorization. Caught while designing the endgame (the dyon's fixed point came out
real-hyperbolic instead of the cusp `1`). Fix: `swMMono = [[1,0],[-2,1]]`,
`swMDyon = [[-1,2],[-2,3]]` (both trace 2, fixing cusps 0 and 1), plus Lean
parabolicity lemmas (`swM*_trace`) and oracle checks §A4–A6 (trace and fixed cusps).

**Lesson:** an oracle that only checks the properties the *proofs consume* (here:
group membership and invariance) can silently accept an object that is unfaithful to
the physics gloss. Every transcription of a physical object should also pin the
invariants that CLASSIFY it (here: the conjugacy class — trace), not just the ones
downstream lemmas use.

## E. Meta-lessons about the review process itself

- **Numerics pass ≠ statement usable.** The C-route v1 signatures passed 62/62 at
  40 digits and were still NO-GO: quantifier structure, missing limits, and missing
  labels are invisible to sampling. Numeric vetting bounds *falsity*, not
  *fitness for purpose*.
- **Fitness-for-purpose review is a distinct axis.** The blocking questions were of
  the form "can the intended theorem actually be proved from this statement?" —
  neither faithfulness (is it the classical fact?) nor soundness (is it true?).
  Reviews should always include a *derivability walk-through*: take each target
  theorem and trace which clause of which axiom supplies each step.
- **The verifier needs verifying.** The oracle's own branch bug was caught only
  because the λ transformation laws failed numerically. Independent implementations
  earn their keep both ways.
- **Adversarial framing works.** The productive review prompt named the blind spots
  of the evidence already in hand and demanded corrected statements, not verdicts
  alone (`C_ROUTE_REVIEW_PROMPT.md`, archived in local `history/audit/`, is the template).
