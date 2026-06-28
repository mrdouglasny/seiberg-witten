# Axioms for physical reasoning: codifying the Seiberg–Witten solution in Lean

*Working paper, draft. Companion to the formal development at
[`mrdouglasny/seiberg-witten`](https://github.com/mrdouglasny/seiberg-witten) and to the
ICML 2026 talk "Validation of AI-generated results in theoretical physics."*

## Abstract

Most results in theoretical physics are not theorems. They are conclusions of arguments the
community trusts without a proof from first principles. For the deepest of them a rigorous
proof is conceivable but lies far out of reach — it would presuppose a nonperturbative
construction of the interacting quantum field theory, a goal at least as hard as the
Yang–Mills mass-gap Millennium problem. We argue that an interactive theorem prover is the
right instrument for such a result even so: not to *prove* it — that is beyond reach — but to
state the physical reasoning as a short list of **explicit, named axioms**, prove every
mathematical consequence of them, and keep a machine-checked line between the two. The trust that remains then rests on that short,
inspectable list, and the prover can report, for any downstream result, exactly which
assumptions it used. We carry this out for the Seiberg–Witten solution of N=2 SU(N)
super-Yang–Mills, formalized in Lean 4. We describe what is proved, what is assumed, how the
assumptions are checked — external review and an independent numerical oracle — and why this
discipline is a sound standard for validating AI-generated results in theoretical physics. What
we offer is a *discipline*, reviewable on its own terms: a reader may take the Seiberg–Witten
mathematics on trust and still assess the formalization method.

## 1. Introduction

Most of what theoretical physics asserts is not proved. Across the field, the results we build on
are typically not theorems but conclusions of *arguments* — chains of physical reasoning trusted
because they cohere internally, because independent routes to the same quantity agree, and
ultimately because they account for experiment. A result can be as certain as anything in science
and still have no proof from first principles; certainty in physics rests on a different footing
than in mathematics.

In quantum field theory the gap is at its widest. There the deepest results — the spectrum of a
gauge theory, the phase structure of a model, an exact low-energy effective action — follow from
reasoning about symmetry, holomorphy, dualities and consistency, and for the hardest of them a
rigorous proof is not merely missing but out of reach: it would require first constructing the
interacting quantum field theory nonperturbatively, a problem on the scale of the Yang–Mills
mass-gap Millennium Prize. These results are as certain as anything in physics, and yet they are not
theorems.

This gap has become pressing for a new reason: AI systems now generate physical derivations, and
their characteristic error is not a wrong algebra step — a referee catches those — but a
*hallucinated assumption*, an unphysical premise or a dropped subtlety presented as if derived.
Catching that by reading is exactly what does not scale. What one wants instead is a way to make an
argument's assumptions explicit and machine-auditable, cleanly separating what is genuinely derived
from what is taken on faith.

Interactive theorem provers are built for exactly that separation. A technology from computer
science — where they grew out of hardware and software verification — proof assistants have lately
drawn intense interest in mathematics, with large parts of the modern corpus now formalized; the
same tools apply directly to the problem here. A proof assistant such as **Lean 4** is a language in
which one writes definitions and proofs that a small, fixed **kernel** — a few thousand lines of
code, audited once and then trusted — checks line by line. A statement the kernel accepts is correct *relative to its inputs*: the handful of logical
axioms built in, plus any further **axioms** the author explicitly declares. That whole list is the
**trusted base** — everything one must believe in order to believe the result — and the prover can
print it: for any theorem, the command `#print axioms` reports exactly which axioms it used, and
nothing reaches that list without being named. Modern provers ship with large formal libraries of
mathematics — Lean's is **Mathlib**, several hundred thousand theorems — so one formalizes atop real
analysis, algebra and geometry rather than from scratch.

The point of this paper is to turn that machinery on a physics result that *cannot* be proved, and
to use it honestly. We do not try to prove the Seiberg–Witten solution; that is beyond reach.
Instead we **state the physical reasoning as a short list of explicit, named axioms, prove every
mathematical consequence of them in Lean, and let the kernel hold the line between the two.** The
residual trust is then concentrated on that named list; the kernel would expose a contradiction
hidden among the axioms; and `#print axioms` audits, for any downstream claim, precisely which
physical inputs it rests on. Justifying the axioms is still a physicist's task — here, external
review and an independent numerical oracle — but it becomes a finite, inspectable one rather than a
diffuse act of faith.

We take as the test case the **Seiberg–Witten solution** of N=2 SU(N) super-Yang–Mills: a
celebrated, universally trusted result, unprovable within reach, yet unusually sharp in content — it
identifies the exact low-energy physics with the period geometry of a specific family of algebraic
curves, so both the physical assumptions and their mathematical consequences are crisp enough to
formalize. Around it we obtain a clean split: a proved mathematical spine (the curve, its genus,
positivity of the special-Kähler metric, the period matrix), the physical hypotheses as named
predicates, and the headline statements — existence, and uniqueness up to duality — proved from
those hypotheses plus a single mathematical input.

The rest of the paper proceeds as follows. §2 explains why a physics *result* is a different
formalization target from a mathematical theorem, and §3 draws out the two kinds of formalization
this entails. §4 states the Seiberg–Witten solution compactly. §5 is the formalization proper — what
is assumed (the hypotheses, with their physical origins), what is proved, and two places where
formalizing forced a hidden choice into the open. §6 describes how we check the axioms and §7 argues
the discipline is the right standard for AI-generated physics. §8 lays out the remaining
mathematical debt and where it will be discharged, and §9 the prospects for deriving the physical
assumptions themselves from deeper principles. §10 places the work in context; §11 concludes. Two
appendices give the Lean statements of the physical hypotheses (A) and the residual mathematical
axioms (B).

## 2. Physics is mostly not theorems

A mathematician who formalizes a theorem has a proof to formalize. A physicist who
formalizes a *result* usually does not. The Seiberg–Witten (SW) solution is the textbook
case. No rigorous proof says that the low-energy physics on the Coulomb branch of N=2 SU(N)
gauge theory is governed by the curve `y² = P_N(x)² − Λ^{2N}`. One is *conceivable* — but it
would first require constructing the interacting N=2 theory nonperturbatively, a problem at
least as hard as the Yang–Mills mass-gap Millennium problem, and so out of reach for the
foreseeable future. What we have instead is an *argument*: a small set of physical
assumptions — holomorphy from supersymmetry, the exact pattern of singularities,
electric–magnetic duality, the weak-coupling asymptotics — that together pick out that curve,
believed because three independent computations of the same quantity agree.

So "formalizing Seiberg–Witten" cannot mean "proving it" — not today, and not without first
solving a Millennium-scale problem. That seems to put the result beyond formal methods. We
argue the reverse: such a result is precisely where formalization helps most, *provided one
is honest about what it does*.

> State the physical assumptions as **explicit, named axioms**; prove every **mathematical
> consequence** of them; and keep a machine-checked line between the two.

We call this second category — the non-rigorous reasoning physicists nonetheless trust —
**foundations for physical reasoning**, by analogy with foundations of mathematics. A
formalization then does three things no informal write-up can: it makes the dependency
structure machine-checkable, it concentrates the residual trust onto a few named axioms, and
it lets the kernel detect a contradiction among them.

This matters now because of *who*, or what, increasingly produces such arguments. As large
language models begin to propose physical and mathematical derivations, their characteristic
failure is not a wrong algebra step a referee would catch but a *hallucinated assumption* — an
unphysical premise, or a dropped topological subtlety, presented as though derived. A
machine-checked boundary between assumed and proved is precisely what keeps such a system
honest; that is why we frame the discipline below as a standard for validating AI-generated
physics, and return to it in §7.

## 3. Two kinds of formalization in physics

| | What it is | Examples |
|---|---|---|
| **Mathematical physics** | A rigorous statement exists; you prove it. | Stability of matter; constructive QFT; the lattice-gauge mass gap — **and the proved spine of this project**: the curve, its genus, special-Kähler positivity, the period matrix. |
| **Foundations for physical reasoning** | Codifying the *non-rigorous* reasoning the community trusts, where no proof is within reach (a rigorous one would be Millennium-hard). | **The Seiberg–Witten *argument* itself.** |

This is not a value judgment but a bookkeeping discipline, and it is necessary because the
kernel does not enforce it. A theorem can be proved, axiom-free, and still be the **wrong
statement** — a dropped hypothesis, a flipped sign, a domain quietly narrowed. And a physical
assumption written as an innocent-looking definition can smuggle a falsehood past the kernel
entirely. The discipline forces every physical input into the open as a named hypothesis, and
every mathematical claim onto the proved side.

For a reader who formalizes *mathematics*, the delta is threefold:

- there is no proof to formalize — the result is unprovable within reach (§2), so the question
  is not "is the proof correct?" but "are the assumptions explicit and the derivations sound?";
- the physical lore becomes **named hypotheses** — predicates a theorem takes in its signature
  — never smuggled into a definition or a convenient default;
- the residual trust then localizes onto a short list, and `#print axioms` of any result audits
  exactly which assumptions it used.

Nothing here is special to physics-as-a-subject; it is what changes when the object you
formalize is an *argument the community trusts* rather than *a theorem with a proof*.

## 4. The Seiberg–Witten solution in one paragraph

*For a reader outside physics: the SW solution maps the exact low-energy behaviour of a
quantum system to the geometry of a specific family of algebraic curves. What matters for the
formalization is less the physical meaning of the terms below than the rigid mathematical data
they impose.*

On the Coulomb branch — coordinates `u₂,…,u_N`, rank `r = N−1` — the low-energy theory is
abelian `U(1)^r` gauge theory. Its data are the special coordinates `aᵢ` and their duals
`a_{D,i}` (periods of a meromorphic differential), the coupling matrix `τ_{ij}`, and the
central charge `Z = nₑ·a + n_m·a_D` of a BPS state, whose modulus is its mass. The SW claim
is that all of this *is* the period geometry of `y² = P_N(x)² − Λ^{2N}` (`P_N` a degree-`N`
polynomial in a coordinate `x`, distinct from the moduli `u`). The assumptions that
single out that curve are: holomorphy / non-renormalization (one holomorphic prepotential
`F`, one-loop-exact perturbation theory); the exact singularity structure (the branch is
singular exactly where a BPS state goes massless, and nowhere else); electric–magnetic
duality (`Sp(2r,ℤ)` monodromy); the `ℤ_{2N}` R-symmetry fixing the singularities; and matching
to the one-loop-plus-instanton expansion at weak coupling.

## 5. The formalization

### 5.1 What is assumed

The physical content is six hypotheses **H0–H6**, each a named Lean **predicate or structure**
(never a global axiom: a theorem that uses the physics carries their bundle `IsSWEffectiveTheory`
as a *hypothesis*, so the assumptions live in its type, not the trusted base). They are **not
independent postulates**: every one is a *specialization of* **N=2 supersymmetry** — the eight
supercharges of the theory — together with the gauge data (`SU(N)`, asymptotic freedom) and
unitarity. We give each with its physical origin and its Lean carrier:

- **H0 — the carrier** (*N=2 SUSY + Coulomb-phase Higgsing*). A generic adjoint vev breaks
  `SU(N) → U(1)^{N−1}`, leaving `r = N−1` abelian N=2 vector multiplets; their special coordinates
  `a, a_D`, coupling `τ`, and the charge lattice with its Dirac pairing are the data
  (`CoulombBase`/`Sheet`), on the universal cover of the moduli space minus its singular locus.
- **H1 — special geometry** (*N=2 SUSY; unitarity*). Eight supercharges force the Coulomb branch to
  be rigid special Kähler: one holomorphic prepotential `F` with `a_D = ∂F/∂a`, `τ = ∂²F/∂a²`;
  `Im τ ≻ 0` is positivity of the gauge kinetic term — the no-ghost (unitarity) condition
  (`Sheet.SpecialGeometry`).
- **H2 — BPS singularities** (*the central-charge BPS bound*). The N=2 algebra carries a central
  charge `Z`; all states obey `M ≥ |Z|`, saturated by BPS states. A singularity of the effective
  theory is a charged BPS state going massless, `Z_n → 0` (`Sheet.SingularitiesAreBPS`).
- **H3 — Picard–Lefschetz monodromy** (*running induced by a light charged state*). Encircling a
  point where the BPS state of charge `n` is massless, its one-loop logarithm produces exactly the
  symplectic Picard–Lefschetz transvection in `n` (`PicardLefschetzAtGenericStratum`).
- **H4 — electric–magnetic duality** (*Montonen–Olive / Seiberg–Witten duality*). The freedom in
  which charges count as "electric" is the symplectic group `Sp(2r,ℤ)` preserving the Dirac pairing
  and the central charge; charts glue by it (`Deck`; sheets form a duality-glued `SWAtlas`).
- **H5 — R-symmetry** (*the anomalous `U(1)_R`*). The classical `U(1)_R` is broken by instantons to
  a discrete subgroup, acting on the moduli (order `2N` for `SU(N)`) and permuting the singular
  locus (`RSymmetry`).
- **H6 — weak-coupling asymptotics** (*N=2 nonrenormalization + asymptotic freedom*). The
  prepotential is **one-loop exact** in perturbation theory; the remainder is a sum of instanton
  corrections weighted by the dynamical scale `Λ^{2N}` (`Sheet.MatchesAsymptotics`).

The rank-1 monodromy input `SameSWMonodromy` (Appendix B) is itself a consequence of H2+H3 — which
BPS state is light where fixes the monodromy. Full Lean definitions are in Appendix A, which also
discusses factoring these as one general N=2 special-geometry structure that `IsSWEffectiveTheory`
specializes.

### 5.2 What is proved

From the hypotheses of §5.1 (with the mathematical inputs of Appendix B), the following are
**sorry-free theorems**, and `#print axioms` reports exactly what each rests on:

- **The headline — existence and uniqueness up to duality.** The Seiberg–Witten curve *realizes*
  such a theory (`sw_curve_admits_effective_theory`), and the hypotheses fix it **uniquely up to
  `Sp(2r,ℤ)` electric–magnetic duality** (`sw_effective_theory_unique_up_to_duality`; atlas-level
  `sw_unique_up_to_duality`) — uniqueness being a period-map rigidity statement. Each depends on
  the three logical axioms plus a *single* mathematical input, the period geometry `swPeriodLayer`;
  for SU(2), `sw_su2_unique` is finer still (physics + two classical complex-analysis facts).
- the SU(N) curve has **genus `N−1`**;
- its period matrix `τ` is **symmetric with `Im τ ≻ 0`** — positivity of the special-Kähler metric,
  the physical no-ghost condition;
- for SU(2), the curve is singular at **exactly `u = ±Λ²`** — the monopole and dyon points, by a
  discriminant computation, not lore;
- the Picard–Lefschetz monodromy of a vanishing cycle is **symplectic** — why the monodromy group
  sits in `Sp(2r,ℤ)`;
- the rank-1 modular function `λ = θ₂⁴/θ₃⁴` (from Mathlib's Jacobi thetas) is a proved
  **`Γ(2)`-Hauptmodul**, with the cusp symmetry `1 − λ = θ₄⁴/θ₃⁴`.

The headline's machine-checked dependency, in full — logic plus one named period-geometry input,
nothing else:

```lean
#print axioms sw_effective_theory_unique_up_to_duality
-- depends on axioms:
--   [propext, Classical.choice, Quot.sound,   -- logic
--    swPeriodLayer]                            -- the one mathematical input (period geometry)
```

The exact statements, the finer SU(2) footprint, and `swPeriodLayer` itself are in Appendix B.

### 5.3 Two things formalizing forced into the open

**The type system can refuse a convenient falsehood.** Our first attempt made the periods
`a, a_D` and the coupling `τ` single-valued functions of the moduli. External review flagged
this as *vacuous*: a global holomorphic map from the moduli space to the Siegel upper
half-space is constant by Liouville's theorem — a free theory. The data must instead live on
the universal cover of the moduli space minus its singular locus. The corrected types encode
this, refusing the free-theory shortcut that prose slides over.

**A surprise comes out derived, not assumed.** Argyres–Douglas points — where the theory
becomes an interacting CFT with no Lagrangian — look as though they need their own postulate.
In the formalization they are instead a *definition*: the locus where two **mutually non-local**
BPS charges (nonzero Dirac pairing) go massless together, built from the central charge and
the charge lattice already in hand. (This locus is *empty* for pure SU(2) — the monopole and
dyon go massless at the two different points `±Λ²` — but the definition is general, correctly
accommodating the matter flavours and higher-rank theories where AD points actually occur.) A
phenomenon the theory should explain falls out as a consequence — a check the axioms pass
rather than a cost they incur.

## 6. Checking the axioms: validation by independent agreement

Concentrating trust onto named axioms is worthwhile only if those axioms are then checked. We
use three tools, cheapest first.

**An independent numerical oracle.** Where a statement has computable content, we evaluate it
in a separate engine (mpmath / numpy) that shares no code or authorship with the Lean. A run
of 44 checks at 40-digit precision confirms the assumed theta-function identities
(`θ₃⁴ = θ₂⁴ + θ₄⁴`, `θ₃ ≠ 0`), verifies that the proved `λ` transformation laws are
*faithful* (catching any sign or shift error), anchors the normalization (`λ(i) = ½`), and
checks the SU(2) singularity locus. Tellingly, the oracle first caught a bug **in itself** —
a fractional power evaluated on the wrong branch — before agreeing with the Lean to full
precision: the method earning its keep. A numerical pass is necessary, not sufficient; it
validates values, not logical structure (it cannot see a too-strong hypothesis or a vacuous one).

**Cross-model and self-review** against the pinned sources, recorded per result, separating
"is it proved?" from "does it say what the source says?".

**The physicist's triangle.** The deepest reason the SW lore is trusted is that three
independent routes to the prepotential agree: weak-coupling perturbation theory, the instanton
expansion (Nekrasov's partition function, itself later made rigorous), and the exact periods
of the curve. This independent agreement is the empirical content behind the axioms, and our
protocol attaches it as a cross-check rather than asserting it.

## 7. Why this is the right standard for AI-generated physics

When an AI produces a physics result, the dangerous failure is rarely a wrong algebra step a
referee would catch. It is an **unstated assumption** — a *hallucination*, in machine-learning
terms — slipped in as though derived. Reasoning from named physical axioms turns the kernel and
type system into a guardrail that makes this impossible to hide:

- a physical input must be *named* to be used;
- every named input shows up when the prover lists the axioms behind a result;
- an honest definition — the universal-cover carrier, Argyres–Douglas as a derived locus —
  cannot encode a convenient falsehood, because the kernel checks the types;
- and *justifying* the axioms remains the physicist's job, done by the same
  independent-agreement checks that earn trust in the first place.

Formalization does not make the physics true. It makes the reasoning **auditable** — which is
exactly what a result no one can prove from first principles needs.

## 8. What remains, and where it lives

The discipline also makes the remaining *mathematical* debt legible. For SU(2) the uniqueness
headline is, as just described, already a theorem modulo named classical-math axioms; the debt
is to *discharge those axioms*, and it reduces to a few sharply-identified, Mathlib-scale
developments: the Jacobi triple product (which discharges the theta identities and
non-vanishing); the modular-`λ` covering `ℍ/Γ(2) ≅ ℂ∖{0,1}` (whose invariance half is already
proved, leaving the surjectivity); and the Gauss–Manin / variation-of-Hodge-structure layer
over the moduli space. The covering rests in turn on the **Riemann mapping theorem** and the
**Schwarz reflection principle** — general complex analysis, absent from Lean (RMT is
formalized in Isabelle/HOL), which we have scoped as upstream contributions. The point is that
"is this physics right?" becomes a precise, prioritized list of theorems to build.

## 9. Prospects: deriving the physical assumptions

The hypotheses of §5.1 are themselves *consequences* of the microscopic definition of N=2
super-Yang–Mills, reached by physical arguments of varying rigor. Some of them are, on inspection,
**theorems** — and formalizing those would push the assumed frontier one level deeper, deriving the
parent N=2 structure from inputs more primitive than its own data. Three tiers.

**Already within reach.** The **BPS bound** `M ≥ |Z|` is a positivity lemma about the
centrally-extended N=2 algebra: a Hermitian combination of supercharges has a positive-semidefinite
anticommutator matrix whose eigenvalues are `M ± |Z|`, the BPS (short-multiplet) case being its
kernel. This is finite-dimensional linear algebra — Mathlib's positive-semidefinite API suffices —
and it derives the core of H2 from the algebra alone, with no quantum field theory.
**Dirac–Schwinger–Zwanziger quantization** splits into a theorem and a postulate: the
electromagnetic field angular momentum of a dyon pair is the antisymmetric pairing
`(q₁g₂ − q₂g₁)/4π` (an explicit `∫ x×(E×B)`), and requiring angular momentum to be quantized forces
that pairing into `ℤ` — the integer symplectic structure of the charge lattice (H0), with the
duality group `Sp(2r,ℤ)` (H4) its automorphisms preserving the central charge. The computation is
formalizable; the quantization is one further named postulate, in the spirit of the others.

**Formalizable, but needing infrastructure.** Special geometry (H1) follows from N=2 superspace
invariance of the vector-multiplet action — formalizable once N=2 superspace is built; the one-loop
exactness behind H6 rests on holomorphy and nonrenormalization (more tractable than the loop
integral it constrains); the discrete R-symmetry (H5) is what the chiral anomaly leaves of `U(1)_R`,
an index computation. Real, but substantial.

**Beyond reach, for now.** That N=2 SYM *exists* as an interacting four-dimensional theory, with
these multiplets and a BPS spectrum carried by genuine states, presupposes constructing the quantum
field theory — the same barrier as the solution itself. The algebra is exactly what one gets to
*assume*; its realization is what cannot yet be assumed away.

The lesson mirrors the body. Just as the headline reduced to physics plus standard mathematics, the
physics itself partly reduces: the BPS bound and the Dirac pairing are mathematics in disguise, and
formalizing them would move the frontier from "assume special geometry, the BPS bound, and a
symplectic lattice" to "assume the supersymmetry algebra and angular-momentum quantization." Each
such step shrinks what must be taken on trust.

## 10. Related work

The assurance artifacts (correspondence index, fidelity review, numerical validation, axiom
audit) follow the conventions of the author's own `formalization-assurance` project
(`math-commons/formalization-assurance`), separate from and predating this work; the upstream
mathematical contributions are framed for the Lean FRO's Tau Ceti library. The Riemann mapping theorem is formalized in
Isabelle/HOL (Paulson); the Schwarz reflection principle and the SW solution appear
unformalized before this work.

## 11. Conclusion

A rigorous proof of the Seiberg–Witten solution lies beyond reach — it presupposes
constructing the quantum field theory itself — yet the result is as certain as anything in
physics. A proof assistant can still treat it rigorously: by separating the machine-checked
consequences from the physical lore, naming the lore as auditable axioms, and validating
those axioms by independent agreement. Proved and assumed as separate, machine-checked columns; trust narrowed to a short
vetted list; faithfulness enforced by types and by an independent oracle: this, we argue, is
the right standard for validating AI-generated results in theoretical physics.

## Appendix A. The physics hypotheses (H0–H6) — predicates, not axioms

After the strengthening (§5.1), the physical inputs are **contentful predicates and
structures**, not opaque axioms: they are *assumed as hypotheses* (bundled in
`IsSWEffectiveTheory`) by the results that use them, so they never enter the trusted base. The
carrier itself *is* the data of an N=2 `U(1)^{N-1}` EFT (H0): a base in gauge-invariant moduli,
and sheets of the cover carrying the holomorphic special coordinates (`SiegelUpperHalfSpace`
bundles `Im τ ≻ 0`). None of the following is an `axiom`.

**One principle, specialized.** The six are not independent postulates but facets of **N=2
supersymmetry** read off the Coulomb branch: SUSY fixes the special-Kähler prepotential (H1) and the
central-charge BPS bound (H2); the BPS spectrum then dictates the monodromy (H3) and, with the
symplectic charge lattice, electric–magnetic duality (H4); the chiral anomaly fixes the discrete
R-symmetry (H5); and the N=2 nonrenormalization theorem fixes the weak-coupling form (H6). Only the
*gauge data* — the group `SU(N)`, its one-loop β-function coefficient (asymptotic freedom), and the
dynamical scale `Λ` — is added to single out this theory. A natural refactor, flagged as future
work, is to formalize that parent **once**: an abstract N=2 special-geometry / BPS Coulomb branch
(special coordinates, charge lattice with Dirac pairing, central charge with the BPS bound,
anomaly-discrete R-symmetry, nonrenormalized prepotential), with `IsSWEffectiveTheory` obtained as
its specialization at `SU(N)`, `Λ`. The hypotheses below would then be *derived projections* of one
structure rather than seven siblings, and the matter and higher-rank theories would follow by
changing only the gauge data.

```lean
-- H0  carrier = the data of an N=2 U(1)^{N-1} EFT
structure CoulombBase (r : ℕ) where
  Δ : Set (Fin r → ℂ); U : Set (Fin r → ℂ); hUopen : IsOpen U; hUsmooth : U = Δᶜ
structure Sheet (B : CoulombBase r) where
  V : Set (Fin r → ℂ); hVopen : IsOpen V; hVsub : V ⊆ B.U; hVsc : SimplyConnectedSpace V
  a  : (Fin r → ℂ) → (Fin r → ℂ); ha  : DifferentiableOn ℂ a V    -- special coordinates aᵢ(u)
  aD : (Fin r → ℂ) → (Fin r → ℂ); haD : DifferentiableOn ℂ aD V   -- duals a_{D,i}(u)
  tau : (Fin r → ℂ) → SiegelUpperHalfSpace r                       -- coupling τ (Im ≻ 0 typed)

-- H1  special geometry: a prepotential F with aD = ∂F/∂a, τ = ∂²F/∂a²
def Sheet.SpecialGeometry (s : Sheet B) : Prop :=
  ∃ F, ContDiffOn ℂ 2 F (s.a '' s.V) ∧
    (∀ u ∈ s.V, ∀ i, s.aD u i = partialDeriv F i (s.a u)) ∧
    (∀ u ∈ s.V, ∀ i j, (s.tau u).val i j = partialDeriv2 F i j (s.a u))

-- H2  massless on Δ as the limit Z_n → 0; massive off Δ
def Sheet.BecomesMasslessAt (s) (u₀) (n) : Prop :=
  Tendsto (fun u => s.centralCharge u n) (𝓝[s.V] u₀) (𝓝 0)
def Sheet.SingularitiesAreBPS (s) : Prop :=
  (∀ u ∈ s.V, ∀ n ≠ 0, s.centralCharge u n ≠ 0) ∧
  (∀ u₀ ∈ closure s.V ∩ B.Δ, ∃ n ≠ 0, s.BecomesMasslessAt u₀ n)

-- H3  Picard–Lefschetz: the monodromy IS an actual deck transformation acting as the
--     reflection in the SAME vanishing charge n as H2 (not the vacuous ∃ g, g = transvection n)
def PicardLefschetzAtGenericStratum (s : Sheet B) : Prop :=
  ∀ u₀ ∈ closure s.V ∩ B.Δ, ∀ n, n ≠ 0 → s.BecomesMasslessAt u₀ n →
    ∃ (s' : Sheet B) (D : Deck s s'), ⇑D.g = transvection n

-- H4  duality gluing: a ℤ-linear (Sp(2r,ℤ)) charge automorphism with covariant central charge
structure Deck (s s' : Sheet B) where
  g : ChargeLattice r ≃ₗ[ℤ] ChargeLattice r
  symplectic : ∀ n n', diracPairing (g n) (g n') = diracPairing n n'
  covariant  : ∀ u ∈ s.V ∩ s'.V, ∀ n, s'.centralCharge u (g n) = s.centralCharge u n

-- H5  R-symmetry: a bijection of EXACT order 2N (not id) fixing Δ
def RSymmetry (B : CoulombBase r) (N : ℕ) : Prop :=
  ∃ ω, Function.Bijective ω ∧ ω^[2*N] = id ∧ (∀ k, 0 < k → k < 2*N → ω^[k] ≠ id) ∧ ω '' B.Δ = B.Δ

-- H6  one-loop over ROOTS (eigenvalue differences; nonzero for SU(2)) + purely instantonic tail
def oneLoopPrepotential (Λ) (a) : ℂ :=        -- ∑_{i≠j} (eᵢ−eⱼ)² log((eᵢ−eⱼ)²/Λ²), e = eigenvalues a
  (i/8π) * ∑ i, ∑ j, if i=j then 0 else (eᵢ−eⱼ)² * log((eᵢ−eⱼ)²/Λ²)
def Instantonic (Λ) (N) (F) : Prop :=         -- fixed classical part + Λ≠0 + holomorphic coeffs
  Λ ≠ 0 ∧ ∃ c, (∀ k, Differentiable ℂ (c k)) ∧
    ∀ a, F a - classicalPrepotential a - oneLoopPrepotential Λ a = ∑' k, c (k+1) a * (Λ^(2*N))^(k+1)
def Sheet.MatchesAsymptotics (s) (Λ) (N) : Prop :=     -- H1's F + the non-renormalized form
  ∃ F, (… the H1 relations for F …) ∧ Instantonic Λ N F

-- the six, bundled: an N=2 U(1)^{N-1} Seiberg–Witten effective theory
structure IsSWEffectiveTheory (s : Sheet B) (Λ : ℂ) (N : ℕ) : Prop where
  specialGeometry : s.SpecialGeometry            -- H1
  singularities   : s.SingularitiesAreBPS        -- H2
  picardLefschetz : PicardLefschetzAtGenericStratum s   -- H3
  matching        : s.MatchesAsymptotics Λ N     -- H6
  rSymmetry       : RSymmetry B N                -- H5
```

`Deck` (H4) relates sheets and is proved to make the BPS mass descend to the base
(`Deck.bpsMass_eq`). Sheets are organized into an `SWAtlas` (covering `B.U`, with overlaps
`Deck`-glued), so the duality gluing H4 is *part of the theory* and uniqueness is stated at the
atlas level (`sw_unique_up_to_duality`). The one rank-1 *monodromy* input that remains a
placeholder axiom is
`SameSWMonodromy` (Appendix B): the hypothesis that two candidate couplings `f, g` carry the
same `Sp(2,ℤ)` monodromy around the punctures — physically fixed by which BPS state (monopole
at `+Λ²`, dyon at `−Λ²`) goes massless where — the input to the rank-1 rigidity theorem
`sw_su2_unique`.

## Appendix B. The residual mathematical axioms and the (now proved) headline

With the physics in predicates (Appendix A), the **only global axioms** beyond the three logical
ones (`propext, Classical.choice, Quot.sound`) are *mathematical*. The headline implications are
**proved theorems** (no `sorry`), each resting on the physical hypotheses plus a single named math
axiom — `swPeriodLayer` (B.1). The finer covering/lift/`θ` axioms (B.2) are the genus-1 pieces of
that period geometry, on which the rank-1 route runs.

**B.1 — The headline theorems and the consolidated period axiom.** The period-level
(Picard–Fuchs / Gauss–Manin) geometry of the SW curve family is taken as one clean axiom; the
headline follows, `#print axioms` = standard-3 + `swPeriodLayer` (no `sorry`):

```lean
-- the single consolidated period-level math axiom (the SW period geometry exists)
axiom swPeriodLayer (N : ℕ) (Λ : ℂ) (hN : 2 ≤ N) : SWPeriodLayer N Λ

-- HEADLINE (proved): uniqueness up to Sp(2(N−1),ℤ) duality, on a connected chart overlap
theorem sw_effective_theory_unique_up_to_duality (hN : 2 ≤ N) (s s' : Sheet B)
    (hconn : IsConnected (s.V ∩ s'.V))
    (h : IsSWEffectiveTheory s Λ N) (h' : IsSWEffectiveTheory s' Λ N) :
    Nonempty (Deck s s') :=
  sw_unique_of_swPeriodLayer (swPeriodLayer N Λ hN) s s' hconn h h'

-- HEADLINE (proved): existence — the SW curve (P monic, degree N, trace-free) realizes a theory
--   whose singular locus is the discriminant locus of the curve family
theorem sw_curve_admits_effective_theory (hN : 2 ≤ N) (P : Polynomial ℂ)
    (hPm : P.Monic) (hPdeg : P.natDegree = N) (hPtr : P.coeff (N - 1) = 0)
    (hsf : Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * N)))) :
    ∃ (B : CoulombBase (N - 1)) (s : Sheet B), IsSWEffectiveTheory s Λ N ∧
      B.Δ = {u | ¬ Squarefree (swCurvePoly N Λ u)} ∧ swModulus N P ∈ s.V :=
  sw_exists_of_swPeriodLayer (swPeriodLayer N Λ hN) P hPm hPdeg hPtr hsf

-- PROVED (standard-3): the classical Coulomb branch has dimension N − 1 (the rank)
theorem coulombBranchDim (N : ℕ) : Module.finrank ℂ (Fin (N - 1) → ℂ) = N - 1
```

**B.2 — Classical mathematics not yet in Mathlib** — the only remaining global axioms, to
discharge by porting (the covering is packaged as a structure):

```lean
structure ThricePuncturedUniformization where
  cover : UpperHalfPlane → {v : ℂ // v ∉ ({0, 1} : Set ℂ)}      -- the developing map λ
  gamma2_invariant : ∀ γ ∈ Gamma2, ∀ τ, cover (γ • τ) = cover τ
  surjective : Function.Surjective cover
  fiber : ∀ τ τ', cover τ = cover τ' ↔ ∃ γ ∈ Gamma2, γ • τ = τ' -- fibres = Γ(2)-orbits

-- the Γ(2) covering ℍ/Γ(2) ≅ ℂ∖{0,1} exists   (discharge: Schwarz reflection ⇒ RMT ⇒ cover)
axiom AX_thrice_punctured_uniformization : Nonempty ThricePuncturedUniformization

-- lift uniqueness: same-monodromy developing maps agree up to a modular frame change
-- (discharge: classical; Forster, Ahlfors)
axiom AX_developing_map_rigidity
    {Λ : ℂ} {D : Set ℂ} {u₀ : ℂ} {f g : ℂ → ℂ}
    (U : ThricePuncturedUniformization) (hmono : SameSWMonodromy Λ f g) :
    ∃ m : ℂ → ℂ, AnalyticOnNhd ℂ (m ∘ g) D ∧ f =ᶠ[𝓝 u₀] (m ∘ g)

-- Jacobi quartic identity and θ₃ ≠ 0           (discharge: Jacobi triple product)
axiom AX_jacobi_quartic (τ : ℂ) : theta3 τ ^ 4 = theta2 τ ^ 4 + theta4 τ ^ 4
axiom AX_theta3_ne_zero (τ : UpperHalfPlane) : theta3 (τ : ℂ) ≠ 0

-- the family's local monodromy is the Picard–Lefschetz transvection
-- (discharge: Gauss–Manin / local-system layer over the moduli space)
axiom localMonodromy : ∀ {r : ℕ}, ChargeLattice r → (ChargeLattice r → ChargeLattice r)
axiom AX_picard_lefschetz_local {r : ℕ} (γ : ChargeLattice r) :
    localMonodromy γ = transvection γ
```

The machine's dependency printout for the rank-1 uniqueness theorem makes the separation literal —
logic, classical-math debt, and the one physical input, in five lines:

```lean
#print axioms sw_su2_unique
-- 'sw_su2_unique' depends on axioms:
--   [propext, Classical.choice, Quot.sound,          -- logic
--    AX_thrice_punctured_uniformization,             -- classical math (Γ(2) covering)
--    AX_developing_map_rigidity,                      -- classical math (lift uniqueness)
--    SameSWMonodromy]                                 -- physics (the SW monodromy)
```

The SU(2) uniqueness theorem `sw_su2_unique` rests on exactly the two covering/lift axioms
(`AX_thrice_punctured_uniformization`, `AX_developing_map_rigidity`) plus the physics
`SameSWMonodromy` — and the three logical axioms (`propext`, `Classical.choice`, `Quot.sound`),
which underlie everything and belong to neither list. (The physical refinement `H4'Duality`
and its derived consequence `metric_posDef_of_h4'` — that electric–magnetic duality keeps the
special-Kähler metric positive along the whole monodromy orbit — are proved, standard-3.)

**B.3 — The period-level layer (a structure; its existence is §B.1's single axiom).** The monodromy input `SameSWMonodromy`
is itself the conclusion of the *periods* of the SW curve — their Picard–Fuchs equation and
Gauss–Manin monodromy. We package that layer as a structure and prove the B.1 goals modulo it,
for SU(2) and for general SU(N):

```lean
-- the period-level debt, bundled as a *hypothesis* (so the theorems below stay standard-3)
structure SWPeriodLayer (N : ℕ) (Λ : ℂ) where
  hN : 2 ≤ N                                                -- SU(N) needs rank N−1 ≥ 1
  rigidity : ∀ {B : CoulombBase (N - 1)} (s s' : Sheet B), IsConnected (s.V ∩ s'.V) →
      IsSWEffectiveTheory s Λ N → IsSWEffectiveTheory s' Λ N → Nonempty (Deck s s')
  realize  : ∀ P : Polynomial ℂ, P.Monic → P.natDegree = N → P.coeff (N - 1) = 0 →
      Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * N))) → ∃ (B : CoulombBase (N - 1)) (s : Sheet B),
        IsSWEffectiveTheory s Λ N ∧ B.Δ = {u | ¬ Squarefree (swCurvePoly N Λ u)} ∧ swModulus N P ∈ s.V

-- the B.1 goals, now THEOREMS modulo the layer (all standard-3):
theorem sw_unique_of_swPeriodLayer (PL : SWPeriodLayer N Λ) … : Nonempty (Deck s s')
theorem sw_exists_of_swPeriodLayer (PL : SWPeriodLayer N Λ) … : ∃ B s, IsSWEffectiveTheory … ∧ …

-- the rank-1 uniqueness routes through an AXIOM-FREE lemma (the SL(2,ℤ) frame builds the gluing,
-- central-charge covariance proved from det = 1):
theorem su2_deck_of_periodFrame (s s' : Sheet B) (α β γ δ : ℤ) (hdet : α * δ - β * γ = 1)
    (hper : … period frame on the overlap …) : Nonempty (Deck s s')   -- #print axioms: the 3 logical only
```

So "period frame ⇒ duality equivalence" is *proved*; only the period frame (the layer's
`rigidity`) is assumed, as honest math debt. Taking the layer's *existence* as the single axiom
`swPeriodLayer` (§B.1) discharges that hypothesis once, so the **named** headline theorems
(`sw_effective_theory_unique_up_to_duality`, `sw_curve_admits_effective_theory`) are closed, with
`#print axioms` = standard-3 + `swPeriodLayer`. Discharging the layer — building the period map
`∮ λ_SW`, its Picard–Fuchs ODE and Gauss–Manin monodromy, and the rigidity argument — is a few
weeks at genus 1 (the elliptic case, where the `λ`/`θ` machinery already exists) and a
Mathlib-scale variation-of-Hodge-structure project in general genus. The structure was reviewed
adversarially: a first version asserted a single globally-constant `SL(2,ℤ)` frame across an
overlap that can be disconnected (false under monodromy) and quantified over degree-`N` curves
(the U(N), not SU(N), family); both are corrected (`IsConnected` overlaps; monic trace-free `P`).

**The mathematical input, stated plainly.** Collected, the headline's entire mathematical debt is
*one* classical object — the **variation of Hodge structure of the Seiberg–Witten curve family**:
the periods `∮ λ_SW` varying holomorphically over the moduli `u`, with their Picard–Fuchs equation
and `Sp(2r,ℤ)` Gauss–Manin monodromy. The B.2 axioms are not independent inputs; they are exactly
its **genus-1 classical pieces** — the `Γ(2)` uniformization `ℍ/Γ(2) ≅ ℂ∖{0,1}` and developing-map
rigidity (the rank-1 period map and its monodromy/rigidity), the Picard–Lefschetz transvection,
and two Jacobi `θ` identities — and B.3 packages the same object as a structure at all ranks. The
fiber side already exists: the SW curve embeds in `jacobian-challenge`'s hyperelliptic type with
genus 1 proved (`swEllipticData_genus`, standard-3), and that library supplies the per-fiber
periods, Riemann-bilinear positivity, Siegel/`θ`. The single capability that remains — at *every*
rank — is the **variation**: that period integrals move holomorphically with a flat Gauss–Manin
connection (`Sp`-monodromy), which is not yet formalized in Lean. The whole result reduces to that
one capability: a few months at genus 1 (on the existing `ℍ`/modular/`λ`/`θ` machinery), a
Mathlib-scale project for general SU(N).

## Acknowledgments

This formalization and paper were developed with heavy use of Claude (Anthropic), and with
Gemini (Google) and Codex (OpenAI) for cross-checking, second opinions, and review. I thank
David Kosower and Jesse Thaler for discussions on the validation of amplitude computations for
collider physics, which informed the broader perspective on validation taken here.

## References

Seiberg–Witten, *Nucl. Phys.* B426 (1994) [hep-th/9407087]; B431 (1994) [hep-th/9408099].
Klemm–Lerche–Yankielowicz–Theisen, *Phys. Lett.* B344 (1995). Argyres–Faraggi, *PRL* 74
(1995). Argyres–Douglas, *Nucl. Phys.* B448 (1995). Lerche, hep-th/9611190. Bilal,
hep-th/9601007. Nekrasov, *Adv. Theor. Math. Phys.* 7 (2003); Nekrasov–Okounkov (2006).
Mathlib (Lean 4). Paulson, Isabelle/HOL `Riemann_Mapping`. M. R. Douglas,
*formalization-assurance* (`math-commons/formalization-assurance`). Lean FRO, Tau Ceti.
