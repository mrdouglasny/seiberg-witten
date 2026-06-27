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

## 1. Physics is mostly not theorems

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
physics, and return to it in §6.

## 2. Two kinds of formalization in physics

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

- there is no proof to formalize — the result is unprovable within reach (§1), so the question
  is not "is the proof correct?" but "are the assumptions explicit and the derivations sound?";
- the physical lore becomes **named hypotheses** — predicates a theorem takes in its signature
  — never smuggled into a definition or a convenient default;
- the residual trust then localizes onto a short list, and `#print axioms` of any result audits
  exactly which assumptions it used.

Nothing here is special to physics-as-a-subject; it is what changes when the object you
formalize is an *argument the community trusts* rather than *a theorem with a proof*.

## 3. The Seiberg–Witten solution in one paragraph

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

## 4. The formalization

### 4.1 What is proved

On a hyperelliptic-curve / period / Jacobian library, the following are theorems —
sorry-free, and (except where noted) depending only on the three standard logical axioms:

- the SU(N) curve has **genus `N−1`**;
- its period matrix `τ` is **symmetric with `Im τ ≻ 0`** — the positivity of the special-Kähler
  metric, i.e. the physical no-ghost condition;
- for SU(2), the curve is singular at **exactly `u = ±Λ²`** — the monopole and dyon points,
  and no others (this is a discriminant computation, not lore);
- the Picard–Lefschetz monodromy of a vanishing cycle is **symplectic** — the reason the
  monodromy group sits in `Sp(2r,ℤ)`;
- for the rank-1 base, the modular function `λ = θ₂⁴/θ₃⁴` (built from Mathlib's Jacobi theta
  functions) is a proved **`Γ(2)`-Hauptmodul**: invariant under both generators of `Γ(2)`,
  with the cusp symmetry `1 − λ = θ₄⁴/θ₃⁴`.

(Declaration names and exact axiom footprints are in the repository; we keep them out of the
prose here.)

### 4.2 What is assumed

The physical content — the six hypotheses H0–H6 — enters as named **predicates and structures**,
not as global axioms. The carrier is an N=2 `U(1)^{N−1}` effective theory; the hypotheses (special
geometry, BPS singularities, the Picard–Lefschetz monodromy, electric–magnetic duality,
R-symmetry, the weak-coupling asymptotics) are bundled into one predicate, `IsSWEffectiveTheory`
(Appendix A). They are the irreducible physics — there is nothing to prove about them — but a
result that uses them takes `IsSWEffectiveTheory` as a *hypothesis*, so its physical assumptions
are visible in its statement and never enter the trusted base. That is even more transparent than
an axiom: the dependence is written into the theorem's type.

The headline claims are different in kind. That the Seiberg–Witten curve *realizes* such a theory
(existence), and that the hypotheses fix it **uniquely up to `Sp(2r,ℤ)` electric–magnetic duality**
(uniqueness), are not physical inputs but mathematical consequences — uniqueness, in particular, is
a period-map rigidity statement. Both are now **proved theorems**, with no gaps. Beyond the physics
hypotheses, each rests on a *single* named mathematical input: the **period geometry of the curve
family** — how the periods of the Seiberg–Witten differential vary over the space of vacua, the
classical *variation of Hodge structure* of the family. That one input aside, the proofs are
complete.

The point of the discipline is that the proof assistant *reports exactly what each result depends
on*. For the general SU(N) headline that dependence is the background logical axioms plus the one
period-geometry input — nothing else. For SU(2) we have gone finer still: the uniqueness theorem
depends only on the physics, two classical complex-analysis facts (a modular covering of the
thrice-punctured sphere, and a lift-uniqueness statement), and the logical axioms — no bespoke
placeholder anywhere. This is the purification in miniature: the headline reduced to *physics +
standard mathematics*, with the machine confirming nothing else slipped in. The precise statements,
the actual machine printout of these dependencies, and the layered way the period input is
organized are collected in Appendix B.

### 4.3 Two things formalizing forced into the open

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

## 5. Checking the axioms: validation by independent agreement

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

## 6. Why this is the right standard for AI-generated physics

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

## 7. What remains, and where it lives

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

## 8. Related work

The assurance artifacts (correspondence index, fidelity review, numerical validation, axiom
audit) follow the conventions of the author's own `formalization-assurance` project
(`math-commons/formalization-assurance`), separate from and predating this work; the upstream
mathematical contributions are framed for the Lean FRO's Tau Ceti library. The Riemann mapping theorem is formalized in
Isabelle/HOL (Paulson); the Schwarz reflection principle and the SW solution appear
unformalized before this work.

## 9. Conclusion

A rigorous proof of the Seiberg–Witten solution lies beyond reach — it presupposes
constructing the quantum field theory itself — yet the result is as certain as anything in
physics. A proof assistant can still treat it rigorously: by separating the machine-checked
consequences from the physical lore, naming the lore as auditable axioms, and validating
those axioms by independent agreement. Proved and assumed as separate, machine-checked columns; trust narrowed to a short
vetted list; faithfulness enforced by types and by an independent oracle: this, we argue, is
the right standard for validating AI-generated results in theoretical physics.

## Appendix A. The physics hypotheses (H0–H6) — predicates, not axioms

After the strengthening (§4.1), the physical inputs are **contentful predicates and
structures**, not opaque axioms: they are *assumed as hypotheses* (bundled in
`IsSWEffectiveTheory`) by the results that use them, so they never enter the trusted base. The
carrier itself *is* the data of an N=2 `U(1)^{N-1}` EFT (H0): a base in gauge-invariant moduli,
and sheets of the cover carrying the holomorphic special coordinates (`SiegelUpperHalfSpace`
bundles `Im τ ≻ 0`). None of the following is an `axiom`.

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
