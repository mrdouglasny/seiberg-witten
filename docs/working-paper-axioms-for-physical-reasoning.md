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
discipline is a sound standard for validating AI-generated results in theoretical physics.

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
entirely. The discipline forces every physical input into the open as a named axiom, and
every mathematical claim onto the proved side.

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

The physical assumptions (H0–H6) are stated as named **predicates and structures** in one
module — the carrier `CoulombBase`/`Sheet` (an N=2 `U(1)^{N-1}` EFT) and the hypotheses
`SpecialGeometry`, `SingularitiesAreBPS`, `PicardLefschetzAtGenericStratum`, `Deck`,
`RSymmetry`, `MatchesAsymptotics`, bundled in `IsSWEffectiveTheory` (Appendix A). They are the
irreducible physics — there is nothing to prove about them — but they are *not global axioms*:
a result that uses the physics takes `IsSWEffectiveTheory` as a **hypothesis**, so the
dependence is explicit in its signature, even more transparent than an axiom and never entering
the trusted base. The only global axioms (besides the three logical ones) are *mathematical* —
the monodromy/modular/covering inputs of Appendix B.2.

The headline claims are different in kind. That the SW curve *realizes* a theory satisfying
the assumptions (existence), and that the assumptions fix the solution **uniquely up to
`Sp(2r,ℤ)` duality** (uniqueness), are not physical inputs but *mathematical* consequences:
given the assumptions, each should be a **theorem** — uniqueness, in particular, is a
period-map rigidity statement. We therefore state them as **goals** (`theorem … := sorry`),
*not* axioms — visible holes to close, which never enter the trusted base — because their
proofs are not yet in place in general (they need the covering and Riemann-mapping machinery of
§7). Discharging them *purifies* the development: the mathematical claims move onto the proved
side, leaving only the five genuinely-physical inputs (and the classical-math axioms of §B.2)
as assumptions. `#print axioms` reports exactly the physical inputs and classical-math axioms a
result uses; the open goals are flagged by `sorry`.

For SU(2) we have carried this out. The rank-1 uniqueness statement is now a **theorem**:
printing its axioms returns only the three logical axioms, the physics monodromy input, and
two named **classical-math** axioms — the modular-`λ` covering `ℍ/Γ(2) ≅ ℂ∖{0,1}` and the
uniqueness of its developing maps — with **no bespoke placeholder**. The two tiers are now
explicit in the proof itself: the physics axiom is irreducible, while the two math axioms are
debt, discharged once the (Mathlib-scale) complex analysis of §7 lands. This is the
purification in miniature — the headline reduced to *physics + standard mathematics*, with the
machine confirming nothing else slipped in.

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
  Δ : Set (Fin r → ℂ); U : Set (Fin r → ℂ); hUopen : IsOpen U; hUsmooth : U ⊆ Δᶜ
structure Sheet (B : CoulombBase r) where
  V : Set (Fin r → ℂ); hVopen : IsOpen V; hVsub : V ⊆ B.U; hVsc : SimplyConnectedSpace V
  a  : (Fin r → ℂ) → (Fin r → ℂ); ha  : DifferentiableOn ℂ a V    -- special coordinates aᵢ(u)
  aD : (Fin r → ℂ) → (Fin r → ℂ); haD : DifferentiableOn ℂ aD V   -- duals a_{D,i}(u)
  tau : (Fin r → ℂ) → SiegelUpperHalfSpace r                       -- coupling τ (Im ≻ 0 typed)

-- H1  special geometry: a prepotential F with aD = ∂F/∂a, τ = ∂²F/∂a²
def Sheet.SpecialGeometry (s : Sheet B) : Prop :=
  ∃ F, DifferentiableOn ℂ F (s.a '' s.V) ∧
    (∀ u ∈ s.V, ∀ i, s.aD u i = partialDeriv F i (s.a u)) ∧
    (∀ u ∈ s.V, ∀ i j, (s.tau u).val i j = partialDeriv2 F i j (s.a u))

-- H2  massless on Δ as the limit Z_n → 0; massive off Δ
def Sheet.BecomesMasslessAt (s) (u₀) (n) : Prop :=
  Tendsto (fun u => s.centralCharge u n) (𝓝[s.V] u₀) (𝓝 0)
def Sheet.SingularitiesAreBPS (s) : Prop :=
  (∀ u ∈ s.V, ∀ n ≠ 0, s.centralCharge u n ≠ 0) ∧
  (∀ u₀ ∈ closure s.V ∩ B.Δ, ∃ n ≠ 0, s.BecomesMasslessAt u₀ n)

-- H3  Picard–Lefschetz: reflection in the SAME vanishing charge n as H2
def PicardLefschetzAtGenericStratum (s : Sheet B) : Prop :=
  ∀ u₀ ∈ closure s.V ∩ B.Δ, ∀ n, s.BecomesMasslessAt u₀ n → ∃ g, g = plReflection n

-- H4  duality gluing: an Sp(2r,ℤ) charge action with covariant central charge
structure Deck (s s' : Sheet B) where
  g : ChargeLattice r → ChargeLattice r
  symplectic : ∀ n n', diracPairing (g n) (g n') = diracPairing n n'   -- ∈ Sp(2r,ℤ)
  covariant  : ∀ u ∈ s.V ∩ s'.V, ∀ n, s'.centralCharge u (g n) = s.centralCharge u n

-- H5  R-symmetry: a ℤ_{2N} action on the moduli fixing Δ
def RSymmetry (B : CoulombBase r) (N : ℕ) : Prop :=
  ∃ ω, (∀ u, ω^[2*N] u = u) ∧ ω '' B.Δ = B.Δ

-- H6  asymptotic matching / non-renormalization (one-loop + purely instantonic remainder)
def Instantonic (Λ) (N) (Fcl F) : Prop :=
  ∃ c, ∀ a, F a - Fcl a - oneLoopPrepotential Λ a = ∑' k, c (k+1) a * (Λ^(2*N))^(k+1)
def Sheet.MatchesAsymptotics (s) (Λ) (N) : Prop :=     -- H1's F + the non-renormalized form
  ∃ F Fcl, (… the H1 relations for F …) ∧ Instantonic Λ N Fcl F

-- the six, bundled: an N=2 U(1)^{N-1} Seiberg–Witten effective theory
structure IsSWEffectiveTheory (s : Sheet B) (Λ : ℂ) (N : ℕ) : Prop where
  specialGeometry : s.SpecialGeometry            -- H1
  singularities   : s.SingularitiesAreBPS        -- H2
  picardLefschetz : PicardLefschetzAtGenericStratum s   -- H3
  matching        : s.MatchesAsymptotics Λ N     -- H6
  rSymmetry       : RSymmetry B N                -- H5
```

`Deck` (H4) relates sheets and is proved to make the BPS mass descend to the base
(`Deck.bpsMass_eq`). The one rank-1 *monodromy* input that remains a placeholder axiom is
`SameSWMonodromy` (Appendix B): the hypothesis that two candidate couplings `f, g` carry the
same `Sp(2,ℤ)` monodromy around the punctures — physically fixed by which BPS state (monopole
at `+Λ²`, dyon at `−Λ²`) goes massless where — the input to the rank-1 rigidity theorem
`sw_su2_unique`.

## Appendix B. The residual axioms (mathematical) and the open goals

With the physics now in predicates (Appendix A), the **only global axioms** beyond the three
logical ones (`propext, Classical.choice, Quot.sound`) are *mathematical* — B.2. **B.1**
collects the open goals (the headline implications, `theorem … := sorry`) and the one classical
fact we *prove*.

**B.1 — Goals, and a proved classical fact.** The headline implications are mathematical
consequences of the hypotheses, stated as `sorry`-goals over the new carrier, not axioms:

```lean
-- GOAL: uniqueness up to Sp(2r,ℤ) duality   [PROVED for SU(2): sw_su2_unique; general open]
theorem sw_effective_theory_unique_up_to_duality (s s' : Sheet B)
    (h : IsSWEffectiveTheory s Λ N) (h' : IsSWEffectiveTheory s' Λ N) :
    Nonempty (Deck s s') := by sorry

-- GOAL: existence — the SW curve furnishes a sheet satisfying H1–H6
theorem sw_curve_admits_effective_theory (P : Polynomial ℂ) (Λ : ℂ)
    (hPdeg : P.natDegree = N) (hN : 2 ≤ N)
    (hsf : Squarefree (P ^ 2 - Polynomial.C (Λ ^ (2 * N)))) :
    ∃ (B : CoulombBase (N - 1)) (s : Sheet B), IsSWEffectiveTheory s Λ N := by sorry

-- PROVED (3): the classical Coulomb branch has dimension N − 1 (the rank), from the gauge group
theorem coulombBranch_classical (N : ℕ) : Module.finrank ℂ (Fin (N - 1) → ℂ) = N - 1
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

The SU(2) uniqueness theorem `sw_su2_unique` rests on exactly the two covering/lift axioms
(`AX_thrice_punctured_uniformization`, `AX_developing_map_rigidity`) plus the physics
`SameSWMonodromy` — and the three logical axioms (`propext`, `Classical.choice`, `Quot.sound`),
which underlie everything and belong to neither list. (The physical refinement `H4'Duality`
and its derived consequence `metric_posDef_of_h4'` — that electric–magnetic duality keeps the
special-Kähler metric positive along the whole monodromy orbit — are proved, standard-3.)

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
