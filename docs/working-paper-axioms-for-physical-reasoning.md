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

The five physical assumptions of §3 are stated as named axioms in one module, each with its
source and a faithfulness note. These are the irreducible physics — there is nothing to prove
about them. (We use Lean's global `axiom` keyword deliberately, as a *dependency-tracking*
device: it is exactly what `#print axioms` reports, so every assumption surfaces natively in
the footprint of any result that uses it. Because a false axiom would make the whole system
inconsistent, each is treated as a debt to discharge, not a convenience — the audit tracks
them as such.)

The headline claims are different in kind. That the SW curve *realizes* a theory satisfying
the assumptions (existence), and that the assumptions fix the solution **uniquely up to
`Sp(2r,ℤ)` duality** (uniqueness), are not physical inputs but *mathematical* consequences:
given the assumptions, each should be a **theorem** — uniqueness, in particular, is a
period-map rigidity statement. We state them as named axioms today only as placeholders,
because their proofs are not yet in place (they need the covering and Riemann-mapping
machinery of §7). Discharging them is precisely that program, and it *purifies* the axiom
list: it moves these mathematical claims onto the proved side, leaving only the five
genuinely-physical inputs as assumptions. Until then, printing the axioms behind a result
shows both — and makes visible exactly which placeholder still stands between the physics and
the theorem.

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

## References

Seiberg–Witten, *Nucl. Phys.* B426 (1994) [hep-th/9407087]; B431 (1994) [hep-th/9408099].
Klemm–Lerche–Yankielowicz–Theisen, *Phys. Lett.* B344 (1995). Argyres–Faraggi, *PRL* 74
(1995). Argyres–Douglas, *Nucl. Phys.* B448 (1995). Lerche, hep-th/9611190. Bilal,
hep-th/9601007. Nekrasov, *Adv. Theor. Math. Phys.* 7 (2003); Nekrasov–Okounkov (2006).
Mathlib (Lean 4). Paulson, Isabelle/HOL `Riemann_Mapping`. M. R. Douglas,
*formalization-assurance* (`math-commons/formalization-assurance`). Lean FRO, Tau Ceti.
