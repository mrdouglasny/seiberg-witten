# Axioms for physical reasoning: codifying the Seiberg–Witten solution in Lean

*Working paper, draft. Companion to the formal development at
[`mrdouglasny/seiberg-witten`](https://github.com/mrdouglasny/seiberg-witten) and to the
ICML 2026 talk "Validation of AI-generated results in theoretical physics."*

## Abstract

Most results in theoretical physics are not theorems: they are conclusions of arguments
that the community trusts without a proof from foundations, and often without any prospect
of one. We argue that interactive theorem provers are nonetheless the right tool for such
results — not to prove them, which is impossible, but to **codify the physical reasoning as
explicit named axioms**, prove every rigorous consequence of those axioms, and keep a
machine-checked line between the two. The residual trust then collapses onto a short,
inspectable, individually-vetted list of physical inputs, and the proof assistant's
`#print axioms` makes the dependency of every downstream result auditable. We develop this
program for the Seiberg–Witten solution of N=2 SU(N) super-Yang–Mills, formalized in Lean 4
on top of Mathlib and a Riemann-surface library. We report what is proved, what is assumed,
how the assumptions are vetted (external review and an independent numerical oracle), and
why this discipline is the appropriate standard for validating AI-generated results in
theoretical physics.

## 1. The problem: physics is mostly not theorems

A mathematician formalizing a theorem has a proof to formalize. A physicist formalizing a
*result* usually does not. The Seiberg–Witten (SW) solution is the textbook case. There is
no proof, from the axioms of mathematics, that the low-energy effective theory on the
Coulomb branch of N=2 SU(N) gauge theory is governed by the hyperelliptic curve
`y² = P_N(x)² − Λ^{2N}`. What exists is an *argument* — a tight web of physical assumptions
(holomorphy from supersymmetry, the exact structure of singularities, electric–magnetic
duality, the asymptotics) that together single out that curve, and which the community
trusts because three independent computations agree.

So "formalizing Seiberg–Witten" cannot mean "proving it." Naively, this seems to put the
result outside the reach of formal methods. We argue the opposite: the result is *exactly*
the kind that benefits most from formalization, provided one is honest about what is being
done.

> State the physical assumptions as **explicit, named axioms**; prove every **rigorous
> consequence** of them as a theorem; keep a bright, machine-checked line between the two.

We call the second column — the codified non-rigorous reasoning physicists nonetheless
trust — **foundations for physical reasoning**, by analogy with foundations of mathematics.
The contribution of a formalization is then threefold: it makes the dependency structure
machine-checkable, it localizes the residual trust onto a small set of explicit axioms, and
it lets the verifier detect contradiction among them.

## 2. Two kinds of formalization in physics

| | What it is | Examples |
|---|---|---|
| **Traditional mathematical physics** | A rigorous statement exists; you prove it. | Stability of matter; constructive QFT (OS axioms); lattice-gauge mass gap; **and the rigorous spine of this project** — the curve, its genus, special-Kähler positivity, the period matrix. |
| **Foundations for physical reasoning** | Codifying the *non-rigorous* reasoning the community trusts, where there is no proof from foundations and may never be. | **The Seiberg–Witten *argument* itself.** |

The two columns are not a value judgment; they are a *bookkeeping discipline*. A `proved`,
axiom-free theorem can still be the **wrong statement** (a dropped hypothesis, a flipped
sign, a narrowed domain), and a physical input dressed up as a definition can smuggle a
falsehood past the kernel. The discipline forces every physical assumption into the open as
a named axiom, and every mathematical claim onto the proved side.

## 3. The Seiberg–Witten solution, briefly

On the Coulomb branch (gauge-invariant moduli `u₂,…,u_N`, rank `r = N−1`) the low-energy
theory is abelian `U(1)^r` gauge theory. Its data are the special coordinates `aᵢ` and their
duals `a_{D,i}` (periods of a meromorphic differential), the effective coupling matrix
`τ_{ij}`, and the central charge `Z = nₑ·a + n_m·a_D` of a BPS state, whose modulus is its
mass. The SW claim is that all of this *is* the period geometry of the curve
`y² = P_N² − Λ^{2N}`. The physical inputs that single out that curve are: (1) holomorphy /
non-renormalization (one holomorphic prepotential `F`, one-loop-exact perturbation theory);
(2) the exact singularity structure (the Coulomb branch is singular exactly where a BPS
state becomes massless, and nowhere else); (3) electric–magnetic duality (`Sp(2r,ℤ)`
monodromy); (4) the `ℤ_{2N}` R-symmetry fixing the singularity pattern; (5) asymptotic
matching to the one-loop + instanton expansion.

## 4. The formalization

### 4.1 The proved spine (column 1)

On top of a hyperelliptic-curve / period / Jacobian library, the following are theorems,
sorry-free, with `#print axioms` reporting only the three standard logical axioms
(`propext, Classical.choice, Quot.sound`) — except where an off-critical-path inherited
axiom is transited, as noted:

- `genus_swCurve`: the SU(N) curve has genus `N−1`.
- `sw_coupling_mem_siegel`, `sw_metric_posDef`: the period matrix `τ` is symmetric with
  `Im τ ≻ 0` — special-Kähler metric positivity, the physical no-ghost statement (transits
  one inherited hyperelliptic cycle-basis axiom).
- `su2_singular_locus`: for SU(2), the curve is singular **exactly** at `u = ±Λ²` — the
  monopole and dyon points, *and no others*. A computation (the discriminant), not lore.
- `transvection_isSymplectic`: a Picard–Lefschetz monodromy preserves the intersection form,
  i.e. lands in `Sp(2r,ℤ)` — the algebraic reason monodromy is symplectic.
- A modular-`λ` layer for the rank-1 base: `λ = θ₂⁴/θ₃⁴` built from Mathlib's `jacobiTheta₂`,
  the cusp symmetry `1 − λ = θ₄⁴/θ₃⁴`, and `λ`'s invariance under both generators of `Γ(2)`
  (`modularLambda_add_two`, `modularLambda_S`, `modularLambda_ST2S`) — establishing `λ` as a
  proved `Γ(2)`-Hauptmodul.

### 4.2 The codified hypotheses (column 2)

The physical inputs (1)–(5) are stated as named axioms in a single module, with docstrings
giving the source and a faithfulness note, and tracked in an axiom-audit table. The headline
lore — that these inputs fix the solution **uniquely up to `Sp(2r,ℤ)` duality** — is itself a
named axiom (`sw_effective_theory_unique_up_to_duality`), because it is the physicists'
argument, not a ZFC theorem. `#print axioms` of any downstream result then exhibits exactly
which physical inputs it rests on.

### 4.3 Two methodological dividends

Formalizing forced two clarifications that informal exposition routinely elides.

**Faithfulness of the carrier (the type system refuses a convenient falsehood).** Our first
attempt typed the periods `a, a_D` and coupling `τ` as single-valued functions on the moduli
space `ℂ^r`. External review (Gemini) flagged this as *vacuous*: a global holomorphic map
`ℂ^r → SiegelUpperHalfSpace` is **constant** by Liouville, forcing a free theory. The
multivalued data must live on the universal cover of `ℂ^r ∖ Δ`. The corrected formalization
encodes this — the type of the data refuses the free-theory shortcut that prose glosses over.

**Derived, not assumed (Argyres–Douglas).** Argyres–Douglas points — where the theory becomes
an interacting SCFT with no Lagrangian — look like they need their own physical postulate. In
the formalization they are a *definition*: `ArgyresDouglasLocus`, the locus where two
**mutually non-local** BPS charges (nonzero Dirac pairing) become massless together,
constructed from the central charge and the charge lattice already in hand. A surprise the
theory should explain comes out as a consequence, not a new axiom — a test the axiom set
passes.

## 5. Vetting the axioms, and validation by independent agreement

Localizing trust onto named axioms is only valuable if the axioms are then *vetted*. We use
three tools, in increasing cost.

**Numerical cross-check against an independent oracle.** Where a statement has computable
content, we evaluate it in a separately-authored engine (mpmath / numpy) sharing no
provenance with the Lean. A run of 44 checks at 40-digit precision (`audit/numerical/`) vets
the Jacobi quartic identity `θ₃⁴ = θ₂⁴ + θ₄⁴` and `θ₃ ≠ 0` (both currently assumed),
confirms the proved `λ` transformation laws are *faithful* (catching any sign/shift error),
anchors the normalization via `λ(i) = ½`, and checks the SU(2) singularity locus. Tellingly,
the oracle first caught a **branch bug in itself** (a half-integer power evaluated on the
wrong branch) before agreeing with the Lean to full precision — the method demonstrating its
own bite. A numeric pass is necessary, not sufficient: it validates values, not
logical-structure faithfulness (quantifier scope, hypothesis strength, vacuity).

**Cross-model statement review and self-audit** against the pinned sources, recorded per
entry in a correspondence index (`status` vs `fidelity` as separate columns) and a fidelity
review.

**The physicist's triangle as the deepest validation.** The reason the SW lore is trusted is
that three independent handles on the prepotential agree: one-loop perturbation theory, the
instanton expansion (Nekrasov's partition function, itself later made rigorous), and the
exact periods of the curve. This *independent agreement* is the empirical content behind the
axioms, and the assurance protocol attaches it as numeric cross-checks rather than assertion.

## 6. Why this is the right standard for AI-generated physics

When an AI produces a physics result, the failure mode is rarely a wrong algebra step that a
referee would catch; it is an **unstated assumption** smuggled in as if derived. Reasoning
from physics axioms makes that structurally impossible to hide:

- every physical input must be *named* to be used;
- every named input appears in `#print axioms` of the results that depend on it;
- an honest definition (the universal-cover carrier; Argyres–Douglas as a derived locus)
  refuses to encode a convenient falsehood, because the kernel checks the types;
- the remaining job — *justifying* the axioms — is the physicist's, and is done by the same
  independent-agreement checks (Nekrasov vs. periods, monodromy composition, numeric
  evaluation) that earn trust in the first place.

Formalization does not make the physics true. It makes the reasoning **auditable** — and that
is exactly what a result no one can prove from first principles needs.

## 7. The frontier: what remains, and where it lives

The discipline also makes the *remaining* mathematical debt legible. For the rank-1 (SU(2))
case, demoting the uniqueness headline to a theorem reduces to a small, sharply-identified set
of **Mathlib-scale** developments (tracked in `audit/PROOF_STATUS.md`):

1. the **Jacobi triple product** (discharges the theta-null identities and non-vanishing);
2. the **modular-`λ` covering** `ℍ/Γ(2) ≅ ℂ∖{0,1}` — whose `Γ(2)`-invariance clause is now
   proved, leaving the surjectivity/fibre (true covering) content;
3. the **Gauss–Manin / variation-of-Hodge-structure** layer over the moduli space.

The covering rests in turn on the **Riemann mapping theorem and the Schwarz reflection
principle**, which are absent from Lean/Mathlib (RMT is formalized in Isabelle/HOL). These are
general complex analysis, not SW-specific, and we have scoped them as upstream contributions —
a draft "conformal mapping & geometric function theory" roadmap entry (RMT as summit, Schwarz
reflection as a layer) for the Lean FRO's Tau Ceti library, positioned to sit between existing
contour-integration and modular-forms roadmaps. The point: the proved/assumed discipline turns
"is this physics right?" into a precise, prioritized list of mathematical theorems to build.

## 8. Related work

The assurance artifacts (correspondence index, fidelity review, numerical validation, axiom
audit, `formalization.yaml`) follow the `math-commons/formalization-assurance` conventions. The
upstream-contribution framing targets the Lean FRO's Tau Ceti library. The Riemann mapping
theorem has been formalized in Isabelle/HOL (Paulson); the Schwarz reflection principle and the
SW solution appear unformalized prior to this work.

## 9. Conclusion

The Seiberg–Witten solution is a result that cannot be proved and is nonetheless certain. We
have shown that a proof assistant can still treat it rigorously, by separating the
machine-checked implications from the codified physical lore, naming the latter as auditable
axioms, and validating those axioms by independent agreement. This *foundations-for-physical-
reasoning* discipline — proved/assumed as separate, machine-checked columns; trust localized
onto a short vetted list; faithfulness enforced by types and by an independent oracle — is, we
argue, the appropriate standard for validating AI-generated results in theoretical physics.

## References

Seiberg–Witten, *Nucl. Phys.* B426 (1994) [hep-th/9407087]; B431 (1994) [hep-th/9408099].
Klemm–Lerche–Yankielowicz–Theisen, *Phys. Lett.* B344 (1995). Argyres–Faraggi, *PRL* 74
(1995). Argyres–Douglas, *Nucl. Phys.* B448 (1995). Lerche, hep-th/9611190. Bilal,
hep-th/9601007. Nekrasov, *Adv. Theor. Math. Phys.* 7 (2003); Nekrasov–Okounkov (2006).
Mathlib (Lean 4). Paulson, Isabelle/HOL `Riemann_Mapping`. `math-commons/formalization-assurance`.
Lean FRO, Tau Ceti.
