# seiberg-witten

The **Seiberg–Witten solution of N=2 SU(2) super-Yang–Mills**, formalized in **Lean 4**.

No rigorous proof of this result exists — it presupposes constructing the interacting
4d quantum field theory. What a proof assistant *can* do is treat the physics argument
rigorously: state the physical inputs as **explicit, named postulates** (H0–H7) and
dictionary transcriptions carried in theorem types — never as axioms — and machine-check
that the Seiberg–Witten solution follows. The trusted base is then Lean's three logical
axioms plus a short, named list of classical mathematics, tracked *per theorem* by a
golden `#print axioms` certificate. The companion paper is
[`docs/paper1.tex`](docs/paper1.tex).

The library is **self-contained on pinned Mathlib** and `sorry`-free.

## The claim

For SU(2)/genus one, the compiled development proves the listed Seiberg–Witten
consequences without `sorry` and without hidden physics axioms; physics enters through
explicit H0–H7 predicates, structures, definitions, and stated dictionary
transcriptions. The remaining trusted inputs beyond Lean's standard three are
explicitly named classical-mathematics axioms, tracked per theorem by
[`audit/axiom-report.txt`](audit/axiom-report.txt). The higher-rank SU(N) headline is a
proved skeleton modulo the coarse period-geometry axiom `periodRigidityAxiom`, whose
discharge is future work.

## What is proved (highlights)

- **Uniqueness up to Γ(2) duality** (`SU2.sw_su2_unique`, `sw_su2_unique_coulomb`):
  footprint = standard-3 + the Γ(2) covering/lift pair — nothing else. The full chain
  is formal: qualitative cusp data (`SWModulusData`) ⟹ the developing formula
  `λ(τ(u)) = 2Λ²/(u+Λ²)` *including its normalization*
  (`swModulusData_eq_crossRatio`, **axiom-free**) ⟹ uniqueness; and the cusp data
  itself follows from an H4-style atlas plus parabolic cusp lifts with non-extension
  (`swModulusData_of_atlas_and_lifts`).
- **The explicit coupling** (`su2_coupling_exists`, special coordinates, `da_D/da = τ`,
  the one-loop running): classical Jacobi inversion (`AX_elliptic_inversion`) as the
  one extra input.
- **Why exactly one monopole–dyon pair** (`singularity_count_pinch`): the Euler/mod-12
  counting alone allows `n ≡ 1 (mod 6)` — the K3 loophole is *witnessed* — and the
  R-spurion covariance (H7, through its curve transcription) pinches `n = 1`.
  Axiom-free.
- **SU(2) SQCD (matter)**: the coupling's uniqueness on the same classical basis
  (`matter_coupling_rigidity`); the Argyres–Douglas locus nonempty **axiom-free**
  (`matter_argyresDouglasLocus_nonempty`), via the development's first constructed
  period chart and an exact discriminant factorization.
- **The θ/λ layer**: `λ = θ₂⁴/θ₃⁴` proved Γ(2)-invariant, the S/T laws, `λ` omitting
  `{0,1}`, `λ → 0` at the cusp — on two citable Jacobi-θ identities.

## What is assumed

- **Physics**: the named postulates **H0–H7** (predicates and structures in theorem
  types — there is no physical `axiom` anywhere) and their stated curve/Kodaira
  transcriptions, each validated per
  [`audit/FIDELITY_REVIEW.md`](audit/FIDELITY_REVIEW.md).
- **Classical mathematics, as named axioms** (citable, numerically vetted): the Γ(2)
  covering/lift pair, Jacobi inversion, and two Jacobi-θ identities.
- **Higher rank only**: `periodRigidityAxiom` (Gauss–Manin period geometry) — the
  declared future work.

Full inventory: [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md).

## Verify it yourself

```bash
lake build                                # pinned Mathlib; no other dependency
bash audit/gen_axiom_report.sh --check    # the golden #print axioms certificate
python3 audit/check_faithfulness.py       # paper-facing quotes match the source
for f in audit/numerical/validate_*.py; do python3 "$f"; done   # 9 oracle suites, 278 checks
```

Reviewing the project? **Start at [`audit/REVIEWER.md`](audit/REVIEWER.md)** — the
claims, what each rests on, and the evidence per claim. The method follows
[`math-commons/formalization-assurance`](https://github.com/math-commons/formalization-assurance):
faithfulness digests with machine-verified quotes, fidelity review with independent
numeric cross-checks, difficult points recorded, adversarial statement review before
adoption.

## Layout

```
SeibergWitten/          the library (physics layer: Physics/)
RiemannPeriods/         weight-1 VHS bootstrap (Mathlib-only)
HigherGenus/            higher-genus Riemann-surface layer — NOT built (see below)
audit/                  certificate, checkers, oracles, V&V documents
docs/paper1.tex         the companion paper
```

## Higher genus and `jacobian-challenge`

The general-SU(N) story (genus `N−1` proved, Riemann-bilinear positivity
`Im τ ≻ 0`) lives in [`HigherGenus/`](HigherGenus/), which builds against the external
Riemann-surface / period / Jacobian library
[`jacobian-challenge`](https://github.com/mrdouglasny/jacobian-challenge) and is kept
**outside the certified build** — the main library and every footprint in the paper
are Mathlib-only. `HigherGenus/README.md` has the re-enable recipe; discharging
`periodRigidityAxiom` through that layer is the roadmap in
[`audit/PERIOD_LAYER_DISCHARGE.md`](audit/PERIOD_LAYER_DISCHARGE.md).

## Acknowledgments

The certified library depends only on Mathlib; it is the **higher-genus skeleton**
(`HigherGenus/`, outside the build) that builds against
[`jacobian-challenge`](https://github.com/mrdouglasny/jacobian-challenge), which in
turn vendors **Rado Kirov**'s Dolbeault/Riemann-surface development. This project owes
much to that library and its contributors — **Kevin Buzzard**, **Rado Kirov**, and the
[other contributors](https://github.com/mrdouglasny/jacobian-challenge/graphs/contributors).
See the paper's acknowledgments for the full list of colleagues whose reviews and
discussions shaped the project.

## License

Copyright 2026 Michael R. Douglas. Released under the
[Apache License 2.0](LICENSE) (the Lean/Mathlib ecosystem convention).
