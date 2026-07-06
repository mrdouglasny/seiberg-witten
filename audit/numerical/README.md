# Numerical validation

Independent-oracle cross-checks (per
[`formalization-assurance/NUMERICAL_VALIDATION.md`](https://github.com/math-commons/formalization-assurance/blob/main/NUMERICAL_VALIDATION.md)):
evaluate the formalized statements at sampled points with an engine that shares no
provenance with the Lean (mpmath / numpy), to catch sign/branch/normalization/constant
bugs the kernel cannot see.

- [`validate_lambda.py`](validate_lambda.py) — θ-null identities, the modular-`λ`
  transformation laws, and the SU(2) singularity locus.
- [`validate_lambda.out.txt`](validate_lambda.out.txt) — checked-in output (**44/44 pass**,
  `dps=40`, residuals ≲1e-40).
- [`validate_elliptic.py`](validate_elliptic.py) — pre-formalization vetting of the proposed
  C-route elliptic axioms (`../GENUS1_PERIODS_PLAN.md`): the `K, E` integral definitions vs
  `mpmath.ellipk/ellipe` (D0), Jacobi inversion / θ-bridge (C1), the Legendre relation (C2),
  the `K` log-asymptotic (C3).
- [`validate_elliptic.out.txt`](validate_elliptic.out.txt) — checked-in output (**84/84 pass**
  after the v2 review extensions, `dps=40`; C1 sampled in all four quadrants of the cut
  plane; both C4 cusp-monodromy checks).
- [`validate_swcrossratio.py`](validate_swcrossratio.py) — the `swCrossRatio` **pin**:
  branch-tracked contour quadrature of the SW curve periods, `λ(τ_curve(u))` against all
  six anharmonic Möbius candidates; winner `2Λ²/(u+Λ²)`, unique at every sample.
- [`validate_swcrossratio.out.txt`](validate_swcrossratio.out.txt) — checked-in output
  (**16/16 pass**, `dps=30`, residuals ≲ 1e-31).
- [`validate_specialcoords.py`](validate_specialcoords.py) — the special-coordinate pin
  (milestone S0): `a, a_D` closed forms vs `∮ x²dx/y` quadrature (unique bracket),
  `da_D/da = swTau`, monopole vanishing, weak-coupling normalization.
- [`validate_specialcoords.out.txt`](validate_specialcoords.out.txt) — checked-in output
  (**14/14 pass**, `dps=30`).

Run:
```
python3 -m venv .venv && .venv/bin/pip install mpmath numpy
.venv/bin/python validate_lambda.py
```

What is and isn't covered, and the per-entry verdicts, are in
[`../FIDELITY_REVIEW.md`](../FIDELITY_REVIEW.md). A numeric pass is *necessary, not
sufficient* — it validates values, not logical-structure faithfulness (quantifiers,
hypothesis strength, vacuity, global non-vanishing).
