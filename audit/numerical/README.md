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

Run:
```
python3 -m venv .venv && .venv/bin/pip install mpmath numpy
.venv/bin/python validate_lambda.py
```

What is and isn't covered, and the per-entry verdicts, are in
[`../FIDELITY_REVIEW.md`](../FIDELITY_REVIEW.md). A numeric pass is *necessary, not
sufficient* — it validates values, not logical-structure faithfulness (quantifiers,
hypothesis strength, vacuity, global non-vanishing).
