# docs/

Conceptual and reference material for the Seiberg–Witten formalization (the Lean code
lives at the repo root). Added as the motivating context for the ICML 2026 talk
*Validation of AI-generated results in theoretical physics*.

- [`intro-to-the-solution.md`](intro-to-the-solution.md) — short, self-contained
  introduction to the SW solution, oriented toward the formalization.
- [`foundations-for-physical-reasoning.md`](foundations-for-physical-reasoning.md) — why
  this project is the canonical example of *foundations for physical reasoning*: codifying
  non-rigorous physics lore (holomorphy, singularity structure, duality, asymptotic
  matching) as vetted axioms above the proved period geometry.
- [`reasoning-from-physics-axioms.md`](reasoning-from-physics-axioms.md) — the worked
  example: the actual Lean axioms and definitions (`Physics/Hypotheses.lean`), the
  proved-vs-assumed split, Argyres–Douglas points as a *derived* locus, and what
  `#print axioms` reveals — a model for auditing AI-generated physics.
- [`working-paper-axioms-for-physical-reasoning.md`](working-paper-axioms-for-physical-reasoning.md)
  — the **working paper**: the full argument (problem → two columns → the SW formalization →
  vetting by independent agreement → the AI-validation standard → the Mathlib-scale frontier),
  grounded in the actual declarations, axiom footprints, and the 44/44 numeric run. Draft;
  markdown working medium (LaTeX/PDF on request).
- [`refs/`](refs/) — primary papers (SW1, SW2, PDFs checked in), `SU(N)` curve papers,
  and pedagogical reviews, with per-paper summaries.
- [`talk/`](talk/) — the ICML 2026 talk (`validation.tex` + PDF), self-contained
  (theme + assets bundled, relative paths) so it builds anywhere: `pdflatex validation.tex`.
