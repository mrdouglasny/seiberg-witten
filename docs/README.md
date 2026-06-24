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
- [`refs/`](refs/) — primary papers (SW1, SW2, PDFs checked in), `SU(N)` curve papers,
  and pedagogical reviews, with per-paper summaries.
- [`talk/`](talk/) — the ICML 2026 talk (`validation.tex` + PDF), self-contained
  (theme + assets bundled, relative paths) so it builds anywhere: `pdflatex validation.tex`.
