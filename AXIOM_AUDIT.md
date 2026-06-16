# Axiom audit — seiberg-witten

*Last updated 2026-06-15.*

Format + conventions:
[`math-commons/formalization-assurance/AXIOM_AUDIT_FORMAT.md`](https://github.com/math-commons/formalization-assurance/blob/main/AXIOM_AUDIT_FORMAT.md).
This is a **forward-chaining** project (formalizing the SW corpus on top of
`jacobian-challenge`); the primary assurance artifact is the
[correspondence index](audit/CORRESPONDENCE_INDEX.md), not the axiom audit.

**Own project axioms: 0.**

| Result | Phase | `#print axioms` |
|---|---|---|
| `genus_swCurve`, `genus_swCurve_su2` | 0 | **standard-3** |
| `sw_coupling_mem_siegel*`, `sw_metric_posDef` | 1a | standard-3 + `Jacobians.Axioms.AX_PeriodCycleBasis` |

The project declares **no axioms of its own**. Phase 0 (genus) is standard-3.
Phase 1a (special geometry / metric positivity) transits the inherited
`AX_PeriodCycleBasis` — jacobian-challenge's hyperelliptic cycle-basis axiom, **off
the Buzzard critical path**. The axiom-free SU(2) route (Phase 1b) would remove it
for genus 1. Per-result axiom sets are tracked in `formalization.yaml ›
main_results` and verified by `#print axioms`.
