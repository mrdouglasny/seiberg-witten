# Axiom audit — seiberg-witten

*Last updated 2026-06-15.*

Format + conventions:
[`math-commons/formalization-assurance/AXIOM_AUDIT_FORMAT.md`](https://github.com/math-commons/formalization-assurance/blob/main/AXIOM_AUDIT_FORMAT.md).
This is a **forward-chaining** project (formalizing the SW corpus on top of
`jacobian-challenge`); the primary assurance artifact is the
[correspondence index](audit/CORRESPONDENCE_INDEX.md), not the axiom audit.

**Own project axioms: 0.** Phase 0 (`SeibergWitten.genus_swCurve`) is
**standard-3** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

Inherited axioms: results that reach deeper into `jacobian-challenge` may transit
its remaining axioms (the three off-critical-path torus axioms; the declared
non-headline `AX_PeriodCycleBasis` scaffolding). Phase 0 transits none. Per-result
axiom sets are tracked in `formalization.yaml › main_results` and verified by
`#print axioms`.
