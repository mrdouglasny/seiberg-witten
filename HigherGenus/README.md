# HigherGenus/ — the Riemann-surface / higher-genus layer (not built)

These files carry the general-`SU(N)` period-geometry spine — the genus computation
(`genus_swCurve`: the SW curve has genus `N−1`), Siegel positivity via the Riemann
bilinear relations (`sw_metric_posDef`, `sw_coupling_mem_siegel`), the curve family as
hyperelliptic data (`SWFamily`), and the family period matrix (`PeriodMap`). They
depend on the external `Jacobians` library (`mrdouglasny/jacobian-challenge`, with its
vendored Kirov Dolbeault port) and are **excluded from the build**: the main
`SeibergWitten` library is self-contained on pinned Mathlib, and its golden axiom
trace (`audit/axiom-report.txt`) contains no `Jacobians` axiom.

To re-enable: clone `jacobian-challenge` as a sibling directory, restore

    [[require]]
    name = "Jacobians"
    path = "../jacobian-challenge"

in `lakefile.toml`, move these files back under `SeibergWitten/` (adjusting the module
imports accordingly), and re-register them in `SeibergWitten.lean`. This layer is the
natural home of the future higher-genus campaign (discharging `periodRigidityAxiom`,
§6/B.1 of the paper).
