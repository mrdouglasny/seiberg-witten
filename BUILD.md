# Building

`seiberg-witten` is a Lake project whose **only dependency is Mathlib**, pinned by
`lake-manifest.json` (Lean toolchain in `lean-toolchain`).

```bash
lake exe cache get   # fetch Mathlib .oleans from the cloud cache
lake build           # builds SeibergWitten + RiemannPeriods
```

## Verify

```bash
bash audit/gen_axiom_report.sh --check    # golden #print axioms certificate in sync
python3 audit/check_faithfulness.py       # FAITHFULNESS.md quotes match the source
```

## The unbuilt higher-genus layer

`HigherGenus/` is **not** part of the build; it depends on the external
[`jacobian-challenge`](https://github.com/mrdouglasny/jacobian-challenge) library. To
work on it, see `HigherGenus/README.md` (clone `jacobian-challenge` as a sibling,
restore its `[[require]]` in `lakefile.toml`, move the files back under
`SeibergWitten/`).
