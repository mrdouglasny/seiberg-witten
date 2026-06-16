# Building

`seiberg-witten` is a Lake project that depends on `jacobian-challenge` (which in
turn pulls Mathlib + the Kirov Dolbeault port). The dependency is a **path** require
to a sibling checkout.

## Layout

```
~/Documents/GitHub/
  jacobian-challenge/     # built (its .lake/packages has Mathlib etc.)
  seiberg-witten/         # this repo
```

## Fast setup (reuse jacobian-challenge's built deps, no Mathlib re-download)

```bash
cd seiberg-witten
mkdir -p .lake
cp -c -R ../jacobian-challenge/.lake/packages .lake/packages   # APFS clone
lake update Jacobians                                            # register path dep + manifest
lake build SeibergWitten
```

`cp -c` (APFS clonefile) reuses Mathlib's built `.olean`s; `lake update` reuses the
Mathlib cloud cache (no re-download). Build time is then just this repo's files.

## Verify

```bash
lake env lean -- <<'LEAN'
import SeibergWitten.Curve
#print axioms SeibergWitten.genus_swCurve   -- [propext, Classical.choice, Quot.sound]
LEAN
```
