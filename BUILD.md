# Building

`seiberg-witten` is a Lake project that depends on `jacobian-challenge` (which in
turn pulls Mathlib + the Kirov Dolbeault port). The dependency is a **path** require
to a sibling checkout.

**Reproducibility pin.** The paper's audited claims (repository tag `v0.2-paper`)
were built against `jacobian-challenge` commit `f4f908faa2880eb661b1e1c385cdc12533b97579`
(Mathlib v4.30.0 via its manifest). Check out that commit in the sibling directory
to reproduce the golden `#print axioms` trace exactly.

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
