# Scoping: closing the SU(2) uniqueness goal (B.1) as a theorem

*How to turn the rank-1 case of the headline `sw_effective_theory_unique_up_to_duality`
(`Physics/Hypotheses.lean`, currently `theorem … := sorry`) into a real theorem, with **no new
axiom** beyond the B.2 math debt already assumed. Companion to
[`COVERING_SCOPING.md`](COVERING_SCOPING.md) and the working paper §7.*

## Target

```lean
-- the B.1 goal, specialized to SU(2) (r = 1), in Deck form:
theorem (B : CoulombBase 1) (s s' : Sheet B) (Λ : ℂ)
    (h : IsSWEffectiveTheory s Λ 2) (h' : IsSWEffectiveTheory s' Λ 2) … :
    Nonempty (Deck s s')
```
with intended footprint **exactly the one we already display for `sw_su2_unique`**:
`propext, Classical.choice, Quot.sound, AX_thrice_punctured_uniformization,
AX_developing_map_rigidity, SameSWMonodromy` — i.e. standard-3 + the two B.2 covering/lift
axioms + the one physics monodromy input. No new axiom.

## Current state

- `SU2Rigidity.sw_su2_unique` is **proved** (this footprint): two holomorphic period maps
  `f, g : ℂ → ℂ` on a connected chart with `SameSWMonodromy Λ f g` agree **up to an `SL(2,ℤ)`
  frame change** (`su2_frame_alignment` consumes the covering + lift-uniqueness;
  `holo_eqOn_of_germ` propagates).
- The B.1 statement is *different in form*: it is over the `Sheet`/`IsSWEffectiveTheory`
  carrier and concludes `Nonempty (Deck s s')`. It is `sorry`, and is **not** wired to
  `sw_su2_unique`.

So the gap is **packaging**, plus one genuinely-new lemma (the monodromy comparison). The
analytic core (rigidity) is done.

## The closure, as four steps

### Step A — monodromy comparison (the one substantive new piece)

**Claim.** Two SW theories `s, s'` over the *same* SU(2) base `B` (same `Δ = {±Λ²}`) carry the
*same* `Sp(2,ℤ)` monodromy up to an overall frame change — i.e. `SameSWMonodromy` holds for
their period maps after conjugation.

*Why it should follow from the hypotheses:* H2 (`SingularitiesAreBPS`) gives both the **same**
singular locus and, at each puncture, a massless charge; H3 (`PicardLefschetzAtGenericStratum`)
gives that the **local** monodromy there is `transvection n` in that charge; H6
(`MatchesAsymptotics`) fixes the semiclassical monodromy `M_∞` at `∞`. The relation
`M_{+} · M_{-} = M_∞` in `Sp(2,ℤ)` then pins the representation up to overall conjugacy.

**Honest blocker.** Making "the local monodromies *compose* to `M_∞`" precise needs a
**`π₁(ℂ ∖ {±Λ²}) → Sp(2,ℤ)` representation** — the family / local-system (Gauss–Manin) layer,
which is **not yet present** (`Monodromy.localMonodromy` is an abstract charge-lattice map with
no `π₁`). So Step A in full needs that layer.

**Consequence for scope.** Until the local-system layer exists, keep `SameSWMonodromy` as the
**physics input** (an explicit hypothesis / the existing physics axiom). Then Steps B–D below
close the goal *modulo that input* — which is exactly the displayed footprint. This is the
bounded, reachable target; Step A removes the input later (it is the same work as `EMDuality`
getting real content in `Monodromy.lean`).

### Step B — rigidity ⇒ frame change (reachable now)

Express the sheet's coupling `s.tau : V → SiegelUpperHalfSpace 1 ≅ ℍ` (via `siegelOneEquiv`) as
the period map, and apply `su2_frame_alignment` (which already consumes
`AX_thrice_punctured_uniformization` + `AX_developing_map_rigidity`) to get an `SL(2,ℤ)` frame
change `m` with `s'.tau =ᶠ m • s.tau` near the cusp, then `holo_eqOn_of_germ` to spread it over
the chart. **This is `sw_su2_unique`'s mechanism**; the work is restating it for the `Sheet`
coupling rather than abstract `f, g`.

### Step C — build the `Deck` (real bookkeeping)

From the coupling frame change `m ∈ SL(2,ℤ) = Sp(2,ℤ)`, construct `Deck s s'`:
- `g :=` the **charge-lattice action** of `m` (the contragredient `Sp(2,ℤ)`-action on
  `ChargeLattice 1 = ℤ² `), as a `≃ₗ[ℤ]`;
- `symplectic`: `m ∈ Sp(2,ℤ)` preserves `diracPairing` — a finite `2×2` computation;
- `covariant`: `s'.centralCharge u (g n) = s.centralCharge u n` on the overlap — the central
  charge `Z = nₑ a + n_m a_D` is the duality-invariant pairing of the charge with the period
  vector, so `m` acting on periods and `g` acting (contragradiently) on charges cancel. This is
  the linear-algebra heart: relate the `m`-action on `(a_D, a)` to the `g`-action on `(n_e,
  n_m)`.

### Step D — wire to B.1 (mechanical)

Replace the `sorry` in `sw_effective_theory_unique_up_to_duality` (r = 1 case) with
`⟨buildDeck …⟩` from Steps B–C. Re-check `#print axioms` matches the target footprint.

## What is reachable now vs blocked

| Step | needs | status |
|---|---|---|
| **C (build `Deck`)** | `Sp(2,ℤ)` charge action + covariance algebra | **DONE** — `su2_deck_of_periodFrame` (`SU2Uniqueness.lean`), **standard-3, zero axioms**: period frame (det 1) ⇒ `Deck`, with `symplectic` + `covariant` derived from `det = 1`. |
| B (rigidity ⇒ frame change) | `su2_frame_alignment` (have it) + period-vs-coupling scale lift | **partly reachable** — the coupling frame change is `su2_frame_alignment`; lifting it to the *period-vector* frame `(s'.a_D, s'.a) = M·(s.a_D, s.a)` (the input `su2_deck_of_periodFrame` consumes) needs fixing the overall scale (BPS normalization). |
| D (wire to B.1) | B, C | **reachable** once B supplies the period frame |
| A (derive `SameSWMonodromy` from H2/H3/H6) | `π₁ → Sp(2,ℤ)` local-system layer | **blocked** (family/Gauss–Manin layer absent) |

So: **B + C + D close the SU(2) B.1 uniqueness goal modulo `SameSWMonodromy`** (the physics
monodromy input) — turning the `sorry` into a theorem whose footprint is the one already
advertised. Step A (removing that last input) is the family-layer project, shared with giving
`EMDualityConsistent` real content.

## Effort

Recalibrated to the project's Lean-time norms (sister-task, infrastructure present):
- **Steps B–D: a few active days** (~2–5). The analytic content exists (`sw_su2_unique`); the
  new work is the `Deck` construction (Step C) — the coupling↔charge covariance is the one
  genuine lemma, a `2×2` `Sp` computation plus the period/charge pairing identity.
- **Step A: weeks**, and only after the `π₁ → Sp` local-system / Gauss–Manin layer exists (the
  general infrastructure investment; not SU(2)-specific).

## Recommendation

Do **B + C + D** as the next bounded piece: it converts a headline `sorry` into a genuine
theorem `sw_su2_unique_deck` (or by filling the B.1 `sorry` directly, with `SameSWMonodromy` as
a hypothesis), resting on **exactly** standard-3 + the two B.2 axioms + the physics monodromy
input — no new axiom, and the paper's "uniqueness proved for SU(2)" claim becomes literally the
B.1 statement rather than a separate concrete one. Defer Step A to the family-layer roadmap.
