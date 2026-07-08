# Why the physical postulates have mathematical names

*Design note, 2026-07-07. The convention is stated in `AXIOM_AUDIT.md` ("Naming
(math-primary)") and embodied in `SeibergWitten/Physics/Dictionary.lean`; this note
records the reasoning, after the question "for math axioms math names are primary,
but for physical postulates why not make physics names primary?"*

## The question

The bundle of physical hypotheses H1–H6 is named `IsPolarizedPeriodChart`, not
`PhysicalHypotheses` or `IsSWEffectiveTheory`; the H-carriers are
`PeriodsDegenerateOnBoundary`, `HasFiniteOrderAutomorphism`, and so on — mathematical
vocabulary throughout, with the physics names supplied only as machine-linked
`abbrev` aliases in the dictionary. For *classical mathematics* axioms this is
obviously right: the statement is the entire content and the justification is a
citation. But the H's are **physical** postulates. Why shouldn't physics names be
primary there?

## The resolution: names track content; the dictionary tracks justification

What differs between a math axiom and a physical postulate is the *justification*,
not the kind of formal content. The formal content of a physical postulate is still
just mathematics — one specific **transcription** of the physics into a predicate.
The physics name properly belongs to the *informal* postulate (the paper's H2, "BPS
singularities"); the Lean predicate is not that postulate but a candidate rendering
of it, and the gap between the two is exactly where this project's errors have
lived. Naming is what makes that gap visible or invisible:

- **Named mathematically**, the predicate claims only what its definition says; the
  identification "this mathematics is the physics" is a separate, human-reviewable
  claim, concentrated in one place (the dictionary, `Dictionary.lean` / paper §4.1).
- **Named physically**, every theorem type would assert the identification
  implicitly — a small unfalsifiable claim the kernel cannot check, distributed
  across the development.

## The deciding scenario: vacuity review (twice, in this project)

The case that decides the convention is reviewing a predicate for vacuity or
under-specification, and it is not hypothetical:

1. **H5.** The first version of the R-symmetry carrier was satisfiable by far too
   little. The fix (redefine faithfully + prove non-vacuity) happened because review
   asked whether `HasFiniteOrderAutomorphism` actually delivers the ℤ₂ₙ action the
   paper claims. Had the predicate been named `RSymmetry`, the name itself would
   have answered the question the review needed to ask. A wrong or vacuous predicate
   wearing the physics name is precisely how misformalization survives review.
2. **The matter chart.** The honest disclosure that the discharged witness is
   non-SQCD was possible to *state* cleanly because `IsMatterPolarizedPeriodChart`
   never claimed in its name to be SQCD.

Math-primary naming keeps the burden of proof on the dictionary, where a human can
dispute the identification in one place.

## Physics names are still primary — in the physics medium

The physics vocabulary is not demoted; it is located where physics claims are
adjudicated:

- the paper's **H0–H7 labels**, inline glosses, and the dictionary table (§4.1);
- machine-linked aliases: `abbrev IsSWEffectiveTheory ... := IsPolarizedPeriodChart`
  (`Dictionary.lean`). An `abbrev` is definitionally transparent, so a
  physics-facing theorem can be *stated* in physics vocabulary while the certificate
  and the kernel see the same mathematical object. Nothing is weakened.

If physicist readability of the headline theorem types becomes a priority, the
right move is to state those theorems through the aliases (optionally adding
per-hypothesis aliases, e.g. `BPSSingularities := PeriodsDegenerateOnBoundary`) —
not to rename the ground-truth structures.

## Honest concessions

- The convention is not perfectly observed: `SpurionCovariantFamily` uses physics
  vocabulary (there is no purely mathematical word for a spurion), and
  `PicardLefschetzAtGenericStratum` is mathematics that happens to be the physics.
  The working rule: **name by the checkable structure; borrow physics words only
  where they have become mathematics.**
- There is a real readability cost: a physicist reading
  `PeriodsDegenerateOnBoundary` in a theorem type does not hear "a BPS state goes
  massless." The mitigations (dictionary, glosses, aliases) are documentation, not
  enforcement.

## Summary

Keep math-primary names as ground truth: names should not assert what only the
dictionary can claim, and the project's own history (H5, the matter chart) shows the
review pressure arrives exactly at the "does the mathematics deserve the physics
name" step. Flipping primacy would be mechanically trivial — and would trade away
the property that saved us twice.
