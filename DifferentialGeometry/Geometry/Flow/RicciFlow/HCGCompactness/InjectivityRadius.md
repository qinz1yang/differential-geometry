# InjectivityRadius

Source used: MSM135 Chapter 3 Theorems 3.9 and 3.10, specifically the basepoint injectivity-radius hypotheses.

Introduced definitions: `HasInjRadiusAt`, `BaseInjBound`, and `FlowBaseInjBound`.

Design note: `HasInjRadiusAt` now wraps the real normal-coordinate predicate `Coordinates.Normal.injRadAtLeast`. The sequence-level records still express the MSM135 uniform positive basepoint lower bound.

2026-05-27 adoption update: HCG injectivity radius now imports the normal-coordinate backend and exposes the definitional bridge plus the admissible-radius producer lemma. This layer requires `[I.Boundaryless]`, matching normal coordinates.

Verification: passed.

2026-07-01 Step-C closure update: added `BaseInjBound.subseq`, the
subsequence projection for the basepoint injectivity-radius lower bound.  This
is data-valued, so it is a `def`, not a theorem.  Verification passed.

2026-07-10 quantitative-radius update: added `HasInjRadiusAt.mono`, the
canonical restriction lemma from a known radius to any smaller positive
radius.  This is the low-level bridge used by bounded-distance uniform floors.
Verification passed.
