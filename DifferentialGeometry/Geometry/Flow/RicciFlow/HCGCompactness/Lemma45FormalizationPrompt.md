# Lemma 4.5 Formalization Prompt

Use this prompt to start a fresh thread.

```text
We are working in `E:\differential-geometry` on the RicciFlower/HCG compactness
layer. Read:

- `AGENTS.md`
- `important_lesson.md`
- `lessons.md`
- `RicciFlower/HCGCompactness/Lemma45FormalizationPlan.md`

Task: start formalizing Lemma 4.5 from the approximate-isometry compactness
argument, following the plan file. Do not formalize the printed proof directly:
extract the hidden "sum of terms" and "choose a larger constant" steps into
explicit constants and finite-sum lemmas first.

First pass scope:

1. Inspect the existing RicciFlower definitions for approximate isometry,
   pullback metrics, Levi-Civita connections, iterated covariant derivatives,
   covariant tensor fields, and tensor norms.
2. Produce a short name map in a same-folder note before editing Lean files.
3. Implement only the geometry-free algebra layer first:
   - `oneStepConst`
   - `lemma45Const`
   - nonnegativity / positivity / monotonicity lemmas
   - finite range-sum lemmas
   - the main induction-step algebra lemma
4. Do not start with mixed tensors. The first real theorem target is the
   covariant `(0,s)` abstract version under an abstract connection-difference
   bound.

Suggested first files:

- `RicciFlower/HCGCompactness/Lemma45Constants.lean`
- `RicciFlower/HCGCompactness/SumLemmas.lean`
- update `RicciFlower/HCGCompactness/Lemma45FormalizationPlan.md` or create a
  same-name `.md` note with what passed/failed.

Constraints:

- Search RicciFlower first; do not import `.reference` or external DG code.
- Keep algebra below geometry.
- Use focused `lake-locked` checks.
- Stop if the proof starts unfolding approximate isometry or Christoffel
  symbols inside the main induction; those belong in a later connection
  difference producer.
- If stuck after three attempts, report the exact theorem, goal/error, lemmas
  tried, and the smallest next lemma.

Acceptance for the first thread:

- The constants and finite-sum algebra files compile, or the exact algebra
  blocker is recorded.
- No new geometry assumptions or theorem-shaped frontier wrappers are added.
```

