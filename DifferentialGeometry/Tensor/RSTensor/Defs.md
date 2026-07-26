# RSTensor Defs

## 2026-07-12 — opaque-fiber evaluation API

- Added canonical `Tensor0SSpace` evaluation lemmas for negation, subtraction, finite
  sums, and natural-number scalar multiplication, alongside the existing
  zero/addition/field-scalar lemmas.
- These are representation-boundary projection lemmas, not new tensor concepts or assumptions.
- Focused verification and the targeted upstream refresh passed without `sorry`.

## 2026-07-24 — TensorRS TotalSpace topology diamond dedup (Edit A)

Spec: `Geometry/Flow/RicciFlow/ShortTime/UNIF_DIAMOND_PRO_RULING.md`.

- Kept all five canonical instances (`tensorRSSpace_topologicalSpace`,
  `tensorRSBundle_topology`, `tensorRSBundle_fiber`, `tensorRSBundle_vector`,
  `tensorRSBundle_smooth`). The pointwise fiber topology
  `tensorRSSpace_topologicalSpace r s x` is the CANONICAL pointwise fiber
  topology (NOT a total-space topology, despite the earlier D-round
  mis-classification); `tensorRSBundle_topology r s` is the sole canonical
  total-space topology.
- HARDENED `tensorRSBundle_fiber`: its trailing inferred pointwise-family `_`
  argument (the `[∀ b, TopologicalSpace (E b)]` slot of `@FiberBundle`) is now
  the explicit canonical family `fun x : M => tensorRSSpace_topologicalSpace r s x`.
  No priority changes. Targeted `+…RSTensor.Defs` build is GREEN, so the explicit
  family is defeq to what `Bundle.ContinuousLinearMap.fiberBundle` produces.
- The redundant higher-layer total-space/fiber/vector aliases were demoted to
  `def` in `…ChartTensor/Inner/TensorRSContRiemannianBundle.lean` (Edit B). See
  that file's `.md`.
- PROBE LESSON: synthesizing `NormedSpace ℝ (TensorRSModel r s ℝ E)` (and hence
  `VectorBundle`) from a bare `Defs`-only context requires
  `set_option backward.isDefEq.respectTransparency false` (the same file-local
  option this file uses at line 50). That is a model-fiber-normed
  defeq-transparency matter, orthogonal to the topology dedup.
