# IntrinsicOffZero.lean — L1 of the A0′ lane (velocity-regularity of intrinsic exp)

Verification: **PASS** (focused check + targeted module build, sorry-free, no new axioms).

## Headline: L1 was a FALSE WALL

The A0′ plan (`A0PRIME_VOLUME_PLAN.md` §8 "B5-pre scout findings" item 4) and
`A0PRIME_AREA_CONSULT.md` declared "off-zero / large-`v` regularity of
`expMapIntrinsic x` in the velocity" the lane's single genuine frontier, claiming
only at-zero (`mfderiv_expMapIntrinsic_at_zero`) and small-ball / variational forms
exist.  **This is wrong.**  The tree already contains, sorry-free and **global**:

- `intrinsicFiber_smooth` (`Exponential/IntrinsicVelocity.lean:191`):
  `ContMDiff 𝓘(ℝ, E) I ∞ (fun v : E ↦ expMapIntrinsic g hEnorm p v)` — at *every* `v`,
  across chart boundaries.  Built from the geodesic spray `geodesicVectorField`
  (`Geodesic/Equation.lean`) + the compact-trajectory flow `flow_slice_smooth`
  (`Analysis/ODE/.../CompactTrajectory.lean`) on `TangentBundle I M`, projected via
  `intrinsicExp_smooth`.  Used tree-wide (CartanLocal, BranchRadius, ExpInvBranch,
  PuncturedCartan, RadialLog, JacobiVariation).
- Dependency chain verified sorry-free; `HopfRinow.lean`'s 4 sorrys sit in the
  minimizing-between-points capstones, declared after and unreachable from the
  velocity-branch lemmas `intrinsicGeodesic` uses.

Lesson (matches `MEMORY.md` "grep the canonical producer before declaring walls"):
the scout listed `mfderiv_expMapIntrinsic_at_zero` but never grepped
`intrinsicFiber_smooth`, the actual global producer.  No new large-`v` regularity
proof is needed.

## What this file adds (the consumable form)

`expChart_contDiffAt` — the Euclidean chart-composed regularity that L2/L5 actually
consume: for `expMapIntrinsic p v` in the chart at `y₀`,
`ContDiffAt ℝ ∞ (fun b ↦ extChartAt I y₀ (expMapIntrinsic p b)) v`.  This is NOT a
redundant alias of `intrinsicFiber_smooth` — it is `intrinsicFiber_smooth.contMDiffAt`
composed with the target chart (`contMDiffOn_extChartAt`, valid at the target) and
read as a Euclidean map (`contMDiffAt_iff_contDiffAt`).  Its
`.differentiableAt.hasFDerivAt` is the Euclidean derivative whose `|det|` enters the
area formula `MeasureTheory.image_lintegral_le`.

## Home choice

Placed in `Exponential/Smoothness/` (sibling of `IntrinsicMfderivZero.lean`, the
at-zero derivative) — the canonical home for intrinsic-exp regularity — rather than
the plan's suggested `Comparison/Exponential/Smoothness/` (which would spawn a new
subtree for one lemma).  Recorded here per CLAUDE.md canonical-home discipline.
