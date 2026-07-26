# RestrictOpenRm04.lean — germ-locality of the metric (0,4) Riemann tensor

## Status: DONE, build-verified sorry-free (targeted `lake-locked build`, 2026-06-30).

Step B of the spherical-space-form quotient descent (plan
`plan-on-taking-a-spicy-kitten.md`, "Steps 6–7"). Lifts the connection-level
germ-locality to the curvature level.

## Results

- `connectionRiemannCurvatureField_restrictOpen` — the connection curvature field
  of the restricted Levi-Civita connection on restricted ambient smooth sections
  equals the ambient curvature field. Term-by-term match of the `∇∇ − ∇∇ − ∇_[]`
  structure.
- `metricRm04StdAt_restrictOpen` — `metricRm04StdAt (g.restrictOpen U) x = metricRm04StdAt g (↑x)`.

## Route (what worked)

The keystone `metricCov_restrictOpen_globalSection` (OpenSubtypeNaturality.lean:293)
already gives connection germ-locality on GLOBAL smooth sections. Lift to (0,4):

1. Reduce both sides to `connectionRiemannCurvatureField` via
   `riemannCurvature04At_apply_smooth` (Sections.lean:215) — this forces the use of
   genuine global smooth sections (`ContMDiffSection.exists_eq_at_gen` at `↑x`),
   NOT chart-constant extensions, because `metricCov_restrictOpen_globalSection`
   only speaks about `ContMDiffSection`.
2. The core lemma matches the three `∇∇/∇∇/∇_[]` terms: nested inner sections
   `y ↦ (covU Z y)(Y y)` = restriction of the ambient `ZYs := (covM Z ·)(Ys ·)`
   (a `ContMDiffSection` via `cov_smooth_apply_contMDiffAt`); the bracket via
   `mlieBracket_restrictOpen`; then `metricCov_restrictOpen_globalSection` on each
   `∇`.
3. `SmoothRiemannianMetric.restrictOpen_inner` handles the outer metric pairing.

## Gotchas (fixed)

- The final rewrite of the core lemma leaves a defeq residual (the `let`-bound
  `ZYs`/`ZXs` vs their unfolding) — close with a trailing `rfl` (zeta-reduces the
  lets).
- `vec4` rewrites need the basepoint pinned explicitly (`vec4 (x := ↑x) …` on the
  M side, `vec4 (x := x) …` on the U side) — otherwise Lean infers the wrong
  basepoint (`x : U` vs `↑x : M`, both defeq to `E` but syntactically distinct)
  and the rewrite pattern is not found.
- `metricRm04At` is a `def` (semireducible), so `rw` can't see through it to
  `riemannCurvature04At`; unfold with `show metricRm04At … = riemannCurvature04At …
  from rfl` before applying `riemannCurvature04At_apply_smooth`.
- `riemannCurvature04At_apply_smooth` produces `connRiemField cov (fun p => S p) …`
  where `S = restrictOpenTangentSection U Xs`; this is defeq (eta + coercion) to the
  core lemma's `restrictOpenTangentField U (fun p => Xs p)` but NOT syntactic — close
  the last step with `congrArg (g.inner ↑x W ·) (…restrictOpen…)` instead of `rw`.

## Instances

Theorem-level binders `[IsManifold I 1 U] [IsManifold I ((∞:WithTop ℕ∞)+1) U]`
(mirroring `metricRm04Std_pullback`'s pattern for its two manifolds), plus the
usual `[SigmaCompactSpace U] [T2Space U]`. No `NeZero`/`BoundarylessManifold`
needed (the restrict route avoids `mfderiv` pushforward).

## Next (Step C)

`PullbackNaturalityLocal.lean` — `metricRm04StdAt_pullback_localDiffeo`: compose
this germ-locality with the GLOBAL same-model `metricRm04Std_pullback` on a
local-section diffeo between open submanifolds (both over 𝓡3), for the covering
curvature descent.
