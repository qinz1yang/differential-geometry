# NeckArmNoReturn

Label: `eq:scn-neck-no-return-inequality` (`master05b.tex`, inside the proof of
`lem:scn-good-point-buffered-canonical`). New leaf, Chapter25 worker W2; not yet registered in
`DifferentialGeometry.lean` (reviewer's job).

## Proof mechanism

The book chooses far transverse slices `S_{-L}`, `S_L` with
`2 min{d(S_0,S_{-L}), d(S_0,S_L)} > diam_intr(S_0)` and argues with the last `S_0`-crossing
before the far slice and the first one afterwards. Here the arm starts **at** the neck centre,
which already lies on `S_0` (`StrongNeck.center_eq`), so that last crossing can be taken to be
the initial point and the whole argument becomes two competing distance bounds in the rescaled
metric `rescaledMetric S t (S.scalar t x) neck.Q_pos 0`:

* upper: two points of the central sphere are at rescaled distance at most a universal `Dc`
  (`exists_uniform_transverse_shortcuts` with `z = 0`, then `edistOf_le_metricPathELength`);
* lower: a point at axial height `|l| > R` is at rescaled distance at least `R/2` from the
  centre (`collar_ball_subset_image`, i.e. the actual first-exit capture, plus injectivity of
  `neck.map` on `neck.map.source` via `left_inv'` to see the point is outside the captured
  slab image).

`MinimizingArm` records `metricDistance g (point s) (point t) = |s - t|`, so the arm parameter
*is* the distance to the start; `MinimizingArm.edistOf_start` upgrades that to the exact
`ENNReal` identity `riemannianEDistOf g x (a.point s) = ENNReal.ofReal s` (the `⊤` branch is
excluded because it would force `s = 0`, where the distance is `0`). With
`edistOf_rescaledMetric_zero` (`edistOf_scale` plus `paraTime_zero`) both bounds become real
inequalities `sqrt Q * w ≤ Dc` and `Dc + 1 ≤ sqrt Q * s₀`, and `s₀ ≤ w` closes it.

Depth: `2*Dc + 2` in the parametrised theorem, `H₀ := 2*Dc + 3` in the fixed-constant form.

## Real dependencies

`CylinderBallCapture.collar_ball_subset_image`, `CollarMetricControl.exists_uniform_transverse_shortcuts`,
`DistanceHessianLocal.edistOf_le_metricPathELength`, `DistanceScaling.edistOf_scale`,
`ModelWitness.rescaledMetric` / `riemannianBallOf`, `Scaling/Parabolic.paraTime_zero`,
`Chapter25Geometry.StrongNeck`, `Chapter25Extension.MinimizingArm`. Imports are
`CylinderBallCapture` and `Chapter25Extension` only. Nothing from the `sorry`-bearing
producers of `Chapter25Extension` is used.

## Pitfalls found

* No regularity of the arm is needed: `collar_return_length_lower` (which wants a `C¹`
  contained cylinder curve) is **not** on this route, and neither is any trapping statement
  about the arm itself. Only the two endpoint distances matter. This is what makes the result
  usable for the merely continuous `MinimizingArm`.
* `univ ×ˢ Icc (-R) R` inside a `have` needs `(univ : Set (Sphere 2))`: with no surrounding
  constraint the sphere factor's type is not determined.
* `StrongNeck.le_edistOf_of_height` has `q : Sphere 2` implicit and occurring only in the
  conclusion, so callers must pass `(q := q)`.
* `z.2 ∈ ({0} : Set ℝ)` is not an `Eq` for dot-notation purposes; re-ascribe it
  (`have hz2 : z.2 = 0 := hz.2`) before `Prod.ext rfl hz2.symm`.
* `metricDistance` is `(riemannianEDistOf ...).toReal`, so it silently truncates `⊤`; the
  finiteness step in `MinimizingArm.edistOf_start` is genuinely needed, not cosmetic.

## Verification

`LEAN_NUM_THREADS=2 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/NeckArmNoReturn.lean`
— exit 0, empty output, 22.99 s (2026-09-11). Repeated with the lakefile's own options
(`-DautoImplicit=false -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true
-Dlinter.style.header=false -Dlinter.style.longLine=false`): empty output, 22.64 s. A control
copy outside the tree with one unused hypothesis produced the expected `unusedVariables` and
`linter.style.whitespace` warnings plus a type error, confirming the run really elaborates and
the mathlib standard linter set is active. No `sorry`/`nolint`/`maxHeartbeats`/`maxRecDepth`/
`skipKernelTC`/`set_option backward.*`.

Endpoint axiom audit still owed (needs the built artifact). Public declarations to audit:
`rescaledMetric_zero`, `edistOf_rescaledMetric_zero`, `MinimizingArm.edistOf_start`,
`exists_fixed_neck_central_diameter`, `StrongNeck.le_edistOf_of_height`,
`MinimizingArm.not_mem_centralSphere_of_far`, `exists_fixed_neck_arm_no_return_depth`,
`exists_fixed_neck_two_arm_no_return_depth` — all in namespace
`DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.Chapter25`.

## Next step

`good_point_buffered_canonical` still needs the *other* halves of its conclusion (the buffered
`2*alpha`-neck at `x`, the opposite-sign axial heights of the two exiting arms, the transverse
path and its `±1` algebraic intersection, and the neck diameter bound). This leaf supplies
exactly the two `∀ w ∈ Icc s a.length, a.point w ∉ …` clauses once those heights are produced.
Upstream candidates: `rescaledMetric_zero` and `edistOf_rescaledMetric_zero` belong next to
`rescaledMetric` in `ModelWitness.lean`; `MinimizingArm.edistOf_start` belongs next to
`MinimizingArm` once `Chapter25Extension` stops being a skeleton module.
