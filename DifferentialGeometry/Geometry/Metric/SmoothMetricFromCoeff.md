# SmoothMetricFromCoeff — Brick C-G (metric realization bridge)

**Status (2026-06-12): DONE + verified.** Focused check green; targeted build green
(2685 jobs); `#print axioms smoothMetric_of_localCoeff` clean =
`[propext, Classical.choice, Quot.sound]`. Sorry-free.

## What it delivers

The inverse of the component (Gram) layer:

```
theorem smoothMetric_of_localCoeff
    (gm : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ x v w, gm x v w = gm x w v)
    (hpos  : ∀ x v, v ≠ 0 → 0 < gm x v v)
    (hcoeff : ∀ x₀ : M, ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => gm x (frameVec x₀ i x) (frameVec x₀ j x))
        (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ g : SmoothRiemannianMetric I M, ∀ x v w, g.inner x v w = gm x v w
```

`frameVec x₀ i x := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (Module.finBasis ℝ E i)`
(exported). Dual-consumer: P3 lbl351 (C1b) and Ch4 Thm 3.9 (`metricCompactness`).

## Key finding — `isVonNBounded` is NOT a new analytic input (planner gate resolved)

The blocker analysis (MetricPreconvDiag.md) feared the `gInf` packaging needed a missing
foundational bridge. The actual gap was ONLY the `contMDiff` field. The other four fields are
free:
- `inner`/`symm`/`pos` ← the hypotheses verbatim.
- `isVonNBounded` ← **`MetricExistence.posDef_isVonNBounded` already exists** (positive-definite
  on a finite-dim inner-product space ⇒ coercive ⇒ the sub-`1` ellipsoid is bounded). Reused
  directly: `fun x => posDef_isVonNBounded (E := E) (gm x) (fun v hv => hpos x v hv)`.

So no STOP-and-return was triggered; the brick lands complete.

## Route for the only real field (`contMDiff`)

Per-chart, then assemble `ContMDiff = ∀ x₀, ContMDiffAt` via `ContMDiffOn.contMDiffAt`
(baseSet ∈ 𝓝 x₀). Per-chart `ContMDiffOn` mirrors `MetricExistence.localFiber_contMDiffOn`:
- `Bundle.Trivialization.contMDiffOn_section_iff` reduces the section to its `(0,2)`-tensor
  trivialization coordinate representation (a map into the **constant** model fibre
  `E →L E →L ℝ`).
- `coordSnd_apply` (generic version of `MetricExistence.inCoordinates_localFiber`, reusing
  `oneForm_continuousLinearMapAt`; stops before the localFiber cancellation): the coordinate
  rep evaluated on model vectors is `gm x` applied to the symm-frame vectors, i.e.
  `(triv_hom ⟨x,gm x⟩).2 v w = gm x (symmL x v)(symmL x w)`.
- `clm_eq_sum`: any `φ : E →L E →L ℝ` equals `∑ᵢⱼ φ(eᵢ)(eⱼ) • munit i j`, where
  `munit i j = (coCLM i).smulRight (coCLM j)` is the **constant** matrix-unit form. Hence the
  coordinate rep is a finite sum of (smooth-by-`hcoeff`) scalars times constants ⇒ smooth via
  `contMDiffOn_finset_sum` + `ContMDiffOn.smul contMDiffOn_const`.

## Plan adjustment recorded (cheapest faithful form)

The plan's `frame_u` was abstract. Adjusted to the concrete tangent-trivialization symm-frame
of the model basis `Module.finBasis ℝ E` — the cheapest faithful form because it lets the proof
reuse the `localFiber_contMDiffOn` skeleton verbatim (no moving bilinear frame). This is the
same construction as `ChartGram.chartBasisVecFiber` (which uses `chartModelBasis E`); a consumer
whose components are in a different frame converts by the constant change-of-basis matrix.
(`Module.finBasis` chosen over `chartModelBasis` to avoid importing ChartGram's MeasureTheory
dependencies into this core metric file.)

## Lean gotchas (record for consumers / future edits)

- `metric_contMDiffOn` needs `set_option maxHeartbeats 1000000` +
  `synthInstance.maxHeartbeats 400000` — the `NormedAddCommGroup (E →L E →L ℝ)` synthesis is
  expensive (same as `MetricExistence.localFiber_contMDiffOn`).
- `SmoothRiemannianMetric` lives in `DifferentialGeometry` (Basic.lean), not `…Geometry`; this
  file imports `DifferentialGeometry.Geometry.Metric.Basic` explicitly (MetricExistence does
  NOT, it builds `ContMDiffRiemannianMetric` directly).
- `Basis.coord_apply` is `Module.Basis.coord_apply` in this Mathlib.
- `contMDiffOn_finset_sum` takes the per-term proof directly; the Finset is implicit (NOT
  `contMDiffOn_finset_sum Finset.univ …`).
- `ContMDiffOn.congr (h : ContMDiffOn _ f s) (h₁ : ∀ x∈s, f₁ x = f x)` needs the KNOWN smooth
  `f` fixed: supply it via a named `have hsmooth`, then `hsmooth.congr`; a bare hole for `f`
  spawns an uninferred `M → _` goal.
- `frameVec` is a plain `def`; in the coefficient match, `simp only [frameVec]` before
  `rw [coordSnd_apply]` so the symm-frame forms unify syntactically.

## Consumer interface (for C1b / Thm 3.9)

Supply the pointwise limit form `gm`, its pointwise `symm`/`pos`, and the per-chart
component-smoothness `hcoeff` against `frameVec`. Out comes a `SmoothRiemannianMetric` whose
`inner` is `gm` (by `rfl`). C1b will obtain `hcoeff` from the engine's `MapCInfConvOnCompacts`
limit components; `symm`/`pos` from pointwise limits of symmetric / the eq-3.3 lower bound.
