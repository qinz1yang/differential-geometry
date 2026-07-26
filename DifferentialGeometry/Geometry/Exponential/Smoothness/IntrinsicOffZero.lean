import DifferentialGeometry.Geometry.Exponential.IntrinsicVelocity

set_option linter.unusedSectionVars false

/-!
# Chart-composed regularity of the intrinsic exponential map

**L1 of the A0′ `VolumeComparisonInput` lane** (`HCGCompactness/C4/A0PRIME_VOLUME_PLAN.md`).

The velocity-regularity of the intrinsic exponential map is **already in the tree,
sorry-free and global**: `intrinsicFiber_smooth`
(`Exponential/IntrinsicVelocity.lean`) gives

  `ContMDiff 𝓘(ℝ, E) I ∞ (fun v : E ↦ expMapIntrinsic g hEnorm p v)`

at *every* `v` (including large `v` whose geodesic crosses chart boundaries — the
map is built from the geodesic spray `geodesicVectorField` and the compact-
trajectory flow `flow_slice_smooth` on `TangentBundle I M`, not from a single
chart).  So the "off-zero, large-`v`" regularity the lane flagged as a frontier is
NOT open — it is a direct consequence of `intrinsicFiber_smooth`.  (The plan's
`A0PRIME_AREA_CONSULT.md` and the B5-pre scout both missed this producer.)

This file records the **downstream-consumable form**: `expMapIntrinsic p`, written
in a chart at its target and read as a Euclidean map `E → E`, is `C^∞` — the
regularity the area-formula (`MeasureTheory.image_lintegral_le`) and the density
identity (`SegmentDensity.lean`) actually consume.

## Main result

* `expChart_contDiffAt` — for `y₀ : M` with `expMapIntrinsic p v` in the chart
  domain of `y₀`, `ContDiffAt ℝ ∞ (fun b : E ↦ extChartAt I y₀ (expMapIntrinsic p b)) v`.
  Its `.differentiableAt.hasFDerivAt` is the Euclidean derivative whose determinant
  enters the area formula.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The intrinsic exponential map is `C^∞` in a chart at its target.**

For a base point `p`, a launch vector `v`, and any chart center `y₀` whose chart
domain contains `expMapIntrinsic p v`, the Euclidean map
`b ↦ extChartAt I y₀ (expMapIntrinsic p b)` is `ContDiffAt ℝ ∞` at `v`.

Immediate from the global smoothness `intrinsicFiber_smooth` composed with the
`C^∞` chart `extChartAt I y₀` (valid at the target), then read as a map between
model spaces via `contMDiffAt_iff_contDiffAt`.  No `v ≠ 0` or radius hypothesis:
`intrinsicFiber_smooth` is unconditional in the velocity. -/
theorem expChart_contDiffAt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : E) (y₀ : M)
    (hy : expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v)
      ∈ (chartAt H y₀).source) :
    ContDiffAt ℝ ∞
      (fun b : E => extChartAt I y₀
        (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from b))) v := by
  -- Global smoothness of the intrinsic exponential in the velocity.
  have hexp : ContMDiffAt 𝓘(ℝ, E) I ∞
      (fun b : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from b)) v :=
    (intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffAt
  -- The chart at `y₀` is `C^∞` at the target point.
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I y₀)
      (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v)) :=
    (contMDiffOn_extChartAt (I := I) (n := ∞) (x := y₀)).contMDiffAt
      ((chartAt H y₀).open_source.mem_nhds hy)
  -- Compose and read as a Euclidean map.
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun b : E => extChartAt I y₀
        (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from b))) v :=
    hchart.comp v hexp
  exact contMDiffAt_iff_contDiffAt.mp hcomp

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
