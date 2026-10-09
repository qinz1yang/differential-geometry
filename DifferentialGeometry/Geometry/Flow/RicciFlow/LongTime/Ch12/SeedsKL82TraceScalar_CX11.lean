import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82PointSelection_CX11

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff
namespace GC.LongTime.Ch12
universe u

/-- The upper bound needed for bounded point selection follows from the original
strong unscathed-family input. `K` may have either sign, since the input uses `K²`. -/
theorem scalar_abs_le_of_bounded_trace_CX11
    (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
    {q : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {K : ℝ} (hA : A.isRmBoundedBy (hat := hat) K) :
    |metricScalarAt (H.stageMetric (H.activeStage t) t) q| ≤ 9 * |K| := by
  have hbound := hA.1 t hat le_rfl
  rw [A.endpoint_eq] at hbound
  have hroot := Real.sqrt_le_sqrt hbound
  rw [Real.sqrt_sq_eq_abs] at hroot
  have hh := scalar_abs_le_rm (H.stageMetric (H.activeStage t) t) q
  change |metricScalarAt (H.stageMetric (H.activeStage t) t) q| ≤
    (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * _ at hh
  norm_num [ThreeSpace] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hroot (by norm_num))

/-- In particular, each bad spacetime set used in (45.5) has a finite scalar
upper bound. There is no unproved maximum-attainment assumption in the selection. -/
theorem scalar_bddAbove_of_trace_family_CX11
    (H : ObservedHistory.{u}) (a t : Icc (0 : ℝ) H.horizon) {K : ℝ}
    (W : Set ((v : Icc (0 : ℝ) H.horizon) × (H.stageAt v).Carrier))
    (hW : ∀ z ∈ W, ∃ (hav : a ≤ z.1), z.1 ≤ t ∧
      ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage z.1)
        (H.activeStage_mono hav) z.2, A.isRmBoundedBy (hat := hav) K) :
    BddAbove ((fun z => metricScalarAt (H.stageMetric (H.activeStage z.1) z.1) z.2) '' W) := by
  refine ⟨9 * |K|, ?_⟩
  rintro R ⟨z, hz, rfl⟩
  obtain ⟨hav, _, A, hA⟩ := hW z hz
  exact (le_abs_self _).trans (scalar_abs_le_of_bounded_trace_CX11 H (hat := hav) A hA)

end GC.LongTime.Ch12
