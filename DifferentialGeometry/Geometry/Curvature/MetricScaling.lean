import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

namespace Poincare.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

theorem riemannOp_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (x : M) :
    riemannOp (LeviCivita (I := I) (scaleMetric c hc g)) x =
      riemannOp (LeviCivita (I := I) g) x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have he : LeviCivita (I := I) (scaleMetric c hc g) = LeviCivita (I := I) g :=
    lcConn_scaleMetric c hc g
  simp only [he]

theorem ricciTensor_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (x : M) :
    ricciTensor (scaleMetric c hc g) x = ricciTensor g x := by
  ext v w
  rw [ricciTensor_apply, ricciTensor_apply]
  congr 1
  ext z
  rw [ricciEndo_apply, ricciEndo_apply, riemannOp_scaleMetric]

end Poincare.Geometry.Curvature
