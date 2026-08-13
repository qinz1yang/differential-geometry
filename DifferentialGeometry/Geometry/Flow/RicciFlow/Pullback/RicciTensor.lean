import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Metric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.LeviCivita
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.RicciTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.MLieBracket
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

theorem ricci_tensor_pullback_natural_under_diffeomorphism
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (Diffeomorph.pullbackMetric g Φ) x v w
      = ricciTensor (I := I) g (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) :=
  ricciTensor_pullback_conjugation (I := I) g Φ x v w

end DifferentialGeometry.PDE.RicciFlow.Pullback
