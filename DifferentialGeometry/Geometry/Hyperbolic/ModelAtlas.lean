import DifferentialGeometry.Geometry.Hyperbolic.Rigidity
import DifferentialGeometry.Geometry.Thurston.Transport
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

set_option autoImplicit false
noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
theorem has_hyperbolic_atlas_of_curvature_neg_one
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (hcurvature : hasConstantSectionalCurvature g (-1)) :
    GC.Geometry.HasThurstonAtlas g .hyperbolic := by
  sorry

def hyperbolicGeometricStructure
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (hcurvature : hasConstantSectionalCurvature g (-(1 / 4 : ℝ)))
    (hcomplete : RiemannianMetricComplete g)
    (hvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤) :
    GC.Geometry.GeometricStructure (𝓡 3) M where
  model := .hyperbolic
  metric := scaleMetric (1 / 4 : ℝ) (by norm_num) g
  complete := hcomplete.scaleMetric _ (by norm_num)
  atlas := by
    apply has_hyperbolic_atlas_of_curvature_neg_one
    intro p v w hvw
    rw [Geometry.Riemannian.sectionalCurvature_scaleMetric, hcurvature p v w hvw]
    norm_num
  hyperbolic_finite_volume := by
    intro _
    rw [Integral.Measure.volume_scale_apply]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hvolume

@[simp] theorem hyperbolicGeometricStructure_model
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (hcurvature : hasConstantSectionalCurvature g (-(1 / 4 : ℝ)))
    (hcomplete : RiemannianMetricComplete g)
    (hvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤) :
    (hyperbolicGeometricStructure g hcurvature hcomplete hvolume).model = .hyperbolic := rfl

end DifferentialGeometry.Geometry.Hyperbolic
