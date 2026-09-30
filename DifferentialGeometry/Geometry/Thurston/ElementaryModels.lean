import DifferentialGeometry.Geometry.Thurston.ModelAtlas
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SphericalMetric
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Product.Completeness
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.RoundMetricDescent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderMetric

namespace GC.Geometry
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff
set_option autoImplicit false
noncomputable section

abbrev RoundThree := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

def sphericalModelMetric : SmoothRiemannianMetric (𝓡 3) RoundThree := roundMetric

def euclideanModelMetric : SmoothRiemannianMetric (𝓡 3) (EuclideanSpace ℝ (Fin 3)) :=
  DifferentialGeometry.euclideanMetric

def sphericalProductModelMetric : SmoothRiemannianMetric SpatialNeckCylinderModel
    SpatialNeckCylinder := unitCylinderMetric

theorem sphericalProductModelMetric_eq_prod :
    sphericalProductModelMetric =
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).prod
        (DifferentialGeometry.euclideanMetric (E := ℝ)) := by
  symm
  apply unitCylinderMetric_unique
  intro y z v w a b
  exact (SmoothRiemannianMetric.prod_inner
    (I := 𝓡 2) (J := 𝓘(ℝ, ℝ))
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
    (DifferentialGeometry.euclideanMetric (E := ℝ)) (y,z) (v,a) (w,b)).trans (by
    change _ + inner ℝ a b = _ + a * b
    congr 1
    exact mul_comm b a)

theorem sphericalModel_complete : RiemannianMetricComplete sphericalModelMetric :=
  RiemannianMetricComplete.of_compact _

theorem euclideanModel_complete : RiemannianMetricComplete euclideanModelMetric :=
  DifferentialGeometry.euclideanMetric_complete

theorem sphericalProductModel_complete :
    RiemannianMetricComplete sphericalProductModelMetric := by
  rw [sphericalProductModelMetric_eq_prod]
  exact (RiemannianMetricComplete.of_compact _).prod
    DifferentialGeometry.euclideanMetric_complete

theorem fixedModels_have_complete_atlases :
    CompleteModelAtlas sphericalModelMetric sphericalModelMetric ∧
    CompleteModelAtlas euclideanModelMetric euclideanModelMetric ∧
    CompleteModelAtlas sphericalProductModelMetric sphericalProductModelMetric :=
  ⟨⟨sphericalModel_complete, ModelAtlas.refl _⟩,
    ⟨euclideanModel_complete, ModelAtlas.refl _⟩,
    ⟨sphericalProductModel_complete, ModelAtlas.refl _⟩⟩

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [CompactSpace M]

theorem sphericalMetric_complete_model_atlas
    (S : SphericalSpaceFormQuotientModel (𝓡 3) M) :
    CompleteModelAtlas (sphericalMetric S) sphericalModelMetric := by
  refine ⟨sphericalMetric_complete S, ?_⟩
  have hq : ModelAtlas S.quotient.gQuot sphericalModelMetric :=
    S.quotient.exists_partialDiffeomorph_gQuot_inner
  exact hq.pullback S.equiv

end
end GC.Geometry
