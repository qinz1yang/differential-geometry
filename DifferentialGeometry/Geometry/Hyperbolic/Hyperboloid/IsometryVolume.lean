import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Volume
import DifferentialGeometry.Geometry.Metric.Isometry.Topology

open MeasureTheory
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)
open scoped Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private local instance : MeasurableSpace (Hyperboloid E) := borel (Hyperboloid E)
private local instance : BorelSpace (Hyperboloid E) := ⟨rfl⟩

theorem measurePreserving_isometryEquiv (e : Hyperboloid E ≃ᵢ Hyperboloid E) :
    MeasurePreserving e
      (riemannianVolumeMeasure 𝓘(ℝ, E) (Hyperboloid E) riemannianMetric)
      (riemannianVolumeMeasure 𝓘(ℝ, E) (Hyperboloid E) riemannianMetric) := by
  let D := isometryDiffeomorph e (n := ∞)
  have hmetric : ∀ z : Hyperboloid E, ∀ u v : TangentSpace 𝓘(ℝ, E) z,
      riemannianMetric.inner z u v = riemannianMetric.inner (D z)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) D z u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) D z v) := by
    intro z u v
    exact (riemannianMetric_inner_mfderiv_isometryEquiv e z u v).symm
  have hmap := Geometry.Measure.riemannianVolumeMeasure_map_of_injective_local_isometry
    riemannianMetric riemannianMetric D D.isLocalDiffeomorph D.injective hmetric
  refine ⟨e.continuous.measurable, ?_⟩
  change Measure.map e (riemannianVolumeMeasure 𝓘(ℝ, E) (Hyperboloid E) riemannianMetric) =
    (riemannianVolumeMeasure 𝓘(ℝ, E) (Hyperboloid E) riemannianMetric).restrict
      (Set.range e) at hmap
  rw [Set.range_eq_univ.mpr e.surjective, Measure.restrict_univ] at hmap
  exact hmap

end DifferentialGeometry.Hyperboloid
