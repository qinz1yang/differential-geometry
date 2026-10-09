import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ImmersionInducedMetric
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

private local instance spatialNeckMetricSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance spatialNeckMetricC1 : IsManifold I 1 N :=
  IsManifold.of_le (I := I) (M := N) (n := ∞) (by decide)

def spatialNeckNormalizedMetric (h : SmoothRiemannianMetric I N) (p : N)
    (hscalar : 0 < metricScalarAt (I := I) h p) {epsilon : ℝ}
    {Phi : C(spatialNeckBuffer epsilon, N)}
    (hPhi : IsSmoothEmbedding SpatialNeckCylinderModel I ∞ Phi) :
    SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer epsilon) :=
  scaleMetric ((spatialNeckScale h p) ^ 2)⁻¹
    (inv_pos.mpr (pow_pos (spatialNeckScale_pos h p hscalar) 2))
    (immersionInducedMetric h hPhi.isImmersion)

omit [T2Space N] [SigmaCompactSpace N] in
theorem spatialNeckNormalizedMetric_inner (h : SmoothRiemannianMetric I N) (p : N)
    (hscalar : 0 < metricScalarAt (I := I) h p) {epsilon : ℝ}
    {Phi : C(spatialNeckBuffer epsilon, N)}
    (hPhi : IsSmoothEmbedding SpatialNeckCylinderModel I ∞ Phi)
    (x : spatialNeckBuffer epsilon) (V W : TangentSpace SpatialNeckCylinderModel x) :
    (spatialNeckNormalizedMetric h p hscalar hPhi).inner x V W =
      ((spatialNeckScale h p) ^ 2)⁻¹ * h.inner (Phi x)
        (mfderiv SpatialNeckCylinderModel I Phi x V)
        (mfderiv SpatialNeckCylinderModel I Phi x W) := by
  rw [spatialNeckNormalizedMetric, scaleMetric_inner, immersionInducedMetric_inner]

theorem SpatialNeckWitness.normalizedMetric_eq_canonical
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon) :
    W.normalizedMetric =
      spatialNeckNormalizedMetric h p W.scalar_pos W.smooth_embedding :=
  (W.normalizedMetric_unique _
    (spatialNeckNormalizedMetric_inner h p W.scalar_pos W.smooth_embedding)).symm

def SpatialNeckWitness.ofEmbedding (h : SmoothRiemannianMetric I N)
    (yStar : SpatialNeckSphere) (p : N) (epsilon : ℝ)
    (hdimension : Module.finrank ℝ E = 3)
    (hcomplete : RiemannianMetricComplete (I := I) h)
    (hepsilon : 0 < epsilon) (hscalar : 0 < metricScalarAt (I := I) h p)
    (Phi : C(spatialNeckBuffer epsilon, N))
    (hPhi : IsSmoothEmbedding SpatialNeckCylinderModel I ∞ Phi)
    (hmarked : Phi (spatialNeckCentralPoint epsilon hepsilon yStar) = p)
    (hclose : metricDerivNormSupOn (I := SpatialNeckCylinderModel)
      (spatialNeckClosedCore epsilon) (Nat.ceil epsilon⁻¹)
      (spatialNeckNormalizedMetric h p hscalar hPhi)
      (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon))
      (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)) < epsilon) :
    SpatialNeckWitness h yStar p epsilon where
  dimension_three := hdimension
  complete := hcomplete
  epsilon_pos := hepsilon
  scalar_pos := hscalar
  embedding := Phi
  smooth_embedding := hPhi
  marked := hmarked
  normalizedMetric := spatialNeckNormalizedMetric h p hscalar hPhi
  normalized_inner := spatialNeckNormalizedMetric_inner h p hscalar hPhi
  closeness := hclose

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
