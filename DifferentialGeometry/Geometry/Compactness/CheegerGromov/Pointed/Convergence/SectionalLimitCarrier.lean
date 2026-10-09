import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.SectionalLimitReturn
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier

set_option autoImplicit false

noncomputable section

namespace GC.Endpoint

open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open Filter
open scoped Manifold ContDiff _root_.Topology

universe u

theorem CompactCarrier.exists_smooth_sectional_nonneg_of_interior_limit
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (hclosed : W.model.boundary W.Carrier = ∅) :
    letI := ModelWithCorners.Boundaryless.of_boundary_eq_empty hclosed
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.Carrier)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.Carrier)
    ∀ (p : W.Carrier)
      (gSeq : ℕ → SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.Carrier),
      SeqMetricComplete (pointedMetricSeq p gSeq) →
      SeqBoundedGeometry (pointedMetricSeq p gSeq) →
      BaseInjBound (pointedMetricSeq p gSeq) →
      ∀ D : ℝ, (∀ n (x y : W.Carrier), riemannianEDistOf (gSeq n) x y ≤ ENNReal.ofReal D) →
      ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ n, SectionalBoundedBelow (gSeq n) (-ε n)) →
      ∃ h : SmoothRiemannianMetric W.model W.Carrier, SectionalBoundedBelow h 0 := by
  let := ModelWithCorners.Boundaryless.of_boundary_eq_empty hclosed
  let := Manifold.interiorChartedSpace W.model ∞ (M := W.Carrier)
  let := Manifold.interiorIsManifold W.model ∞ (M := W.Carrier)
  intro p gSeq hcomplete hgeom hinj D hdiam ε hεlim hsec
  exact exists_sectional_nonneg_of_bounded_geometry_limit_of_diffeomorph
    (Manifold.interiorAtlasDiffeomorph W.model ∞ (M := W.Carrier)) p gSeq hcomplete hgeom hinj
    D hdiam ε hεlim hsec

end GC.Endpoint

end
