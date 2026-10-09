import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SingletonBase
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateApplications

/-!
The X136 closed-zero singleton on the actual standard round three-sphere. Its auxiliary metric
and complete carrier coverage are geometric data, not assumed certificate conclusions.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

local instance sphereDimension : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

def zeroW : CompactCarrier.{0} := NoCuts.carrier standardThreeSphere

def zeroMetric : SmoothRiemannianMetric (𝓡 3) standardThreeSphere.Carrier :=
  Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)

theorem zeroMetric_nonneg : Geometry.Riemannian.SectionalBoundedBelow zeroMetric 0 := by
  change Geometry.Riemannian.SectionalBoundedBelow
    (Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) 0
  intro x v w
  change 0 * (Geometry.roundMetric.inner x v v * Geometry.roundMetric.inner x w w -
    Geometry.roundMetric.inner x v w ^ 2) ≤
      Geometry.Curvature.metricRm04StandardAt Geometry.roundMetric x v w w v
  rw [zero_mul, Geometry.roundMetric_sec_value]
  exact sub_nonneg.mpr (by
    simpa only [pow_two] using
      SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq Geometry.roundMetric x v w)

def zeroClosedPiece : ClosedZeroPiece zeroW where
  piece := wholePiece standardThreeSphere
  boundary_empty := wholePiece_boundary standardThreeSphere
  Q := standardThreeSphere
  metric := zeroMetric
  nonneg := zeroMetric_nonneg
  ident := wholeDiffeomorph standardThreeSphere

theorem zeroClosedPiece_cover : range zeroClosedPiece.piece.map = univ :=
  wholePiece_range standardThreeSphere

def zeroClosedSeed : ClosedDecompositionCertificate zeroW :=
  closedCertificateOfClosedZeroPiece zeroClosedPiece zeroClosedPiece_cover

end GC.GraphManifold.Assembly.FC39P0.X136
