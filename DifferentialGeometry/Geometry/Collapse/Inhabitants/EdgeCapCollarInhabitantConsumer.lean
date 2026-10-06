import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapCollarInhabitant

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set Metric
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open DifferentialGeometry.Geometry.Collapse.EdgeCapCylindrical
open DifferentialGeometry.Geometry.Collapse.EdgeCapDistance
open DifferentialGeometry.Geometry.Collapse.EdgeCapGeodesic
open DifferentialGeometry.Geometry.Collapse.EdgeCapHeight
open DifferentialGeometry.Geometry.Collapse.EdgeCapPlane
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapRadial
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapRankOne
open DifferentialGeometry
open DifferentialGeometry.Analysis
open GC.MetricGeometry
open scoped Manifold ContDiff Topology InnerProductSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] capExampleSigma capExampleMetricSpace capExampleEDist
  capExampleDist capExampleUniform capExampleEMetric capExamplePseudo capExampleBundle
  capExampleRiemannian capExampleContinuous capExampleComplete capExampleProper capExampleDimension

open DifferentialGeometry.Geometry.Collapse.EdgeCapCollarInhabitant

namespace DifferentialGeometry.Geometry.Collapse.EdgeCapCollarInhabitantConsumer

/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceMetricSpace : MetricSpace E2 :=
  EdgeCapSplitting.capSurfaceMetricSpace
local instance capProductSurfaceSigma : SigmaCompactSpace E2 := by infer_instance
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceEDist : EDist E2 := EdgeCapSplitting.capSurfaceEDist
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceDist : Dist E2 := EdgeCapSplitting.capSurfaceDist
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceUniform : UniformSpace E2 :=
  EdgeCapSplitting.capSurfaceUniform
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceEMetric : PseudoEMetricSpace E2 :=
  EdgeCapSplitting.capSurfaceEMetric
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfacePseudo : PseudoMetricSpace E2 :=
  EdgeCapSplitting.capSurfacePseudo
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceBundle :
    RiemannianBundle (TangentSpace (𝓡 2) : E2 → Type _) :=
  ⟨(scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).toRiemannianMetric⟩
local instance capProductSurfaceRiemannian : IsRiemannianManifold (𝓡 2) E2 :=
  inducedMetricSpace_isRiemannianManifold
    (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
local instance capProductSurfaceComplete : CompleteSpace E2 :=
  (scaledCapComplete capExampleEpsilon capExampleEpsilon_pos).complete

/-- Consumes packet coverage and product slab clauses under shared hypotheses. -/
theorem capExampleClosedSlabConsumer (y : E3)
    (hy : y ∈ ball capExampleEdgeChart.center (100 * capExampleDelta))
    (hc : |capExampleEdgeChart.coord y| ≤ 4 * capExampleDelta)
    (hH : edgeRowHeight capExampleDelta capExampleF (fun _ => 1) y ≤
      4 * capExampleDelta) :
    y ∈ (capExampleEdgeDiskPacket.slabOpen : Set E3) ∧
      (∃ s : ℝ × E2, |s.1| < 5 * capExampleDelta ∧
        dist s.2 (0 : E2) < 5 * capExampleDelta ∧
        capProductTheta s ∈ capProductEmbedding.source ∧
        capProductEmbedding (capProductTheta s) = y) := by
  constructor
  · exact capExampleEdgeDiskPacket.slab_subset y hy hc hH
  · exact capExampleEdgeProductModel.slab y hy hc hH


end DifferentialGeometry.Geometry.Collapse.EdgeCapCollarInhabitantConsumer
