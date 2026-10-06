import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepSet
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Orientation
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)
  (hclosed : ∀ i, IsClosed (range (T.cuspMap i))) {b : ℝ} (hb : 2 ≤ b)

/-- The deeper core as a regular sublevel set of the smooth function `deepHeight`. -/
def deepAtlas_CPA2 : SmoothBoundaryAtlas (𝓡 3) 3 (deepSet_CPA2 T b) :=
  SmoothBoundaryAtlas.regularSublevel (𝓡 3) (n := 2) finrank_euclideanSpace_fin
    (contMDiff_deepHeight_CPA2 T hclosed b) 0 (deepHeight_regular_CPA2 T hclosed hb)

instance : SecondCountableTopology H.Carrier :=
  ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) H.Carrier

/-- The deeper core as a compact oriented `3`-manifold with boundary. -/
def deepCarrier_CPA2 : CompactCarrier.{u} :=
  letI : ChartedSpace (EuclideanHalfSpace 3) (deepSet_CPA2 T b) :=
    (deepAtlas_CPA2 T hclosed hb).toChartedSpace
  haveI : IsManifold (𝓡∂ 3) ∞ (deepSet_CPA2 T b) := (deepAtlas_CPA2 T hclosed hb).isManifold
  haveI : CompactSpace (deepSet_CPA2 T b) :=
    isCompact_iff_compactSpace.mp (isCompact_deepSet_CPA2 T (by linarith))
  { kind := .withBoundary
    Carrier := deepSet_CPA2 T b
    orientation := (deepAtlas_CPA2 T hclosed hb).orientation H.orientation }

end GC.LongTime.CuspP1
