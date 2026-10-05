import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialCircleRegion
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0CornersV2

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_CircleRowsX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_CircleRowsX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialCircleBundle : CircleBundle carrier where
  Base := radialCircleBase
  domain := radialCircleDomain
  domain_interior := radialCircleRegion.domain_interior
  proj := radialCircleProjection
  proj_smooth := radialCircleProjection_smooth
  proj_submersion := radialCircleProjection_onto
  neighborhood _ := radialCircleTopBase
  mem_neighborhood _ := mem_univ _
  trivialization _ := radialCircleTrivialization
  projection_trivialization _ _ := rfl
  cbase := radialCircleCornerBase
  cbase_compact := radialCircleCornerBase_compact

theorem radialCircleBundle_region : radialCircleBundle.region =
    {p : carrier.Carrier | -(3 / 4 : ℝ) ≤ height p ∧ height p ≤ -(1 / 2 : ℝ)} :=
  radialCircleRegion_range

def radialCircleRestriction : CircleRestrictionLink radialCircleBundle radialCircleRegion where
  region_eq := rfl
  ι := id
  ι_isOpenEmbedding := Topology.IsOpenEmbedding.id
  ι_smooth := contMDiff_id
  ι_mfderiv c := by
    have hc := ((Diffeomorph.refl (𝓡 2) radialCircleBase ∞).mfderivToContinuousLinearEquiv
      (by simp) (show radialCircleBase from c)).bijective
    exact hc
  domain_eq := by
    ext p
    constructor
    · intro hp
      refine ⟨⟨p, hp⟩, ?_, rfl⟩
      exact ⟨radialCircleProjection ⟨p, hp⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact q.property
  proj_eq x := ⟨x.property, rfl⟩

end GC.GraphManifold.Assembly.FC39P0.X135Radial
