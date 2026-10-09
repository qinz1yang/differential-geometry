import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialEdgeRegistry

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_EdgeLinkX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_EdgeLinkX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialEdgeLayer : EdgeLayer carrier where
  handleCount := 0
  handle i := i.elim0
  edgeCircleCount := 1
  edgeCircle _ := radialEdgeCircle

theorem radialEdgeCircle_proj (q : radialEdgeSet) :
    ∃ hx : edgeToCarrier q ∈ radialEdgeBundle.source,
      radialEdgeBundle.proj ⟨edgeToCarrier q, hx⟩ = radialEdgeProjection q := by
  refine ⟨?_, edgeLongitude_core q⟩
  exact (sub_nonpos.mp q.property).trans_lt (by norm_num : -(3 / 4 : ℝ) < 0)

theorem radialEdgeCircle_disk (c : Circle) :
    edgeToCarrier '' {q | radialEdgeProjection q = c} = radialEdgeBundle.disk c := by
  ext p
  constructor
  · rintro ⟨q, hc, rfl⟩
    obtain ⟨hs, he⟩ := radialEdgeCircle_proj q
    refine ⟨⟨edgeToCarrier q, hs⟩, ⟨he.trans hc, ?_⟩, rfl⟩
    exact sub_nonpos.mp q.property
  · rintro ⟨q, ⟨hc, hh⟩, rfl⟩
    have hq : q.val ∈ range edgeToCarrier := by
      rw [edgeToCarrier_range]
      exact hh
    obtain ⟨r, hr⟩ := hq
    refine ⟨r, ?_, hr⟩
    exact (edgeLongitude_core r).symm.trans ((congrArg edgeLongitude hr).trans hc)

theorem radialEdgeCircle_rim (c : Circle) :
    edgeToCarrier '' {q | radialEdgeProjection q = c ∧ (𝓡∂ 3).IsBoundaryPoint q} =
      radialEdgeBundle.rim c := by
  ext p
  constructor
  · rintro ⟨q, ⟨hc, hb⟩, rfl⟩
    obtain ⟨hs, he⟩ := radialEdgeCircle_proj q
    exact ⟨⟨edgeToCarrier q, hs⟩, ⟨he.trans hc, radialEdge_boundary_iff.mp hb⟩, rfl⟩
  · rintro ⟨q, ⟨hc, hh⟩, rfl⟩
    have hq : q.val ∈ range edgeToCarrier := by
      rw [edgeToCarrier_range]
      exact hh.le
    obtain ⟨r, hr⟩ := hq
    refine ⟨r, ⟨?_, ?_⟩, hr⟩
    · exact (edgeLongitude_core r).symm.trans ((congrArg edgeLongitude hr).trans hc)
    · apply radialEdge_boundary_iff.mpr
      change height (edgeToCarrier r) = -(3 / 4 : ℝ)
      exact (congrArg height hr).trans hh

def radialEdgeComponentsLink :
    EdgeComponentsLink radialEdgeBundle radialEdgeComponentModels radialEdgeLayer where
  handleEquiv := Equiv.refl (Fin 0)
  circleEquiv := Equiv.refl (Fin 1)
  handle_whole i := i.elim0
  circle_whole _ := by rw [radialWholeComponent]; exact edgeToCarrier_range
  handle_proj i := i.elim0
  handle_disk i := i.elim0
  handle_rim i := i.elim0
  circle_proj _ := radialEdgeCircle_proj
  circle_disk _ := radialEdgeCircle_disk
  circle_rim _ := radialEdgeCircle_rim

end GC.GraphManifold.Assembly.FC39P0.X135Radial
