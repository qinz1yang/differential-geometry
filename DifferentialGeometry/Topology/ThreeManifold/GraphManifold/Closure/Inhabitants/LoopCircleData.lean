import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopSublevelExact

/-!
The actual first-Clifford circle region has its genuine compact cornered base and common rounding.
Its full global defining family and both original rim corners give the native CircleRegion datum.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem regionData_boolPairwise : Pairwise fun b b' : Bool =>
    Disjoint (loopBaseCorner b).target (loopBaseCorner b').target := by
  intro b b' h
  cases b <;> cases b'
  · exact False.elim (h rfl)
  · exact loopBaseCorner_disjoint
  · exact loopBaseCorner_disjoint.symm
  · exact False.elim (h rfl)

private theorem regionData_unitUnion :
    (⋃ k : Fin 2, loopBaseCorner (finTwoEquiv k) '' rimBox 1) =
    ⋃ b : Bool, loopBaseCorner b '' rimBox 1 := by
  ext z
  constructor
  · intro hz
    obtain ⟨k,hk⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨finTwoEquiv k,hk⟩
  · intro hz
    obtain ⟨b,hb⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨finTwoEquiv.symm b,by simpa using hb⟩

def loopCircleRegionData : CircleRegion (NoCuts.carrier standardThreeSphereLift.{0}) where
  Base := loopCircleBase
  domain := loopCircleDomain
  domain_interior := by intro p hp; exact BoundarylessManifold.isInteriorPoint
  proj := loopCircleProjection
  proj_smooth := loopCircleProjection_smooth
  proj_submersion := loopCircleProjection_submersion
  neighborhood := fun _ => ⊤
  mem_neighborhood := fun b => Set.mem_univ b
  trivialization := fun _ => loopCircleTrivialization
  projection_trivialization := fun _ p => loopCircleTrivialization_proj p
  definingCount := 3
  defining := loopDefining
  defining_smooth := loopDefining_smooth
  defining_regular := loopDefining_regular
  depth_le_two := loopDefining_depth
  defining_independent := loopDefining_independent
  cornerBase := loopCircleCornerBase
  cornerBase_eq := Set.ext (fun z => loopCircleCornerBase_sublevel (z := z))
  cornerBase_compact := loopCircleCornerBase_compact
  cornerCount := 2
  cornerChart := fun k => loopBaseCorner (finTwoEquiv k)
  cornerChart_source := fun k => loopBaseCorner_source (finTwoEquiv k)
  cornerChart_disjoint := by
    intro k k' h
    exact regionData_boolPairwise (finTwoEquiv.injective.ne h)
  cornerFirst := fun _ => 0
  cornerSecond := fun _ => 1
  corner_ne := fun _ => by decide
  cornerScale := fun _ => 1
  cornerScale_pos := fun _ => by norm_num
  chart_first := by
    intro k v hv
    simpa using loopDefining_chart_first (finTwoEquiv k) hv
  chart_second := by
    intro k v hv
    simpa using loopDefining_chart_second (finTwoEquiv k) hv
  chart_other := by
    intro k l v hl0 hl1 hv
    exact loopDefining_chart_other (finTwoEquiv k) l hl0 hl1 hv
  corner_center := by
    intro z l l' hne hl hl'
    obtain ⟨b,hb⟩ := loopDefining_corner_center z l l' hne hl hl'
    exact ⟨finTwoEquiv.symm b,by simpa using hb⟩
  rounding := loopCircleBaseRounding
  rounding_smooth := loopCircleBaseRounding_smooth
  rounding_regular := loopCircleBaseRounding_regular
  rounding_chart := by
    intro k v hv
    simpa using loopCircleBaseRounding_corner (finTwoEquiv k) v hv
  rounding_agree := by
    rw [regionData_unitUnion]
    exact loopCircleCornerBase_rounding_agree
  rounded_compact := loopCircleBaseRounding_compact

theorem loopCircleRegionData_region : loopCircleRegionData.region = loopCircleRegion := rfl

theorem loopCircleRegionData_rounded : loopCircleRegionData.rounded = loopRoundedShell :=
  loopCircleLift_rounded

end GC.GraphManifold.Assembly
