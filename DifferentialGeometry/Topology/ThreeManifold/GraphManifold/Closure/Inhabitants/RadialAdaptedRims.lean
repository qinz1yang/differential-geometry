import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialSafeNeighbourhoods

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def radialRims : RimChartLayer carrier radialEdgeLayer radialCircleRegion where
  handleCorner h := Fin.elim0 h
  handleCorner_bijective := by
    constructor
    · intro a
      exact Fin.elim0 a.1
    · intro k
      exact Fin.elim0 k
  rimChart h := Fin.elim0 h
  rim_source h := Fin.elim0 h
  rim_proj h := Fin.elim0 h
  rim_label h := Fin.elim0 h
  rim_disjoint h := Fin.elim0 h

def radialGlobalFaceLink : GlobalFaceLinkV2 radialPrepared.globalFaces radialCircleRegion
    radialCircleRestriction where
  range_subset := fun _ _ => mem_univ _
  faceIndex := Equiv.refl (Fin 2)
  defining_eq _ _ := rfl

def radialLabelledCompatibility : LabelledCornerCompatibilityV2 radialPrepared radialEdgeLayer
    radialCircleRegion radialRims where
  edgeLink := radialEdgeComponentsLink
  circleLink := radialCircleRestriction
  globalFaces := radialGlobalFaceLink
  endOfCorner := by
    change Fin 0 ≃ radialRows.edge.EdgeEnd
    exact Equiv.equivOfIsEmpty _ _
  corner_center k := Fin.elim0 k
  endpoint_label h := Fin.elim0 h
  first_label h := Fin.elim0 h
  second_label h := Fin.elim0 h
  height_eq h := Fin.elim0 h
  horizontal_eq h := Fin.elim0 h
  target_full h := Fin.elim0 h
  target_in_raw_tube h := Fin.elim0 h

theorem radial_rim_product : ∀ h b,
    RimProductAt (radialRims.rimChart h b) (radialEdgeLayer.handle h) b :=
  fun h => Fin.elim0 h

def radialAdapted : AdaptedEdgeRimDataV2 radialPrepared radialSafe where
  edges := radialEdgeLayer
  circ := radialCircleRegion
  components := radialEdgeComponentsLink
  circle := radialCircleRestriction
  rims := radialRims
  labelled := radialLabelledCompatibility
  components_eq := rfl
  circle_eq := rfl
  product := radial_rim_product
  rim_closure_in_safe h := Fin.elim0 h
  rounding_in_safe := by
    change Subtype.val '' (radialCircleProjection ⁻¹'
      symmDiff {b | radialCircleRounding b ≤ 0} radialCircleCornerBase) ⊆ _
    rw [radialCircleRounding_sublevel]
    simp

end GC.GraphManifold.Assembly.FC39P0.X135Radial
