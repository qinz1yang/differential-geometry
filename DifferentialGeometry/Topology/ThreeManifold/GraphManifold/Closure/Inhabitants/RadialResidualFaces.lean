import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialHeightLayout

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def radialNewEnd : radialSlims.NewEnd := ⟨⟨⟨(0 : Fin 1), true⟩, trivial⟩, rfl⟩

def radialSharedEnd : radialSlims.End := ⟨⟨(0 : Fin 1), false⟩, trivial⟩

def radialCuspNeighbour : NeighbourFace radialZeros radialCuspCores :=
  .inr ⟨0, ⟨radialCuspCores.internalModelFace 0, rfl⟩⟩

theorem radial_end_height (e : radialSlims.End) : radialSlims.endSet e =
    {p | height p = if e.val.2 then -(1 / 2 : ℝ) else -(1 / 4 : ℝ)} := by
  change slimToCarrier '' range (slimEnd e.val.2) = _
  rw [← range_comp]
  exact slimEnd_map_range e.val.2

theorem radial_new_end_height (e : radialSlims.NewEnd) : radialSlims.endSet e.val =
    {p | height p = -(1 / 2 : ℝ)} := by
  rw [radial_end_height, radialSlim_new_true e]
  rfl

theorem radial_neighbour_unique (F : NeighbourFace radialZeros radialCuspCores) :
    F = radialCuspNeighbour := by
  cases F with
  | inl F => exact Fin.elim0 F.1
  | inr F =>
    obtain ⟨b, face, hface⟩ := F
    have hb : b = (0 : Fin 1) := Subsingleton.elim _ _
    subst b
    subst face
    rfl

theorem radial_shared_false (e : ActualSharedFace radialSlims) : e.val.val.2 = false := by
  have he := e.property
  change (radialSlimKind e.val).isSome at he
  cases hb : e.val.val.2
  · rfl
  · simp [radialSlimKind, hb] at he

theorem radial_shared_removed (e : ActualSharedFace radialSlims) :
    radialSlims.endSet e.val ⊆ relInt (regionM1 radialZeros radialCuspCores)
      radialSlims.union := by
  rw [radial_first_remainder, radial_slim_union, radial_slim_relative,
    radial_end_height, radial_shared_false e]
  intro p hp
  change height p = -(1 / 4 : ℝ) at hp
  change -(1 / 2 : ℝ) < height p ∧ height p ≤ -(1 / 4 : ℝ)
  rw [hp]
  norm_num

def radialResidualFace : radialSlims.ResidualFace := .inr radialNewEnd

theorem radial_residual_height (F : radialSlims.ResidualFace) :
    radialSlims.residualSet F = {p | height p = -(1 / 2 : ℝ)} := by
  cases F with
  | inl F =>
    have hf := radial_neighbour_unique F.val
    have hn := F.property radialSharedEnd
    rw [hf] at hn
    exact (hn rfl).elim
  | inr e => exact radial_new_end_height e

theorem radial_boundary_height : radialSlims.boundaryM2 =
    {p | height p = -(1 / 2 : ℝ)} := by
  unfold SlimPiecesV2.boundaryM2
  ext p
  constructor
  · intro hp
    obtain ⟨F, hF⟩ := mem_iUnion.mp hp
    rw [radial_residual_height] at hF
    exact hF
  · intro hp
    apply mem_iUnion.mpr
    refine ⟨radialResidualFace, ?_⟩
    rw [radial_residual_height]
    exact hp

theorem radial_frontier_boundary : frontier (regionM2 radialSlims) =
    radialSlims.boundaryM2 := by
  rw [radial_M2_frontier, radial_boundary_height]

theorem radial_slim_M2 : radialSlims.union ∩ regionM2 radialSlims =
    ⋃ e : radialSlims.NewEnd, radialSlims.endSet e.val := by
  have he : (⋃ e : radialSlims.NewEnd, radialSlims.endSet e.val) =
      {p | height p = -(1 / 2 : ℝ)} := by
    ext p
    constructor
    · intro hp
      obtain ⟨e, he⟩ := mem_iUnion.mp hp
      rw [radial_new_end_height] at he
      exact he
    · intro hp
      apply mem_iUnion.mpr
      refine ⟨radialNewEnd, ?_⟩
      rw [radial_new_end_height]
      exact hp
  rw [he, radial_slim_union, slimToCarrier_range, radial_M2_height]
  ext p
  constructor
  · intro hp
    exact le_antisymm hp.2 hp.1.1
  · intro hp
    change height p = -(1 / 2 : ℝ) at hp
    change (-(1 / 2 : ℝ) ≤ height p ∧ height p ≤ -(1 / 4 : ℝ)) ∧
      height p ≤ -(1 / 2 : ℝ)
    rw [hp]
    norm_num

theorem radial_shared_eq (e : radialSlims.End)
    (F : NeighbourFace radialZeros radialCuspCores) (he : radialSlims.endKind e = some F) :
    radialSlims.endSet e = neighbourSet F := by
  have hf := radial_neighbour_unique F
  subst F
  have hb : e.val.2 = false := by
    cases h : e.val.2
    · rfl
    · change radialSlimKind e = some radialCuspNeighbour at he
      simp [radialSlimKind, h] at he
  change slimToCarrier '' range (slimEnd e.val.2) =
    cuspPiece.map '' (radialCuspCores.internalModelFace 0).val
  rw [hb]
  exact slim_cusp_shared

theorem radial_horizontal_empty : radialEdgeBundle.horizontalDisks =
    (∅ : Set carrier.Carrier) := by
  unfold EdgeBundle.horizontalDisks
  simp

theorem radial_region_boundary : radialCircleBundle.region ∩ radialSlims.boundaryM2 =
    radialSlims.boundaryM2 \
      relInt radialSlims.boundaryM2 radialEdgeBundle.horizontalDisks := by
  rw [radial_horizontal_empty]
  have hi : relInt radialSlims.boundaryM2 (∅ : Set carrier.Carrier) = ∅ := by
    unfold relInt
    simp
  rw [hi, sdiff_empty, radial_boundary_height, radialCircleBundle_region]
  ext p
  constructor
  · exact And.right
  · intro hp
    change height p = -(1 / 2 : ℝ) at hp
    change (-(3 / 4 : ℝ) ≤ height p ∧ height p ≤ -(1 / 2 : ℝ)) ∧
      height p = -(1 / 2 : ℝ)
    rw [hp]
    norm_num

theorem radial_edge_residual_disjoint (F : radialSlims.ResidualFace) :
    radialEdgeBundle.edgePiece ∩ radialSlims.residualSet F = ∅ := by
  rw [radial_edge_height, radial_residual_height]
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro ⟨he, hf⟩
  linarith

end GC.GraphManifold.Assembly.FC39P0.X135Radial
