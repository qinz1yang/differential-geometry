import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusSlimCores
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialCircleRows
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialHeightRelative

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

theorem radial_cusp_interior :
    interior (range cuspToCarrier) = {p | -(1 / 4 : ℝ) < height p} := by
  rw [cuspToCarrier_range]
  exact height_interior_ge _ (by norm_num) (by norm_num)

theorem radial_slim_interior :
    interior (range slimToCarrier) =
      {p | -(1 / 2 : ℝ) < height p ∧ height p < -(1 / 4 : ℝ)} := by
  rw [slimToCarrier_range]
  exact height_interior_band _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem radial_slim_relative :
    relInt {p : carrier.Carrier | height p ≤ -(1 / 4 : ℝ)} (range slimToCarrier) =
      {p | -(1 / 2 : ℝ) < height p ∧ height p ≤ -(1 / 4 : ℝ)} := by
  rw [slimToCarrier_range]
  exact height_relInt_band _ _ (by norm_num) (by norm_num) (by norm_num)

theorem radial_second_remainder :
    {p : carrier.Carrier | height p ≤ -(1 / 4 : ℝ)} \
      relInt {p : carrier.Carrier | height p ≤ -(1 / 4 : ℝ)} (range slimToCarrier) =
        {p | height p ≤ -(1 / 2 : ℝ)} := by
  rw [radial_slim_relative]
  ext p
  simp only [mem_sdiff, mem_ofPred_eq]
  constructor
  · rintro ⟨hu, hn⟩
    by_contra! hs
    exact hn ⟨hs, hu⟩
  · intro hs
    constructor
    · linarith
    · rintro ⟨h, _⟩
      linarith

theorem radial_first_remainder :
    regionM1 radialZeros radialCuspCores =
      {p : carrier.Carrier | height p ≤ -(1 / 4 : ℝ)} := by
  have hz : (⋃ i, range (radialZeros.piece i).map) = (∅ : Set carrier.Carrier) := by
    ext p
    simp only [mem_iUnion, mem_range, mem_empty_iff_false, iff_false]
    rintro ⟨i, _, _⟩
    exact Fin.elim0 i
  have hc : (⋃ b, range (radialCuspCores.piece b).map) = range cuspToCarrier := by
    ext p
    constructor
    · intro hp
      obtain ⟨b, hb⟩ := mem_iUnion.mp hp
      exact hb
    · intro hp
      exact mem_iUnion.mpr ⟨0, hp⟩
  unfold regionM1
  rw [hz, empty_union, hc, radial_cusp_interior]
  ext p
  simp

theorem radial_slim_union : radialSlims.union = range slimToCarrier := by
  unfold SlimPiecesV2.union
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    exact hj
  · intro hp
    exact mem_iUnion.mpr ⟨(0 : Fin 1), hp⟩

theorem radial_M2_height : regionM2 radialSlims =
    {p : carrier.Carrier | height p ≤ -(1 / 2 : ℝ)} := by
  unfold regionM2
  rw [radial_first_remainder, radial_slim_union, radial_second_remainder]

theorem radial_edge_height : radialEdgeBundle.edgePiece =
    {p : carrier.Carrier | height p ≤ -(3 / 4 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq.2
  · intro hp
    change height p ≤ -(3 / 4 : ℝ) at hp
    have hn : height p < 0 := by linarith
    exact ⟨⟨p, hn⟩, ⟨mem_univ _, hp⟩, rfl⟩

theorem radial_edge_relative : relInt (regionM2 radialSlims) radialEdgeBundle.edgePiece =
    {p : carrier.Carrier | height p < -(3 / 4 : ℝ)} := by
  rw [radial_M2_height, radial_edge_height,
    height_relInt_le _ _ (by norm_num) (by norm_num) (by norm_num)]
  ext p
  constructor
  · exact And.left
  · intro hp
    change height p < -(3 / 4 : ℝ) at hp
    exact ⟨hp, by linarith⟩

theorem radial_M3_circle : regionM3 radialSlims radialEdgeBundle =
    radialCircleBundle.region := by
  unfold regionM3
  rw [radial_edge_relative, radial_M2_height, radialCircleBundle_region]
  ext p
  simp only [mem_sdiff, mem_ofPred_eq, not_lt]
  exact and_comm

theorem radial_M2_frontier : frontier (regionM2 radialSlims) =
    {p : carrier.Carrier | height p = -(1 / 2 : ℝ)} := by
  rw [radial_M2_height]
  have hc : IsClosed {p : carrier.Carrier | height p ≤ -(1 / 2 : ℝ)} :=
    isClosed_le height_continuous continuous_const
  rw [frontier, hc.closure_eq, height_interior_le _ (by norm_num) (by norm_num)]
  ext p
  simp only [mem_sdiff, mem_ofPred_eq, not_lt]
  constructor
  · intro hp
    exact le_antisymm hp.1 hp.2
  · intro hp
    exact ⟨hp.le, hp.ge⟩

end GC.GraphManifold.Assembly.FC39P0.X135Radial
