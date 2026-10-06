import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialEmptyHandleLayers

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

theorem radialPartitionedFace {f : Fin 4} (hf : radialFaces.faceKind f = .partitioned) :
    f = 3 := by
  fin_cases f
  · cases hf
  · cases hf
  · cases hf
  · rfl

theorem radialLoopFace_region : radialFaces.face (3 : Fin 4) ⊆ radialCircleRegion.region := by
  rw [radialCircleRegion_range]
  intro p hp
  change height p = -(1 / 2 : ℝ) at hp
  change -(3 / 4 : ℝ) ≤ height p ∧ height p ≤ -(1 / 2 : ℝ)
  rw [hp]
  constructor <;> norm_num

def radialLoopLayer : ArcLayer carrier radialEdgeLayer radialCircleRegion
    radialFaces radialHandleEnds radialRims where
  arcFaceCount := 0
  arcFace := fun j => Fin.elim0 j
  arcOwner := fun j => Fin.elim0 j
  arcOwner_kind := fun j => Fin.elim0 j
  arcBase := fun j => Fin.elim0 j
  arcBase_embedding := fun j => Fin.elim0 j
  arcFace_eq := fun j => Fin.elim0 j
  arcDefining := fun j => Fin.elim0 j
  arcBase_defining := fun j => Fin.elim0 j
  arcAnnulus := fun j => Fin.elim0 j
  arcAnnulus_continuous := fun j => Fin.elim0 j
  arcAnnulus_injective := fun j => Fin.elim0 j
  arcAnnulus_range := fun j => Fin.elim0 j
  arcAnnulus_proj := fun j => Fin.elim0 j
  loopFaceCount := 1
  loopFace := fun _ => radialFaces.face (3 : Fin 4)
  loopOwner := fun _ => (3 : Fin 4)
  loopOwner_kind := fun _ => rfl
  loopBase := fun _ => radialLoopBase
  loopBase_embedding := fun _ => radialLoopBase_embedding
  loopFace_eq := fun _ => radialLoopFace_eq.symm
  loopDefining := fun _ => (0 : Fin 2)
  loopBase_defining := fun _ => radialLoopBase_defining
  loopFace_closed := fun _ => isClosed_eq height_continuous continuous_const
  loopFace_nonempty := fun _ => ⟨radialLoopCarrier 1, radialLoopCarrier_height _⟩
  arcFace_disjoint := fun j => Fin.elim0 j
  loopFace_disjoint := fun j k hn => (hn (Subsingleton.elim j k)).elim
  arc_loop_disjoint := fun j => Fin.elim0 j
  face_partition f hf := by
    have he := radialPartitionedFace hf
    subst f
    ext p
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro ((⟨h, _⟩ | ⟨j, _⟩) | ⟨j, _, hp⟩)
      · exact Fin.elim0 h
      · exact Fin.elim0 j
      · exact hp
    · intro hp
      exact Or.inr ⟨(0 : Fin 1), rfl, hp⟩
  face_region_inter f hf := by
    have he := radialPartitionedFace hf
    subst f
    ext p
    simp only [mem_inter_iff, mem_union, mem_iUnion]
    constructor
    · intro hp
      exact Or.inr ⟨(0 : Fin 1), rfl, hp.1⟩
    · rintro (⟨j, _⟩ | ⟨j, _, hp⟩)
      · exact Fin.elim0 j
      · exact ⟨hp, radialLoopFace_region hp⟩
  handleArc := fun h => Fin.elim0 h
  handleArc_owner := fun h => Fin.elim0 h
  handleArc_meets := fun h => Fin.elim0 h
  endDisk_loop_disjoint := fun h => Fin.elim0 h
  endDisk_rim := fun h => Fin.elim0 h
  arcEnd := fun j => Fin.elim0 j
  arcEnd_arc := fun j => Fin.elim0 j
  arcEnd_injective := fun j => Fin.elim0 j
  arcEnd_surjective := fun h => Fin.elim0 h
  arcAnnulus_end := fun j => Fin.elim0 j
  arcBase_end := fun j => Fin.elim0 j

end GC.GraphManifold.Assembly.FC39P0.X135Radial
