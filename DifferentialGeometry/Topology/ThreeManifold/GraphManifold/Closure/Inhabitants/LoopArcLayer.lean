import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopFaceLayers
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopArcEmbedding
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopFaceRegion
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopAnnulusData

/-!
The SAME complete sphere annulus and deep core torus give the native arc and residual loop layer.
Both original handle ends and all whole-face partitions retain the actual fixed circle region.
-/
set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold GC.Endpoint
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly
open FC39P0

private theorem loopArcLayer_endUnion :
    (⋃ b : Bool, (standardLoopBallHandleCycle.handle
      ⟨0,standardLoopBallHandleCycle.len_pos⟩).endDisk b) =
    (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).endDisk false ∪
    (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).endDisk true := by
  ext p
  constructor
  · intro hp
    obtain ⟨b,hb⟩ := mem_iUnion.mp hp
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  · rintro (hp | hp)
    · exact mem_iUnion.mpr ⟨false,hp⟩
    · exact mem_iUnion.mpr ⟨true,hp⟩

def loopArcLayer : ArcLayer (NoCuts.carrier standardThreeSphereLift.{0})
    loopEdgeLayer loopCircleRegionData loopFaceLayer loopHandleEndLayer loopRimChartLayer where
  arcFaceCount := 1
  arcFace := fun _ => Set.range loopBallAnnulus
  arcOwner := fun _ => (0 : Fin 2)
  arcOwner_kind := fun _ => rfl
  arcBase := fun _ => loopBallArcBase
  arcBase_embedding := fun _ => loopBallArcBase_embedding
  arcFace_eq := fun _ => loopBallAnnulus_projection_range
  arcDefining := fun _ => (1 : Fin 3)
  arcBase_defining := fun _ => loopBallArcBase_ballZero
  arcAnnulus := fun _ => loopBallAnnulusNative
  arcAnnulus_continuous := fun _ => loopBallAnnulusNative_continuous
  arcAnnulus_injective := fun _ => loopBallAnnulusNative_injective
  arcAnnulus_range := fun _ => loopBallAnnulusNative_range
  arcAnnulus_proj := fun _ => loopBallAnnulusNative_projection
  loopFaceCount := 1
  loopFace := fun _ => loopComplementFace
  loopOwner := fun _ => (1 : Fin 2)
  loopOwner_kind := fun _ => rfl
  loopBase := fun _ => loopCoreBaseCircle
  loopBase_embedding := fun _ => loopCoreBaseCircle_embedding
  loopFace_eq := fun _ => loopComplementFace_projection
  loopDefining := fun _ => (2 : Fin 3)
  loopBase_defining := fun _ => loopCoreDefining_loop
  loopFace_closed := fun _ => loopComplementFace_closed
  loopFace_nonempty := fun _ => loopComplementFace_nonempty
  arcFace_disjoint := by
    intro j j' hne
    exact False.elim (hne (@Subsingleton.elim (Fin 1) inferInstance j j'))
  loopFace_disjoint := by
    intro j j' hne
    exact False.elim (hne (@Subsingleton.elim (Fin 1) inferInstance j j'))
  arc_loop_disjoint := by
    intro _j _j'
    apply loopCertificateFace_disjoint.mono
    · exact loopBallAnnulus_face
    · exact subset_rfl
  face_partition := by
    intro f _hf
    fin_cases f
    · change ((⋃ _h : Fin 1, ⋃ b : Bool, ⋃ (_ : (0 : Fin 2) = 0),
        (standardLoopBallHandleCycle.handle
          ⟨0,standardLoopBallHandleCycle.len_pos⟩).endDisk b) ∪
        (⋃ _j : Fin 1, ⋃ (_ : (0 : Fin 2) = 0), Set.range loopBallAnnulus)) ∪
        (⋃ _j : Fin 1, ⋃ (_ : (1 : Fin 2) = 0), loopComplementFace) = loopBallWholeFace
      ext p
      simp only [mem_union,mem_iUnion]
      constructor
      · rintro ((⟨_h,b,_he,hp⟩ | ⟨_j,_he,hp⟩) | ⟨_j,he,_hp⟩)
        · rw [loopBallWholeFace_partition]
          cases b
          · exact Or.inl (Or.inl hp)
          · exact Or.inl (Or.inr hp)
        · rw [loopBallWholeFace_partition]
          exact Or.inr hp
        · norm_num at he
      · intro hp
        rw [loopBallWholeFace_partition] at hp
        rcases hp with (hp | hp) | hp
        · exact Or.inl (Or.inl ⟨(0 : Fin 1),false,by trivial,hp⟩)
        · exact Or.inl (Or.inl ⟨(0 : Fin 1),true,by trivial,hp⟩)
        · exact Or.inl (Or.inr ⟨(0 : Fin 1),by trivial,hp⟩)
    · change ((⋃ _h : Fin 1, ⋃ b : Bool, ⋃ (_ : (0 : Fin 2) = 1),
        (standardLoopBallHandleCycle.handle
          ⟨0,standardLoopBallHandleCycle.len_pos⟩).endDisk b) ∪
        (⋃ _j : Fin 1, ⋃ (_ : (0 : Fin 2) = 1), Set.range loopBallAnnulus)) ∪
        (⋃ _j : Fin 1, ⋃ (_ : (1 : Fin 2) = 1), loopComplementFace) = loopComplementFace
      ext p
      simp only [mem_union,mem_iUnion]
      constructor
      · rintro ((⟨_h,_b,he,_hp⟩ | ⟨_j,he,_hp⟩) | ⟨_j,_he,hp⟩)
        · norm_num at he
        · norm_num at he
        · exact hp
      · exact fun hp => Or.inr ⟨(0 : Fin 1),by trivial,hp⟩
  face_region_inter := by
    intro f _hf
    fin_cases f
    · change loopBallWholeFace ∩ loopCircleRegion =
        (⋃ _j : Fin 1, ⋃ (_ : (0 : Fin 2) = 0), Set.range loopBallAnnulus) ∪
        (⋃ _j : Fin 1, ⋃ (_ : (1 : Fin 2) = 0), loopComplementFace)
      ext p
      simp only [mem_inter_iff,mem_union,mem_iUnion]
      constructor
      · intro hp
        have ha : p ∈ Set.range loopBallAnnulus := by
          rw [← loopBallWholeFace_region]
          exact hp
        exact Or.inl ⟨(0 : Fin 1),by trivial,ha⟩
      · rintro (⟨_j,_he,hp⟩ | ⟨_j,he,_hp⟩)
        · have hr : p ∈ loopBallWholeFace ∩ loopCircleRegion := by
            rw [loopBallWholeFace_region]
            exact hp
          exact hr
        · norm_num at he
    · change loopComplementFace ∩ loopCircleRegion =
        (⋃ _j : Fin 1, ⋃ (_ : (0 : Fin 2) = 1), Set.range loopBallAnnulus) ∪
        (⋃ _j : Fin 1, ⋃ (_ : (1 : Fin 2) = 1), loopComplementFace)
      ext p
      simp only [mem_inter_iff,mem_union,mem_iUnion]
      constructor
      · exact fun hp => Or.inr ⟨(0 : Fin 1),by trivial,hp.1⟩
      · rintro (⟨_j,he,_hp⟩ | ⟨_j,_he,hp⟩)
        · norm_num at he
        · refine ⟨hp,?_⟩
          rw [← loopCircleRegion_core_inter] at hp
          exact hp.1
  handleArc := fun _h _b => (0 : Fin 1)
  handleArc_owner := fun _h _b => rfl
  handleArc_meets := fun _h _b j _hp => @Subsingleton.elim (Fin 1) inferInstance 0 j
  endDisk_loop_disjoint := by
    intro _h b _j
    apply (loopHandle_core_disjoint ⟨0,standardLoopBallHandleCycle.len_pos⟩).mono
    · rintro p ⟨w,rfl⟩
      exact ⟨(w,iccEnd b),rfl⟩
    · rintro p ⟨w,_,hw⟩
      exact ⟨w,hw⟩
  endDisk_rim := by
    intro _h b
    exact (loopBallAnnulus_end_rim b).symm.trans (loopBallAnnulus_endDisk_inter b).symm
  arcEnd := fun _j b => ((0 : Fin 1),b)
  arcEnd_arc := fun j _b => @Subsingleton.elim (Fin 1) inferInstance 0 j
  arcEnd_injective := fun _j _b _b' he => congrArg Prod.snd he
  arcEnd_surjective := by
    intro h b
    refine ⟨b,Prod.ext ?_ rfl⟩
    exact @Subsingleton.elim (Fin 1) inferInstance 0 h
  arcAnnulus_end := by
    intro _j b
    exact (loopBallAnnulus_endDisk_inter b).trans (loopBallAnnulusNative_end b).symm
  arcBase_end := by
    intro _j b
    change loopBallArcBase (iccEnd b) = loopBaseCorner (finTwoEquiv (finTwoEquiv.symm b)) (0,0)
    rw [finTwoEquiv.apply_symm_apply]
    exact loopBallArcBase_end b

end GC.GraphManifold.Assembly
