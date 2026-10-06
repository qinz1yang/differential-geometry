import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBaseLayers

/-!
The SAME two WHOLE native faces and both original handle ends supply the actual face and rim layers.
The entire genuine rimBox has the original vertex, handle and circle-region sign partitions.
-/
set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold GC.Endpoint
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly
open FC39P0

private def loopFaceLayerIndex : Fin standardLoopBallHandleCycle.len :=
  ⟨0,standardLoopBallHandleCycle.len_pos⟩

private theorem loopFaceLayer_single (k : Fin standardLoopBallHandleCycle.len) :
    k = loopFaceLayerIndex := by
  apply Fin.ext
  have hbound : standardLoopBallHandleCycle.len ≤ 1 := by
    rw [standardLoopBallHandleCycle_len]
  have hlt := lt_of_lt_of_le k.isLt hbound
  change k.val = 0
  omega

def loopFaceLayer : FaceLayer (NoCuts.carrier standardThreeSphereLift.{0})
    (BoundaryTori.empty (NoCuts.carrier standardThreeSphereLift.{0}))
    loopVertexLayer loopSeamLayer loopPortLayer where
  faceCount := 2
  face := loopCertificateFace
  faceOwner := id
  faceModel := loopCertificateFaceModel
  face_exhausted := by
    intro k
    change (⋃ f : Fin 2, ⋃ (_ : f = k), loopCertificateFace f) =
      (loopCertificateVertex k).boundaryImage
    rw [← loopCertificateFace_boundary k]
    ext p
    constructor
    · intro hp
      obtain ⟨f,hf⟩ := mem_iUnion.mp hp
      obtain ⟨he,hm⟩ := mem_iUnion.mp hf
      change f = k at he
      subst f
      exact hm
    · exact fun hp => mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨rfl,hp⟩⟩
  faceKind := fun _ => .partitioned
  face_disjoint := by
    intro f f' hne _hs _ht
    fin_cases f <;> fin_cases f'
    · exact False.elim (hne rfl)
    · exact loopCertificateFace_disjoint
    · exact loopCertificateFace_disjoint.symm
    · exact False.elim (hne rfl)
  face_external := fun _f i => i.elim0
  external_face := fun i => i.elim0
  face_torusSeam := fun _f c => c.elim0
  torusSeam_face := fun c => c.elim0
  face_sphereSeam := fun _f c => c.elim0
  sphereSeam_face := fun c => c.elim0

def loopHandleEndLayer : HandleEndLayer (NoCuts.carrier standardThreeSphereLift.{0})
    loopVertexLayer loopEdgeLayer loopFaceLayer where
  handleEnd := fun _h _b => (0 : Fin 2)
  handleFace := fun _h _b => (0 : Fin 2)
  handleFace_owner := fun _h _b => rfl
  handleFace_kind := fun _h _b => rfl
  handleEnd_face := by
    intro _h b p hp
    change p ∈ loopBallWholeFace
    cases b
    · exact standardLoopBallHandleCycle.start_face loopFaceLayerIndex hp
    · have hf := standardLoopBallHandleCycle.end_face loopFaceLayerIndex hp
      rw [loopFaceLayer_single (finRotate standardLoopBallHandleCycle.len
        loopFaceLayerIndex)] at hf
      exact hf
  endDisk_disjoint := by
    intro h b h' b' hne
    have hb : b ≠ b' := by
      intro he
      exact hne (Prod.ext (@Subsingleton.elim (Fin 1) inferInstance h h') he)
    apply Set.disjoint_left.mpr
    rintro p ⟨w,hw⟩ ⟨w',hw'⟩
    have he := (standardLoopBallHandleCycle.handle loopFaceLayerIndex).injective
      (hw.trans hw'.symm)
    have ht := congrArg (fun v : ClosedCell 2 × Set.Icc (0 : ℝ) 1 => v.2.val) he
    cases b <;> cases b'
    · exact hb rfl
    · norm_num [iccEnd] at ht
    · norm_num [iccEnd] at ht
    · exact hb rfl

def loopRimChartLayer : RimChartLayer (NoCuts.carrier standardThreeSphereLift.{0})
    loopEdgeLayer loopCircleRegionData where
  handleCorner := fun _h b => finTwoEquiv.symm b
  handleCorner_bijective := by
    constructor
    · intro hb hb' he
      apply Prod.ext
      · exact @Subsingleton.elim (Fin 1) inferInstance hb.1 hb'.1
      · exact finTwoEquiv.symm.injective he
    · intro k
      exact ⟨((0 : Fin 1),finTwoEquiv k),finTwoEquiv.symm_apply_apply k⟩
  rimChart := fun _h b => standardLoopBallHandleCycle.rimChart loopFaceLayerIndex b
  rim_source := fun _h b => standardLoopBallHandleCycle.rim_source loopFaceLayerIndex b
  rim_proj := by
    intro _h b p hp
    have hv := (standardLoopBallHandleCycle.rim_source loopFaceLayerIndex b).mp hp
    refine ⟨loopRegionRim_domain b p.1 p.2 hv,?_⟩
    change loopCircleProjection ⟨standardLoopBallHandleCycle.rimChart
      loopFaceLayerIndex b p,loopRegionRim_domain b p.1 p.2 hv⟩ =
      loopBaseCorner (finTwoEquiv (finTwoEquiv.symm b)) p.2
    rw [finTwoEquiv.apply_symm_apply]
    exact loopRegionRim_projection b p.1 p.2 hv
  rim_label := fun _h b => standardLoopBallHandleCycle.rim_label loopFaceLayerIndex b
  rim_disjoint := by
    intro h b h' b' hne
    have hb : b ≠ b' := by
      intro he
      exact hne (Prod.ext (@Subsingleton.elim (Fin 1) inferInstance h h') he)
    apply standardLoopBallHandleCycle.rim_disjoint loopFaceLayerIndex b loopFaceLayerIndex b'
    exact fun he => hb (congrArg Prod.snd he)

theorem loopRimRegionLayer : RimRegionLayer (NoCuts.carrier standardThreeSphereLift.{0})
    loopVertexLayer loopEdgeLayer loopCircleRegionData loopHandleEndLayer loopRimChartLayer where
  rim_vertex := by
    intro _h b p hp
    have hh := standardLoopBallHandleCycle.rim_ball loopFaceLayerIndex b hp
    rw [loopFaceLayer_single (rimBall standardLoopBallHandleCycle.len
      loopFaceLayerIndex b)] at hh
    exact hh
  rim_handle := fun _h b => standardLoopBallHandleCycle.rim_handle loopFaceLayerIndex b
  rim_region := by
    intro _h b p hp
    have hv := (standardLoopBallHandleCycle.rim_source loopFaceLayerIndex b).mp hp
    exact loopCircleRegion_rim b p.1 hv

theorem loopProtectionLayer : ProtectionLayer (NoCuts.carrier standardThreeSphereLift.{0})
    (BoundaryTori.empty (NoCuts.carrier standardThreeSphereLift.{0}))
    loopEdgeLayer loopCircleRegionData loopSeamLayer loopRimChartLayer where
  external_region_disjoint := fun i => i.elim0
  external_handle_disjoint := fun i => i.elim0
  external_edgeCircle_disjoint := fun i => i.elim0
  external_torusSeam_disjoint := fun i => i.elim0
  external_sphereSeam_disjoint := fun i => i.elim0
  rim_external_disjoint := fun _h _b i => i.elim0
  rim_torusSeam_disjoint := fun _h _b c => c.elim0
  rim_sphereSeam_disjoint := fun _h _b c => c.elim0
  sphereSeam_region_disjoint := fun c => c.elim0
  sphereSeam_handle_disjoint := fun c => c.elim0

end GC.GraphManifold.Assembly
