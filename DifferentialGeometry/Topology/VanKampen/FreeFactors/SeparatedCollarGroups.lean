import DifferentialGeometry.Topology.VanKampen.FreeFactors.OpenCoverFreeFactors
import DifferentialGeometry.Topology.VanKampen.FreeFactors.CollarFreeFactor
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped ContinuousMap
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.ThreeManifold
namespace GC.Topology
universe u v
variable {S : Type v} [TopologicalSpace S] {X : Type u} [TopologicalSpace X]
  {e : S → X} (c : TwoSidedCollar e)

theorem collar_sides_disjoint [Nonempty S]
    (hsep : ConnectedComponents.mk c.negativePoint ≠ ConnectedComponents.mk c.positivePoint) :
    Disjoint c.negativeSide c.positiveSide := by
  rw [disjoint_left]
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have hab' : a = b := Subtype.ext hab.symm
  subst b
  have hccne : connectedComponent c.negativePoint ≠ connectedComponent c.positivePoint :=
    ConnectedComponents.coe_ne_coe.mp hsep
  exact disjoint_left.mp (connectedComponent_disjoint hccne) ha hb

theorem collar_negative_overlap_image [ConnectedSpace S]
    (hsep : ConnectedComponents.mk c.negativePoint ≠ ConnectedComponents.mk c.positivePoint) :
    c.negativeSide ∩ c.range = c.toFun '' ((univ : Set S) ×ˢ Iio (0 : ℝ)) := by
  ext x
  constructor
  · rintro ⟨hx, p, rfl⟩
    have ht : p.2 ≠ 0 := by
      intro ht
      exact c.negativeSide_subset_complement hx
        ⟨p.1, (c.zero_eq p.1).symm.trans (congrArg c.toFun (Prod.ext rfl ht.symm))⟩
    refine ⟨p, ⟨mem_univ _, ?_⟩, rfl⟩
    rcases lt_or_gt_of_ne ht with ht | ht
    · exact ht
    · exact (disjoint_left.mp (collar_sides_disjoint c hsep) hx
        (c.toFun_mem_positiveSide_of_pos p.1 ht)).elim
  · rintro ⟨p, hp, rfl⟩
    exact ⟨c.toFun_mem_negativeSide_of_neg p.1 hp.2, ⟨p, rfl⟩⟩

theorem collar_positive_overlap_image [ConnectedSpace S]
    (hsep : ConnectedComponents.mk c.negativePoint ≠ ConnectedComponents.mk c.positivePoint) :
    c.positiveSide ∩ c.range = c.toFun '' ((univ : Set S) ×ˢ Ioi (0 : ℝ)) := by
  ext x
  constructor
  · rintro ⟨hx, p, rfl⟩
    have ht : p.2 ≠ 0 := by
      intro ht
      exact c.positiveSide_subset_complement hx
        ⟨p.1, (c.zero_eq p.1).symm.trans (congrArg c.toFun (Prod.ext rfl ht.symm))⟩
    refine ⟨p, ⟨mem_univ _, ?_⟩, rfl⟩
    rcases lt_or_gt_of_ne ht with ht | ht
    · exact (disjoint_left.mp (collar_sides_disjoint c hsep)
        (c.toFun_mem_negativeSide_of_neg p.1 ht) hx).elim
    · exact ht
  · rintro ⟨p, hp, rfl⟩
    exact ⟨c.toFun_mem_positiveSide_of_pos p.1 hp.2, ⟨p, rfl⟩⟩

theorem simplyConnectedSpace_collar_image [SimplyConnectedSpace S]
    (J : Set ℝ) [ContractibleSpace J] :
    SimplyConnectedSpace ↥(c.toFun '' ((univ : Set S) ×ˢ J)) := by
  let h : ↥(c.toFun '' ((univ : Set S) ×ˢ J)) ≃ₜ S × J :=
    (c.isOpenEmbedding_toFun.toIsEmbedding.homeomorphImage ((univ : Set S) ×ˢ J)).symm.trans
      ((Homeomorph.Set.prod univ J).trans ((Homeomorph.Set.univ S).prodCongr (Homeomorph.refl _)))
  let k : S × J ≃ₕ S :=
    ((ContinuousMap.HomotopyEquiv.refl S).prodCongr
      (ContractibleSpace.hequiv_unit J).some).trans
        (Homeomorph.prodUnique S Unit).toHomotopyEquiv
  exact (h.toHomotopyEquiv.trans k).simplyConnectedSpace

theorem simplyConnectedSpace_negative_overlap [SimplyConnectedSpace S]
    (hsep : ConnectedComponents.mk c.negativePoint ≠ ConnectedComponents.mk c.positivePoint) :
    SimplyConnectedSpace ↥(c.negativeSide ∩ c.range) := by
  rw [collar_negative_overlap_image c hsep]
  let : ContractibleSpace (Iio (0 : ℝ)) := (convex_Iio 0).contractibleSpace ⟨-1, by norm_num⟩
  exact simplyConnectedSpace_collar_image c (Iio 0)

theorem simplyConnectedSpace_positive_overlap [SimplyConnectedSpace S]
    (hsep : ConnectedComponents.mk c.negativePoint ≠ ConnectedComponents.mk c.positivePoint) :
    SimplyConnectedSpace ↥(c.positiveSide ∩ c.range) := by
  rw [collar_positive_overlap_image c hsep]
  let : ContractibleSpace (Ioi (0 : ℝ)) := (convex_Ioi 0).contractibleSpace ⟨1, by norm_num⟩
  exact simplyConnectedSpace_collar_image c (Ioi 0)

theorem pathConnectedSpace_negativeSide [CompactSpace S] [Nonempty S]
    [T2Space X] [LocallyPathConnectedSpace X] : PathConnectedSpace c.negativeSide := by
  let : LocallyPathConnectedSpace c.complement := c.isOpen_complement.locallyPathConnectedSpace
  have h : IsPathConnected (connectedComponent c.negativePoint) := by
    rw [← pathComponent_eq_connectedComponent]
    exact isPathConnected_pathComponent
  exact isPathConnected_iff_pathConnectedSpace.mp
    (h.image continuous_subtype_val)

theorem pathConnectedSpace_positiveSide [CompactSpace S] [Nonempty S]
    [T2Space X] [LocallyPathConnectedSpace X] : PathConnectedSpace c.positiveSide := by
  let : LocallyPathConnectedSpace c.complement := c.isOpen_complement.locallyPathConnectedSpace
  have h : IsPathConnected (connectedComponent c.positivePoint) := by
    rw [← pathComponent_eq_connectedComponent]
    exact isPathConnected_pathComponent
  exact isPathConnected_iff_pathConnectedSpace.mp
    (h.image continuous_subtype_val)

theorem isFreeFactor_negativeSide [CompactSpace S] [SimplyConnectedSpace S]
    [T2Space X] [ConnectedSpace X] [LocallyPathConnectedSpace X]
    (hsep : ConnectedComponents.mk c.negativePoint ≠ ConnectedComponents.mk c.positivePoint)
    (x : c.negativeSide) : GC.Group.IsFreeFactor (FundamentalGroup c.negativeSide x)
      (FundamentalGroup X x.val) := by
  let : PathConnectedSpace c.negativeSide := pathConnectedSpace_negativeSide c
  let : PathConnectedSpace c.positiveSide := pathConnectedSpace_positiveSide c
  let : SimplyConnectedSpace c.range := simplyConnectedSpace_collar_range c
  let : SimplyConnectedSpace ↥(c.negativeSide ∩ c.range) := simplyConnectedSpace_negative_overlap c hsep
  let : SimplyConnectedSpace ↥(c.positiveSide ∩ c.range) := simplyConnectedSpace_positive_overlap c hsep
  exact isFreeFactor_separated_bridge c.negativeSide c.positiveSide c.range
    c.isOpen_negativeSide c.isOpen_positiveSide c.isOpen_range (collar_sides_disjoint c hsep)
    (by rw [← c.complement_eq_negativeSide_union_positiveSide]; exact c.complement_union_range) x

theorem isFreeFactor_positiveSide [CompactSpace S] [SimplyConnectedSpace S]
    [T2Space X] [ConnectedSpace X] [LocallyPathConnectedSpace X]
    (hsep : ConnectedComponents.mk c.negativePoint ≠ ConnectedComponents.mk c.positivePoint)
    (x : c.positiveSide) : GC.Group.IsFreeFactor (FundamentalGroup c.positiveSide x)
      (FundamentalGroup X x.val) := by
  let : PathConnectedSpace c.negativeSide := pathConnectedSpace_negativeSide c
  let : PathConnectedSpace c.positiveSide := pathConnectedSpace_positiveSide c
  let : SimplyConnectedSpace c.range := simplyConnectedSpace_collar_range c
  let : SimplyConnectedSpace ↥(c.negativeSide ∩ c.range) := simplyConnectedSpace_negative_overlap c hsep
  let : SimplyConnectedSpace ↥(c.positiveSide ∩ c.range) := simplyConnectedSpace_positive_overlap c hsep
  exact isFreeFactor_separated_bridge c.positiveSide c.negativeSide c.range
    c.isOpen_positiveSide c.isOpen_negativeSide c.isOpen_range (collar_sides_disjoint c hsep).symm
    (by rw [union_comm c.positiveSide, ← c.complement_eq_negativeSide_union_positiveSide];
        exact c.complement_union_range) x

theorem pathConnectedSpace_complement_of_same_sides [CompactSpace S] [ConnectedSpace S]
    [T2Space X] [ConnectedSpace X] [LocallyPathConnectedSpace X]
    (heq : ConnectedComponents.mk c.negativePoint = ConnectedComponents.mk c.positivePoint) :
    PathConnectedSpace c.complement := by
  let : Nonempty c.complement := ⟨c.negativePoint⟩
  let : PreconnectedSpace c.complement := preconnectedSpace_iff_connectedComponent.mpr (by
    intro y
    apply eq_univ_of_forall
    intro z
    have hy := c.component_eq_negative_or_positive y
    have hz := c.component_eq_negative_or_positive z
    have hzy : ConnectedComponents.mk z = ConnectedComponents.mk y := by
      rcases hz with hz | hz <;> rcases hy with hy | hy
      · exact hz.trans hy.symm
      · exact hz.trans (heq.trans hy.symm)
      · exact hz.trans (heq.symm.trans hy.symm)
      · exact hz.trans hy.symm
    rw [← ConnectedComponents.coe_eq_coe.mp hzy]
    exact mem_connectedComponent)
  let : ConnectedSpace c.complement :=
    { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }
  let : LocallyPathConnectedSpace c.complement := c.isOpen_complement.locallyPathConnectedSpace
  exact PathConnectedSpace.of_locallyPathConnectedSpace

theorem component_freeFactor_of_image {Y : Set X} (x : Y) (A : Set X)
    (hA : Subtype.val '' connectedComponent x = A)
    (hfree : ∀ a : A, GC.Group.IsFreeFactor (FundamentalGroup A a) (FundamentalGroup X a.val)) :
    GC.Group.IsFreeFactor (FundamentalGroup (connectedComponent x) ⟨x, mem_connectedComponent⟩)
      (FundamentalGroup X x.val) := by
  let E : ↥(connectedComponent x) ≃ₜ A :=
    (_root_.Topology.IsEmbedding.subtypeVal.homeomorphImage (connectedComponent x)).trans
      (Homeomorph.setCongr hA)
  let z : ↥(connectedComponent x) := ⟨x, mem_connectedComponent⟩
  have h := hfree (E z)
  let e := fundamentalGroupMulEquivOfHomotopyEquiv E.toHomotopyEquiv z (E z) rfl
  exact h.congr e.symm (MulEquiv.refl _)

theorem isFreeFactor_collar_component [CompactSpace S] [SimplyConnectedSpace S]
    [T2Space X] [ConnectedSpace X] [LocallyPathConnectedSpace X] (x : c.complement) :
    GC.Group.IsFreeFactor (FundamentalGroup (connectedComponent x) ⟨x, mem_connectedComponent⟩)
      (FundamentalGroup X x.val) := by
  classical
  by_cases hsep : ConnectedComponents.mk c.negativePoint ≠ ConnectedComponents.mk c.positivePoint
  · rcases c.component_eq_negative_or_positive x with hx | hx
    · apply component_freeFactor_of_image x c.negativeSide ?_ (isFreeFactor_negativeSide c hsep)
      change Subtype.val '' connectedComponent x = Subtype.val '' connectedComponent c.negativePoint
      rw [ConnectedComponents.coe_eq_coe.mp hx]
    · apply component_freeFactor_of_image x c.positiveSide ?_ (isFreeFactor_positiveSide c hsep)
      change Subtype.val '' connectedComponent x = Subtype.val '' connectedComponent c.positivePoint
      rw [ConnectedComponents.coe_eq_coe.mp hx]
  · let : PathConnectedSpace c.complement := pathConnectedSpace_complement_of_same_sides c (not_ne_iff.mp hsep)
    apply component_freeFactor_of_image x c.complement ?_ (isFreeFactor_collar_complement c)
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    simp

end GC.Topology
