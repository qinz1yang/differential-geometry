import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreCutChainProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreComponent
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRescale
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSimplyConnected

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private def middleBandIntervalInclusion : Ioo (-1 : ℝ) 1 → Icc (-2 : ℝ) 2 :=
  fun t => ⟨t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

private theorem middleBandIntervalInclusion_isEmbedding :
    _root_.Topology.IsEmbedding middleBandIntervalInclusion := by
  apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  exact _root_.Topology.IsEmbedding.subtypeVal

private def middleBandInclusion : Sphere 2 × Ioo (-1 : ℝ) 1 → TubeDomain :=
  Prod.map id middleBandIntervalInclusion

private theorem middleBandInclusion_isEmbedding :
    _root_.Topology.IsEmbedding middleBandInclusion :=
  _root_.Topology.IsEmbedding.id.prodMap middleBandIntervalInclusion_isEmbedding

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

private theorem range_tube_middleBandInclusion (a : T.Index) :
    Set.range (T.tube a ∘ middleBandInclusion) = T.removedBand a := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨middleBandInclusion z, z.2.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z.1, ⟨z.2.1, hz⟩), ?_⟩
    congr 1

private theorem tube_middleBandInclusion_isOpenEmbedding (a : T.Index)
    (hopen : IsOpen (T.removedBand a)) :
    _root_.Topology.IsOpenEmbedding (T.tube a ∘ middleBandInclusion) :=
  ⟨(T.embedding a).comp middleBandInclusion_isEmbedding,
    (T.range_tube_middleBandInclusion a).symm ▸ hopen⟩

def middleSphereCollar (a : T.Index) (hopen : IsOpen (T.removedBand a)) :
    DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
      (fun y : Sphere 2 => T.tube a (y, (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2))) :=
  DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.ofOpenInterval one_pos
    (T.tube a ∘ middleBandInclusion)
    (T.tube_middleBandInclusion_isOpenEmbedding a hopen)
    (by intro y; rfl)

@[simp] theorem middleSphereCollar_zero (a : T.Index) (hopen : IsOpen (T.removedBand a))
    (y : Sphere 2) :
    (T.middleSphereCollar a hopen).toFun (y, 0) = T.tube a (y, (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2)) :=
  (T.middleSphereCollar a hopen).zero_eq y

theorem middleSphereCollar_range (a : T.Index) (hopen : IsOpen (T.removedBand a)) :
    (T.middleSphereCollar a hopen).range = T.removedBand a := by
  let h : Sphere 2 × ℝ ≃ₜ Sphere 2 × Ioo (-1 : ℝ) 1 :=
    (Homeomorph.refl (Sphere 2)).prodCongr
      (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo 1 one_pos)
  change Set.range ((T.tube a ∘ middleBandInclusion) ∘ h) = _
  rw [h.surjective.range_comp]
  exact T.range_tube_middleBandInclusion a

theorem middleSphereCollar_toFun (a : T.Index) (hopen : IsOpen (T.removedBand a))
    (y : Sphere 2) (t : ℝ) :
    (T.middleSphereCollar a hopen).toFun (y, t) =
      T.tube a (y, ⟨
        (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo
          1 one_pos t : Set.Ioo (-1 : ℝ) 1).1,
        by
          have ht := (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo
            1 one_pos t : Set.Ioo (-1 : ℝ) 1).2
          constructor <;> linarith [ht.1, ht.2]⟩) := rfl

theorem middleSphereCollar_mem_positiveTube (a : T.Index) (hopen : IsOpen (T.removedBand a))
    (y : Sphere 2)
    {t : ℝ} (ht : 0 < t) :
    (T.middleSphereCollar a hopen).toFun (y, t) ∈ T.positiveTube a := by
  let r := DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo
    1 one_pos t
  refine ⟨(y, middleBandIntervalInclusion r), ?_, rfl⟩
  exact (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_pos_iff
    1 one_pos t).mpr ht

theorem middleSphereCollar_mem_negativeTube (a : T.Index) (hopen : IsOpen (T.removedBand a))
    (y : Sphere 2)
    {t : ℝ} (ht : t < 0) :
    (T.middleSphereCollar a hopen).toFun (y, t) ∈ T.negativeTube a := by
  let r := DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo
    1 one_pos t
  refine ⟨(y, middleBandIntervalInclusion r), ?_, rfl⟩
  exact (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_neg_iff
    1 one_pos t).mpr ht

end TubeSystem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)
    (hopen : ∀ a, IsOpen (T.removedBand a))

theorem pairwise_disjoint_middleSphereCollar_range :
    Pairwise fun a b => Disjoint (T.middleSphereCollar a (hopen a)).range
      (T.middleSphereCollar b (hopen b)).range := by
  intro a b hab
  rw [T.middleSphereCollar_range, T.middleSphereCollar_range]
  exact (T.disjoint hab).mono (T.removedBand_subset_range a) (T.removedBand_subset_range b)

theorem middleSphereCollar_zero_range (a : T.Index) :
    Set.range (fun y : Sphere 2 => (T.middleSphereCollar a (hopen a)).toFun (y, 0)) =
      T.middleSphere a := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    dsimp only
    rw [T.middleSphereCollar_zero]
    exact ⟨_, rfl, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.1, ?_⟩
    dsimp only
    rw [T.middleSphereCollar_zero]
    apply congrArg (T.tube a)
    exact Prod.ext rfl (Subtype.ext hz.symm)

theorem puncturedCore_eq_compl_iUnion_middleSphereCollar_zero_range :
    T.puncturedCore =
      (⋃ a, Set.range (fun y : Sphere 2 => (T.middleSphereCollar a (hopen a)).toFun (y, 0)))ᶜ := by
  simp_rw [T.middleSphereCollar_zero_range]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end

noncomputable section

open Set
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace TubeSystem
variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem isConnected_positiveTube (a : T.Index) : IsConnected (T.positiveTube a) := by
  let f : Sphere 2 × Ioc (0 : ℝ) 2 → M := fun z =>
    T.tube a (z.1, ⟨z.2.1, by
      exact ⟨by linarith [z.2.2.1], z.2.2.2⟩⟩)
  have hi : ConnectedSpace (Ioc (0 : ℝ) 2) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioc (by norm_num))
  have hs : ConnectedSpace (Sphere 2) := inferInstanceAs
    (ConnectedSpace DifferentialGeometry.Topology.SphereTwo)
  have hf : Continuous f := by
    apply (T.tube a).continuous.comp
    exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hrange : Set.range f = T.positiveTube a := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, z.2.2.1, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z.1, ⟨z.2.1, hz, z.2.2.2⟩), rfl⟩
  rw [← hrange]
  exact isConnected_range hf

theorem isConnected_negativeTube (a : T.Index) : IsConnected (T.negativeTube a) := by
  let f : Sphere 2 × Ico (-2 : ℝ) 0 → M := fun z =>
    T.tube a (z.1, ⟨z.2.1, by
      exact ⟨z.2.2.1, by linarith [z.2.2.2]⟩⟩)
  have hi : ConnectedSpace (Ico (-2 : ℝ) 0) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ico (by norm_num))
  have hs : ConnectedSpace (Sphere 2) := inferInstanceAs
    (ConnectedSpace DifferentialGeometry.Topology.SphereTwo)
  have hf : Continuous f := by
    apply (T.tube a).continuous.comp
    exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hrange : Set.range f = T.negativeTube a := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, z.2.2.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z.1, ⟨z.2.1, z.2.2.1, hz⟩), rfl⟩
  rw [← hrange]
  exact isConnected_range hf
end TubeSystem
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

private theorem middleSphereCollar_complement (a : T.Index) (hopen : IsOpen (T.removedBand a)) :
    (T.middleSphereCollar a hopen).complement = (T.middleSphere a)ᶜ := by
  change (Set.range (fun y : Sphere 2 => T.tube a (y, middleLevel)))ᶜ = _
  rw [show (fun y : Sphere 2 => T.tube a (y, middleLevel)) =
    (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) from rfl,
    T.range_tube_middleSphereSlice]

def middleSphereSides [T2Space M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]
    (a : T.Index) (hopen : IsOpen (T.removedBand a)) :
    T.MiddleSphereSides a := by
  let h := T.middleSphereCollar a hopen
  let : ConnectedSpace (Sphere 2) :=
    inferInstanceAs (ConnectedSpace DifferentialGeometry.Topology.SphereTwo)
  let y : Sphere 2 := DifferentialGeometry.Topology.sphereTwoNorth
  refine
    { A := h.positiveSide
      B := h.negativeSide
      isOpen_A := h.isOpen_positiveSide
      isOpen_B := h.isOpen_negativeSide
      disjoint := h.disjoint_negativeSide_positiveSide.symm
      union_eq := ?_
      positiveTube_subset := ?_
      negativeTube_subset := ?_ }
  · rw [Set.union_comm, ← h.complement_eq_negativeSide_union_positiveSide]
    exact T.middleSphereCollar_complement a hopen
  · have hsub : T.positiveTube a ⊆ h.positiveSide ∪ h.negativeSide := by
      rw [Set.union_comm, ← h.complement_eq_negativeSide_union_positiveSide,
        T.middleSphereCollar_complement]
      intro x hx hm
      exact (T.mem_puncturedCore_iff x).mp
        (T.positiveTube_subset_puncturedCore a hx) a hm
    exact (T.isConnected_positiveTube a).isPreconnected.subset_left_of_subset_union
      h.isOpen_positiveSide h.isOpen_negativeSide h.disjoint_negativeSide_positiveSide.symm
      hsub ⟨h.toFun (y, 1), T.middleSphereCollar_mem_positiveTube a hopen y (by norm_num),
        h.toFun_mem_positiveSide_of_pos y (by norm_num)⟩
  · have hsub : T.negativeTube a ⊆ h.positiveSide ∪ h.negativeSide := by
      rw [Set.union_comm, ← h.complement_eq_negativeSide_union_positiveSide,
        T.middleSphereCollar_complement]
      intro x hx hm
      exact (T.mem_puncturedCore_iff x).mp
        (T.negativeTube_subset_puncturedCore a hx) a hm
    exact (T.isConnected_negativeTube a).isPreconnected.subset_right_of_subset_union
      h.isOpen_positiveSide h.isOpen_negativeSide h.disjoint_negativeSide_positiveSide.symm
      hsub ⟨h.toFun (y, -1), T.middleSphereCollar_mem_negativeTube a hopen y (by norm_num),
        h.toFun_mem_negativeSide_of_neg y (by norm_num)⟩

theorem middleSphereSeparation_of_isOpen_removedBand
    [T2Space M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]
    (hopen : ∀ a, IsOpen (T.removedBand a)) : T.middleSphereSeparation :=
  fun a => ⟨T.middleSphereSides a (hopen a)⟩

end TubeSystem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [T2Space M]
    [LocallyPathConnectedSpace M] [SimplyConnectedSpace M] (T : TubeSystem M)

theorem simplyConnectedSpace_connectedComponentIn_puncturedCore
    (hopen : ∀ a, IsOpen (T.removedBand a))
    {x : M} (hx : x ∈ T.puncturedCore) :
    SimplyConnectedSpace ↥(connectedComponentIn T.puncturedCore x) := by
  let _ : SimplyConnectedSpace (Sphere 2) :=
    DifferentialGeometry.Topology.sphereTwoSimplyConnectedSpace
  have heq := T.puncturedCore_eq_compl_iUnion_middleSphereCollar_zero_range hopen
  simp only [T.middleSphereCollar_zero] at heq
  rw [heq] at hx ⊢
  exact DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.simplyConnectedSpace_connectedComponentIn_compl_iUnion
    (fun a => T.middleSphereCollar a (hopen a))
    (T.pairwise_disjoint_middleSphereCollar_range hopen) hx

theorem componentwiseSimplyConnected_of_isOpen_removedBand
    (hopen : ∀ a, IsOpen (T.removedBand a)) :
    T.componentwiseSimplyConnected := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hset : {y : ↥T.puncturedCore | ConnectedComponents.mk y = ConnectedComponents.mk x} =
      connectedComponent x := connectedComponents_preimage_singleton
  change SimplyConnectedSpace {y : ↥T.puncturedCore |
    ConnectedComponents.mk y = ConnectedComponents.mk x}
  rw [hset]
  exact (DifferentialGeometry.Topology.simplyConnectedSpace_connectedComponentIn_iff x.2).mp
    (T.simplyConnectedSpace_connectedComponentIn_puncturedCore hopen x.2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end
