import DifferentialGeometry.Topology.ThreeManifold.Surgery.Capping.Defs

noncomputable section

open Set Function Relation
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace Capping

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {T : TubeSystem M} (K : Capping T N)


def componentMap : ConnectedComponents T.core → ConnectedComponents N :=
  K.coreInclusion.continuous.connectedComponentsMap

@[simp] theorem componentMap_mk (x : T.core) :
    K.componentMap (ConnectedComponents.mk x) = ConnectedComponents.mk (K.coreInclusion x) := rfl

private noncomputable def spherePoint : Sphere 2 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

private theorem coreBoundary_preconnected (b : T.Boundary) :
    IsPreconnected (range (T.coreBoundarySphere b)) := by
  have : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
  exact isPreconnected_range (T.coreBoundarySphere b).continuous

private noncomputable def capComponent (b : T.Boundary) : ConnectedComponents T.core :=
  ConnectedComponents.mk (T.coreBoundarySphere b spherePoint)

private theorem coreBoundary_subset_fiber (b : T.Boundary) :
    range (T.coreBoundarySphere b) ⊆
      {z : T.core | ConnectedComponents.mk z = capComponent (T := T) b} := by
  intro z hz
  exact ConnectedComponents.coe_eq_coe'.mpr
    ((coreBoundary_preconnected (T := T) b).subset_connectedComponent
      (⟨spherePoint, rfl⟩ :
        (T.coreBoundarySphere b) spherePoint ∈ range (T.coreBoundarySphere b)) hz)

private theorem capRange_preconnected (b : T.Boundary) :
    IsPreconnected (range (K.cap b)) := by
  have : ConnectedSpace ThreeBall := isConnected_iff_connectedSpace.mp
    ((convex_closedBall (0 : ThreeSpace) 1).isConnected ⟨0, by simp⟩)
  exact isPreconnected_range (K.cap b).continuous

private noncomputable def piece (D : ConnectedComponents T.core) : Set N :=
  K.coreInclusion '' {z : T.core | ConnectedComponents.mk z = D} ∪
    ⋃ (b : {b : T.Boundary // capComponent (T := T) b = D}), range (K.cap b.1)

private noncomputable def pieceAux (D : ConnectedComponents T.core) :
    Option {b : T.Boundary // capComponent (T := T) b = D} → Set N
  | none => K.coreInclusion '' {z : T.core | ConnectedComponents.mk z = D}
  | some b => range (K.cap b.1)

private theorem cap_range_subset_piece (b : T.Boundary) :
    range (K.cap b) ⊆ piece K (capComponent (T := T) b) := by
  intro n hn
  exact Or.inr (mem_iUnion.mpr ⟨⟨b, rfl⟩, hn⟩)

private theorem coreInclusion_mem_piece_iff {D : ConnectedComponents T.core} {z : T.core} :
    K.coreInclusion z ∈ piece K D ↔ ConnectedComponents.mk z = D := by
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨w, hw, hwz⟩ := h
      have hwz' : w = z := K.coreEmbedding.injective hwz
      rw [← hwz']
      exact hw
    · obtain ⟨⟨b, hb⟩, hbn⟩ := mem_iUnion.mp h
      have hmem : K.coreInclusion z ∈ range K.coreInclusion ∩ range (K.cap b) :=
        ⟨⟨z, rfl⟩, hbn⟩
      rw [K.core_cap_intersection b] at hmem
      obtain ⟨y, hy⟩ := hmem
      have hy' : T.coreBoundarySphere b y = z := K.coreEmbedding.injective hy
      have hz' : ConnectedComponents.mk z = capComponent (T := T) b := by
        rw [← hy']
        exact coreBoundary_subset_fiber (T := T) b ⟨y, rfl⟩
      rw [hz', hb]
  · intro hz
    exact Or.inl ⟨z, hz, rfl⟩

private theorem corePart_preconnected (D : ConnectedComponents T.core) :
    IsPreconnected (K.coreInclusion '' {z : T.core | ConnectedComponents.mk z = D}) := by
  obtain ⟨z₀, rfl⟩ := ConnectedComponents.surjective_coe D
  have hset : {z : T.core | ConnectedComponents.mk z = ConnectedComponents.mk z₀} =
      connectedComponent z₀ := connectedComponents_preimage_singleton
  rw [hset]
  exact isPreconnected_connectedComponent.image _ K.coreInclusion.continuous.continuousOn

private theorem boundaryPoint_mem_corePart (b : T.Boundary) :
    K.coreInclusion (T.coreBoundarySphere b (K.attaching b spherePoint)) ∈
      K.coreInclusion '' {z : T.core | ConnectedComponents.mk z = capComponent (T := T) b} :=
  ⟨_, coreBoundary_subset_fiber (T := T) b ⟨K.attaching b spherePoint, rfl⟩, rfl⟩

private theorem boundaryPoint_mem_capRange (b : T.Boundary) :
    K.coreInclusion (T.coreBoundarySphere b (K.attaching b spherePoint)) ∈ range (K.cap b) :=
  ⟨sphereToThreeBall spherePoint, K.boundary_eq b spherePoint⟩

private theorem pieceAux_link (D : ConnectedComponents T.core)
    (b : {b : T.Boundary // capComponent (T := T) b = D}) :
    (pieceAux K D none ∩ pieceAux K D (some b)).Nonempty := by
  refine ⟨K.coreInclusion (T.coreBoundarySphere b.1 (K.attaching b.1 spherePoint)), ?_, ?_⟩
  · refine ⟨T.coreBoundarySphere b.1 (K.attaching b.1 spherePoint), ?_, rfl⟩
    exact (coreBoundary_subset_fiber (T := T) b.1
      ⟨K.attaching b.1 spherePoint, rfl⟩).trans b.2
  · exact boundaryPoint_mem_capRange K b.1

private theorem piece_preconnected (D : ConnectedComponents T.core) :
    IsPreconnected (piece K D) := by
  have hunion : (⋃ i, pieceAux K D i) = piece K D := by
    rw [iUnion_option, piece]
    simp only [pieceAux]
  have hlink : ∀ i j, ReflTransGen
      (fun i j => (pieceAux K D i ∩ pieceAux K D j).Nonempty) i j := by
    intro i j
    match i, j with
    | none, none => exact ReflTransGen.refl
    | none, some b => exact ReflTransGen.single (pieceAux_link K D b)
    | some b, none =>
      obtain ⟨x, hx⟩ := pieceAux_link K D b
      exact ReflTransGen.single ⟨x, hx.2, hx.1⟩
    | some b, some b' =>
      obtain ⟨x, hx⟩ := pieceAux_link K D b
      exact (ReflTransGen.single (show (pieceAux K D (some b) ∩
        pieceAux K D none).Nonempty from ⟨x, hx.2, hx.1⟩)).tail (pieceAux_link K D b')
  have hpc : IsPreconnected (⋃ i, pieceAux K D i) :=
    IsPreconnected.iUnion_of_reflTransGen
      (fun i => by cases i with
        | none => exact corePart_preconnected K D
        | some b => exact capRange_preconnected K b.1) hlink
  rwa [hunion] at hpc

private theorem piece_isClosed [CompactSpace T.core] [T2Space N]
    (D : ConnectedComponents T.core) : IsClosed (piece K D) := by
  obtain ⟨z₀, rfl⟩ := ConnectedComponents.surjective_coe D
  have hset : {z : T.core | ConnectedComponents.mk z = ConnectedComponents.mk z₀} =
      connectedComponent z₀ := connectedComponents_preimage_singleton
  have hcore : IsClosed (K.coreInclusion '' {z : T.core |
      ConnectedComponents.mk z = ConnectedComponents.mk z₀}) := by
    rw [hset]
    exact (IsCompact.image (isClosed_connectedComponent).isCompact
      K.coreInclusion.continuous).isClosed
  have hfin : ({b : T.Boundary | capComponent (T := T) b = ConnectedComponents.mk z₀}).Finite :=
    Set.toFinite _
  have hcaps : IsClosed (⋃ b ∈
      {b : T.Boundary | capComponent (T := T) b = ConnectedComponents.mk z₀},
      range (K.cap b)) := by
    refine hfin.isClosed_biUnion ?_
    intro b _
    exact (isCompact_range (K.cap b).continuous).isClosed
  rw [piece]
  refine hcore.union ?_
  rw [iUnion_subtype]
  exact hcaps

private theorem piece_cover : ⋃ D, piece K D = univ := by
  refine eq_univ_of_forall ?_
  intro n
  have hn : n ∈ range K.coreInclusion ∪ ⋃ b, range (K.cap b) := by
    rw [K.exhaustive]
    trivial
  rcases hn with hn | hn
  · obtain ⟨z, rfl⟩ := hn
    exact mem_iUnion.mpr ⟨ConnectedComponents.mk z,
      (coreInclusion_mem_piece_iff K).mpr rfl⟩
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hn
    exact mem_iUnion.mpr ⟨capComponent (T := T) b, cap_range_subset_piece K b hb⟩

private theorem piece_pairwise_disjoint : Pairwise (Disjoint on piece K) := by
  intro D D' hne
  rw [Function.onFun, disjoint_left]
  intro n hn hn'
  by_cases hcore : n ∈ range K.coreInclusion
  · obtain ⟨z, rfl⟩ := hcore
    exact hne (((coreInclusion_mem_piece_iff K).mp hn).symm.trans
      ((coreInclusion_mem_piece_iff K).mp hn'))
  · have hnuc : n ∈ ⋃ (b : {b : T.Boundary //
        capComponent (T := T) b = D}), range (K.cap b.1) := by
      rcases hn with hn | hn
      · obtain ⟨w, -, hwn⟩ := hn
        exact absurd ⟨w, hwn⟩ hcore
      · exact hn
    have hnuc' : n ∈ ⋃ (b : {b : T.Boundary //
        capComponent (T := T) b = D'}), range (K.cap b.1) := by
      rcases hn' with hn' | hn'
      · obtain ⟨w, -, hwn⟩ := hn'
        exact absurd ⟨w, hwn⟩ hcore
      · exact hn'
    obtain ⟨⟨b, hb⟩, hbn⟩ := mem_iUnion.mp hnuc
    obtain ⟨⟨b', hb'⟩, hb'n⟩ := mem_iUnion.mp hnuc'
    have hbb' : b ≠ b' := by
      intro hEq
      exact hne (by rw [← hb, ← hb', hEq])
    exact Set.disjoint_left.mp (K.cap_disjoint hbb') hbn hb'n

theorem rfs_cap_component_bijection [CompactSpace T.core] [LocallyConnectedSpace T.core]
    [T2Space N] : Function.Bijective K.componentMap := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    have hab' : ConnectedComponents.mk (K.coreInclusion x) =
        ConnectedComponents.mk (K.coreInclusion y) := by
      simpa only [componentMap, Continuous.connectedComponentsMap_mk] using hab
    have hmem : K.coreInclusion y ∈ connectedComponent (K.coreInclusion x) :=
      ConnectedComponents.coe_eq_coe'.mp hab'.symm
    have hx : K.coreInclusion x ∈ piece K (ConnectedComponents.mk x) :=
      (coreInclusion_mem_piece_iff K).mpr rfl
    have hxmem : K.coreInclusion x ∈ connectedComponent (K.coreInclusion x) := mem_connectedComponent
    set v := ⋃ D' ∈ {D' : ConnectedComponents T.core | D' ≠ ConnectedComponents.mk x},
      piece K D' with hv
    have hvc : IsClosed v := by
      rw [hv]
      refine (Set.toFinite
        ({D' : ConnectedComponents T.core | D' ≠ ConnectedComponents.mk x})).isClosed_biUnion ?_
      intro D' _
      exact piece_isClosed K D'
    have hsub : connectedComponent (K.coreInclusion x) ⊆
        piece K (ConnectedComponents.mk x) ∪ v := by
      intro n _
      have hn' : n ∈ ⋃ D', piece K D' := by
        rw [piece_cover K]
        exact mem_univ n
      obtain ⟨D', hD'⟩ := mem_iUnion.mp hn'
      by_cases hD : D' = ConnectedComponents.mk x
      · exact Or.inl (hD ▸ hD')
      · exact Or.inr (mem_iUnion.mpr ⟨D', mem_iUnion.mpr ⟨hD, hD'⟩⟩)
    have hdisj : connectedComponent (K.coreInclusion x) ∩
        (piece K (ConnectedComponents.mk x) ∩ v) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro n ⟨_, hnu, hnv⟩
      obtain ⟨D', hD'⟩ := mem_iUnion.mp hnv
      obtain ⟨hD'ne, hnD'⟩ := mem_iUnion.mp hD'
      exact Set.disjoint_left.mp (piece_pairwise_disjoint K hD'ne) hnD' hnu
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponent (x := K.coreInclusion x)))
      (piece K (ConnectedComponents.mk x)) v (piece_isClosed K _) hvc hsub hdisj with hCu | hCv
    · exact ((coreInclusion_mem_piece_iff K).mp (hCu hmem)).symm
    · exact absurd (hCv hxmem) (fun hxuv =>
        (Set.eq_empty_iff_forall_notMem.mp hdisj) (K.coreInclusion x) ⟨hxmem, hx, hxuv⟩)
  · intro c
    obtain ⟨n, rfl⟩ := ConnectedComponents.surjective_coe c
    have hn' : n ∈ ⋃ D, piece K D := by
      rw [piece_cover K]
      exact mem_univ n
    obtain ⟨D, hD⟩ := mem_iUnion.mp hn'
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe D
    have hzn : n ∈ piece K (ConnectedComponents.mk z) := hD
    have hzc : K.coreInclusion z ∈ piece K (ConnectedComponents.mk z) :=
      (coreInclusion_mem_piece_iff K).mpr rfl
    have hsame : ConnectedComponents.mk n = ConnectedComponents.mk (K.coreInclusion z) :=
      ConnectedComponents.coe_eq_coe'.mpr
        (((piece_preconnected K (ConnectedComponents.mk z)).subset_connectedComponent
          hzc) hzn)
    exact ⟨ConnectedComponents.mk z, by
      simpa only [componentMap, Continuous.connectedComponentsMap_mk] using hsame.symm⟩


def componentEquiv [CompactSpace T.core] [LocallyConnectedSpace T.core] [T2Space N] :
    ConnectedComponents T.core ≃ ConnectedComponents N :=
  Equiv.ofBijective K.componentMap K.rfs_cap_component_bijection


theorem component_meets_core [CompactSpace T.core] [LocallyConnectedSpace T.core] [T2Space N]
    (c : ConnectedComponents N) :
    ∃ x : T.core, ConnectedComponents.mk (K.coreInclusion x) = c := by
  obtain ⟨d, hd⟩ := K.rfs_cap_component_bijection.surjective c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe d
  exact ⟨x, hd⟩

end Capping

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
