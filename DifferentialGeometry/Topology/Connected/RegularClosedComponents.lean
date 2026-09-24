import DifferentialGeometry.Topology.Connected.ComponentIn
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.Compact

open Set

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {K : Set X}

private theorem closure_interior_image_of_isClopen
    (hK : closure (interior K) = K) {C : Set K} (hC : IsClopen C) :
    closure (interior (Subtype.val '' C : Set X)) = Subtype.val '' C := by
  have hclosed : IsClosed K := hK ▸ isClosed_closure
  have hCclosed : IsClosed (Subtype.val '' C : Set X) :=
    hclosed.isClosedMap_subtype_val C hC.isClosed
  obtain ⟨U, hU, hCU⟩ := hC.isOpen.image_val
  apply Subset.antisymm (closure_minimal interior_subset hCclosed)
  intro x hx
  rw [hCU] at hx
  have hxcl : x ∈ closure (U ∩ interior K) :=
    hU.inter_closure ⟨hx.1, hK.symm ▸ hx.2⟩
  apply closure_mono ?_ hxcl
  apply interior_maximal ?_ (hU.inter isOpen_interior)
  intro y hy
  rw [hCU]
  exact ⟨hy.1, interior_subset hy.2⟩

theorem closure_interior_connectedComponentIn [LocallyConnectedSpace K]
    (hK : closure (interior K) = K) (x : X) :
    closure (interior (connectedComponentIn K x)) = connectedComponentIn K x := by
  by_cases hx : x ∈ K
  · rw [connectedComponentIn_eq_image hx]
    exact closure_interior_image_of_isClopen hK isClopen_connectedComponent
  · rw [connectedComponentIn_eq_empty hx, interior_empty, closure_empty]

theorem isCompact_connectedComponentIn (hK : IsCompact K) (x : X) :
    IsCompact (connectedComponentIn K x) := by
  by_cases hx : x ∈ K
  · let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    rw [connectedComponentIn_eq_image hx]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  · rw [connectedComponentIn_eq_empty hx]
    exact isCompact_empty

theorem frontier_connectedComponentIn_subset [LocallyConnectedSpace X] (K : Set X) (x : X) :
    frontier (connectedComponentIn K x) ⊆ frontier K := by
  intro y hy
  refine ⟨closure_mono (connectedComponentIn_subset K x) hy.1, ?_⟩
  intro hyint
  have hyC : y ∈ connectedComponentIn K x := by
    rw [← closure_connectedComponentIn_inter K x]
    exact ⟨hy.1, interior_subset hyint⟩
  have hsub : connectedComponentIn (interior K) y ⊆ connectedComponentIn K x := by
    rw [connectedComponentIn_eq hyC]
    exact connectedComponentIn_mono y interior_subset
  have hopen : IsOpen (connectedComponentIn (interior K) y) :=
    isOpen_interior.connectedComponentIn
  exact hy.2 ((interior_maximal hsub hopen) (mem_connectedComponentIn hyint))

theorem frontier_connectedComponentIn_eq_iUnion [LocallyConnectedSpace X]
    (hK : IsClosed K) {ι : Type*} (F : ι → Set X)
    (hF : ∀ i, IsPreconnected (F i)) (hfront : frontier K = ⋃ i, F i)
    (x : X) :
    frontier (connectedComponentIn K x) =
      ⋃ i, ⋃ (_ : (F i ∩ connectedComponentIn K x).Nonempty), F i := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨i, hyF⟩ := mem_iUnion.mp
      (hfront ▸ frontier_connectedComponentIn_subset K x hy)
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨⟨y, hyF,
      (hK.connectedComponentIn x).frontier_subset hy⟩, hyF⟩⟩
  · intro y hy
    obtain ⟨i, hy⟩ := mem_iUnion.mp hy
    obtain ⟨⟨z, hzF, hzC⟩, hyF⟩ := mem_iUnion.mp hy
    have hsub : F i ⊆ K := by
      intro w hw
      exact hK.frontier_subset (hfront.symm ▸ mem_iUnion.mpr ⟨i, hw⟩)
    have hFC : F i ⊆ connectedComponentIn K x := by
      rw [connectedComponentIn_eq hzC]
      exact (hF i).subset_connectedComponentIn hzF hsub
    refine ⟨subset_closure (hFC hyF), ?_⟩
    intro hyint
    have hyfront : y ∈ frontier K := hfront.symm ▸ mem_iUnion.mpr ⟨i, hyF⟩
    exact hyfront.2 (interior_mono (connectedComponentIn_subset K x) hyint)

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {K : Set X}

theorem interior_connectedComponentIn_eq_inter [DiscreteTopology (ConnectedComponents K)] (x : X) :
    interior (connectedComponentIn K x) = interior K ∩ connectedComponentIn K x := by
  by_cases hx : x ∈ K
  · rw [connectedComponentIn_eq_image hx]
    obtain ⟨U, hU, hUC⟩ :=
      (ConnectedComponents.discreteTopology_iff.mp inferInstance (⟨x, hx⟩ : K)).image_val
    rw [hUC, interior_inter, hU.interior_eq]
    exact Set.ext (fun y => by simp only [mem_inter_iff]; exact
      ⟨fun h => ⟨h.2, h.1, interior_subset h.2⟩, fun h => ⟨h.2.1, h.1⟩⟩)
  · rw [connectedComponentIn_eq_empty hx, interior_empty, inter_empty]

end DifferentialGeometry.Topology


namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {W L : Set X}

private theorem exists_isClopen_component_union_meeting
    [DiscreteTopology (ConnectedComponents W)] :
    ∃ A : Set W, IsClopen A ∧ Subtype.val '' A = ⋃ y ∈ L, connectedComponentIn W y := by
  let I : Set (ConnectedComponents W) :=
    ConnectedComponents.mk '' {y : W | y.val ∈ L}
  let A : Set W := ConnectedComponents.mk ⁻¹' I
  refine ⟨A, ⟨(isClosed_discrete I).preimage ConnectedComponents.continuous_coe,
    (isOpen_discrete I).preimage ConnectedComponents.continuous_coe⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨z, ⟨y, hyL, heq⟩, rfl⟩
    exact mem_iUnion₂.mpr ⟨y.val, hyL, by
      rw [connectedComponentIn_eq_image y.property]
      exact ⟨z, ConnectedComponents.coe_eq_coe'.mp heq.symm, rfl⟩⟩
  · intro hx
    obtain ⟨y, hyL, hxy⟩ := mem_iUnion₂.mp hx
    have hyW : y ∈ W := connectedComponentIn_nonempty_iff.mp ⟨x, hxy⟩
    rw [connectedComponentIn_eq_image hyW] at hxy
    obtain ⟨z, hz, rfl⟩ := hxy
    exact ⟨z, ⟨⟨y, hyW⟩, hyL, (ConnectedComponents.coe_eq_coe'.mpr hz).symm⟩, rfl⟩

theorem component_union_meeting_union_of_inter_subset
    {B : Set X} [DiscreteTopology (ConnectedComponents W)]
    (hW : IsClosed W)
    (hB : IsClosed B) (hBconn : IsPreconnected B)
    (hBW : B ∩ W ⊆ ⋃ a ∈ L, connectedComponentIn W a)
    (hmeet : (B ∩ ⋃ a ∈ L, connectedComponentIn W a).Nonempty) :
    (⋃ a ∈ L, connectedComponentIn (W ∪ B) a) =
      (⋃ a ∈ L, connectedComponentIn W a) ∪ B := by
  let R := ⋃ a ∈ L, connectedComponentIn W a
  obtain ⟨Q, hQ, heq⟩ := exists_isClopen_component_union_meeting (W := W) (L := L)
  change Subtype.val '' Q = R at heq
  have hRclosed : IsClosed R := by
    simpa only [heq] using hW.isClosedMap_subtype_val Q hQ.isClosed
  have hDimage : Subtype.val '' Qᶜ = W \ R := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.property, ?_⟩
      intro hR
      rw [← heq] at hR
      obtain ⟨v, hv, hvz⟩ := hR
      exact hz ((Subtype.ext hvz) ▸ hv)
    · rintro ⟨hxW, hxR⟩
      exact ⟨⟨x, hxW⟩, fun hxQ => hxR (heq ▸ ⟨⟨x, hxW⟩, hxQ, rfl⟩), rfl⟩
  have hDclosed : IsClosed (W \ R) :=
    hDimage ▸ hW.isClosedMap_subtype_val Qᶜ hQ.isOpen.isClosed_compl
  have hdis : Disjoint (R ∪ B) (W \ R) := by
    rw [disjoint_left]
    intro x hx hxD
    rcases hx with hxR | hxB
    · exact hxD.2 hxR
    · exact hxD.2 (hBW ⟨hxB, hxD.1⟩)
  apply subset_antisymm
  · intro x hx
    obtain ⟨a, haL, hxa⟩ := mem_iUnion₂.mp hx
    by_contra hxnot
    have hxD : x ∈ W \ R := by
      have hxV := connectedComponentIn_subset (W ∪ B) a hxa
      exact ⟨hxV.resolve_right (fun h => hxnot (Or.inr h)), fun h => hxnot (Or.inl h)⟩
    have haV : a ∈ W ∪ B := connectedComponentIn_nonempty_iff.mp ⟨x, hxa⟩
    have haC : a ∈ connectedComponentIn (W ∪ B) a := mem_connectedComponentIn haV
    have haRB : a ∈ R ∪ B := by
      rcases haV with haW | haB
      · exact Or.inl (mem_iUnion₂.mpr ⟨a, haL, mem_connectedComponentIn haW⟩)
      · exact Or.inr haB
    have hcover : connectedComponentIn (W ∪ B) a ⊆ (R ∪ B) ∪ (W \ R) := by
      intro z hz
      rcases connectedComponentIn_subset (W ∪ B) a hz with hzW | hzB
      · by_cases hzR : z ∈ R
        · exact Or.inl (Or.inl hzR)
        · exact Or.inr ⟨hzW, hzR⟩
      · exact Or.inl (Or.inr hzB)
    obtain ⟨z, _, hzRB, hzD⟩ :=
      isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn
        (R ∪ B) (W \ R) (hRclosed.union hB) hDclosed hcover
        ⟨a, haC, haRB⟩ ⟨x, hxa, hxD⟩
    exact disjoint_left.mp hdis hzRB hzD
  · intro x hx
    rcases hx with hxR | hxB
    · obtain ⟨a, haL, hxa⟩ := mem_iUnion₂.mp hxR
      exact mem_iUnion₂.mpr ⟨a, haL, connectedComponentIn_mono a subset_union_left hxa⟩
    · obtain ⟨z, hzB, hzR⟩ := hmeet
      obtain ⟨a, haL, hza⟩ := mem_iUnion₂.mp hzR
      have hza' : z ∈ connectedComponentIn (W ∪ B) a :=
        connectedComponentIn_mono a subset_union_left hza
      refine mem_iUnion₂.mpr ⟨a, haL, ?_⟩
      rw [connectedComponentIn_eq hza']
      exact hBconn.subset_connectedComponentIn hzB subset_union_right hxB

theorem component_union_meeting_regular_closed
    [DiscreteTopology (ConnectedComponents W)]
    (hWregular : closure (interior W) = W) (hL : L ⊆ interior W) :
    let R := ⋃ y ∈ L, connectedComponentIn W y
    R ⊆ W ∧ L ⊆ interior R ∧
      closure (interior R) = R ∧ frontier R ⊆ frontier W ∧ IsClosed (W \ R) := by
  let R := ⋃ y ∈ L, connectedComponentIn W y
  obtain ⟨A, hA, heq⟩ := exists_isClopen_component_union_meeting (W := W) (L := L)
  change Subtype.val '' A = R at heq
  have hWclosed : IsClosed W := hWregular ▸ isClosed_closure
  have hRclosed : IsClosed R := heq ▸ hWclosed.isClosedMap_subtype_val A hA.isClosed
  have hRW : R ⊆ W := by
    rintro x hx
    obtain ⟨y, _, hxy⟩ := mem_iUnion₂.mp hx
    exact connectedComponentIn_subset W y hxy
  have hregular : closure (interior R) = R :=
    heq ▸ closure_interior_image_of_isClopen hWregular hA
  obtain ⟨O, hO, hOA⟩ := hA.isOpen.image_val
  have hRset : R = O ∩ W := heq.symm.trans hOA
  have hinterior : interior R = O ∩ interior W := by
    rw [hRset, interior_inter, hO.interior_eq]
  have hlow : L ⊆ interior R := by
    intro x hx
    have hxR : x ∈ R := mem_iUnion₂.mpr ⟨x, hx, mem_connectedComponentIn (interior_subset (hL hx))⟩
    rw [hinterior]
    exact ⟨(hRset.subset hxR).1, hL hx⟩
  have hfront : frontier R ⊆ frontier W := by
    intro x hx
    have hxR : x ∈ R := hRclosed.frontier_subset hx
    refine ⟨subset_closure (hRW hxR), ?_⟩
    intro hxint
    apply hx.2
    rw [hinterior]
    exact ⟨(hRset.subset hxR).1, hxint⟩
  have hremoved : IsClosed (W \ R) := by
    have heq : W \ R = W \ O := by rw [hRset]; ext x; simp only [mem_sdiff, mem_inter_iff]; tauto
    rw [heq]
    exact hWclosed.sdiff hO
  exact ⟨hRW, hlow, hregular, hfront, hremoved⟩


theorem component_union_meeting_compact_regular_closed
    [DiscreteTopology (ConnectedComponents W)] (hWcompact : IsCompact W)
    (hWregular : closure (interior W) = W) (hL : L ⊆ interior W) :
    let R := ⋃ y ∈ L, connectedComponentIn W y
    IsCompact R ∧ R ⊆ W ∧ L ⊆ interior R ∧
      closure (interior R) = R ∧ frontier R ⊆ frontier W ∧ IsClosed (W \ R) := by
  obtain ⟨hRW, hL, hregular, hfront, hremoved⟩ :=
    component_union_meeting_regular_closed hWregular hL
  have hRclosed : IsClosed (⋃ y ∈ L, connectedComponentIn W y) := hregular ▸ isClosed_closure
  exact ⟨hWcompact.of_isClosed_subset hRclosed hRW, hRW, hL, hregular, hfront, hremoved⟩

theorem frontier_component_union_meeting_eq_iUnion
    [DiscreteTopology (ConnectedComponents W)] (hWclosed : IsClosed W)
    {ι : Type*} (F : ι → Set X) (hF : ∀ i, IsPreconnected (F i))
    (hfrontier : frontier W = ⋃ i, F i) :
    let R := ⋃ y ∈ L, connectedComponentIn W y
    frontier R = ⋃ i ∈ {i | (F i ∩ R).Nonempty}, F i := by
  let R := ⋃ y ∈ L, connectedComponentIn W y
  obtain ⟨A, hA, heq⟩ := exists_isClopen_component_union_meeting (W := W) (L := L)
  change Subtype.val '' A = R at heq
  have hRclosed : IsClosed R := heq ▸ hWclosed.isClosedMap_subtype_val A hA.isClosed
  have hRW : R ⊆ W := by
    rintro x hx
    obtain ⟨y, _, hxy⟩ := mem_iUnion₂.mp hx
    exact connectedComponentIn_subset W y hxy
  obtain ⟨O, hO, hOA⟩ := hA.isOpen.image_val
  have hRset : R = O ∩ W := heq.symm.trans hOA
  have hfront : frontier R ⊆ frontier W := by
    intro x hx
    have hxR : x ∈ R := hRclosed.frontier_subset hx
    refine ⟨subset_closure (hRW hxR), ?_⟩
    intro hxW
    apply hx.2
    rw [hRset, interior_inter, hO.interior_eq]
    exact ⟨(hRset.subset hxR).1, hxW⟩
  have hFW (i : ι) : F i ⊆ W := by
    intro x hx
    exact hWclosed.frontier_subset (hfrontier.symm ▸ mem_iUnion.mpr ⟨i, hx⟩)
  have hwhole (i : ι) (hi : (F i ∩ R).Nonempty) : F i ⊆ R := by
    obtain ⟨x, hxF, hxR⟩ := hi
    obtain ⟨y, hyL, hxy⟩ := mem_iUnion₂.mp hxR
    have hFC : F i ⊆ connectedComponentIn W y := by
      rw [connectedComponentIn_eq hxy]
      exact (hF i).subset_connectedComponentIn hxF (hFW i)
    exact hFC.trans (subset_iUnion₂_of_subset y hyL subset_rfl)
  apply subset_antisymm
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hfrontier ▸ hfront hx)
    exact mem_iUnion₂.mpr ⟨i, ⟨x, hxi, hRclosed.frontier_subset hx⟩, hxi⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    refine ⟨subset_closure (hwhole i hi hxi), ?_⟩
    intro hxint
    exact (hfrontier.symm ▸ mem_iUnion.mpr ⟨i, hxi⟩ : x ∈ frontier W).2
      (interior_mono hRW hxint)

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {W L : Set X} [DiscreteTopology (ConnectedComponents W)]

theorem component_union_meeting_interior_anchor
    (hL : L ⊆ interior W)
    (hconn : ∀ y ∈ L, IsPreconnected (interior (connectedComponentIn W y))) :
    let R := ⋃ y ∈ L, connectedComponentIn W y
    ∀ x ∈ interior R, ∃ a ∈ connectedComponentIn (interior R) x, a ∈ L := by
  let R := ⋃ y ∈ L, connectedComponentIn W y
  have hRW : R ⊆ W := by
    rintro x hx
    obtain ⟨y, _, hxy⟩ := mem_iUnion₂.mp hx
    exact connectedComponentIn_subset W y hxy
  change ∀ x ∈ interior R, ∃ a ∈ connectedComponentIn (interior R) x, a ∈ L
  intro x hx
  obtain ⟨y, hyL, hxy⟩ := mem_iUnion₂.mp (interior_subset hx)
  have hyW : y ∈ W := interior_subset (hL hyL)
  have hcomponent : connectedComponentIn W y ⊆ R :=
    subset_iUnion₂_of_subset y hyL subset_rfl
  have hxint : x ∈ interior (connectedComponentIn W y) := by
    rw [interior_connectedComponentIn_eq_inter]
    exact ⟨interior_mono hRW hx, hxy⟩
  have hyint : y ∈ interior (connectedComponentIn W y) := by
    rw [interior_connectedComponentIn_eq_inter]
    exact ⟨hL hyL, mem_connectedComponentIn hyW⟩
  exact ⟨y, (hconn y hyL).subset_connectedComponentIn hxint
    (interior_mono hcomponent) hyint, hyL⟩

end DifferentialGeometry.Topology
