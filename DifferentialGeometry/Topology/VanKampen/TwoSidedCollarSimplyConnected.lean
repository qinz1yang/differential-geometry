import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarCover
import DifferentialGeometry.Topology.Connected.ComponentIn
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRestriction

noncomputable section

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

section

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
  {e : S → X} (h : TwoSidedCollar e)

private theorem simplyConnectedSpace_collarSlice_Iio [SimplyConnectedSpace S] (a : ℝ) :
    SimplyConnectedSpace (h.collarSlice (Iio a)) := by
  let _ : ContractibleSpace (Iio a) := (convex_Iio a).contractibleSpace ⟨a - 1, by change a - 1 < a; linarith⟩
  let hp : S × Iio a ≃ₕ S :=
    ((ContinuousMap.HomotopyEquiv.refl S).prodCongr
      (ContractibleSpace.hequiv_unit (Iio a)).some).trans
        (Homeomorph.prodUnique S Unit).toHomotopyEquiv
  let he : S × Iio a ≃ₜ h.collarSlice (Iio a) :=
    (((Homeomorph.Set.univ S).symm.prodCongr (Homeomorph.refl (Iio a))).trans
      (Homeomorph.Set.prod (univ : Set S) (Iio a)).symm).trans
        (h.isOpenEmbedding_toFun.toIsEmbedding.homeomorphImage (univ ×ˢ Iio a))
  exact (he.symm.toHomotopyEquiv.trans hp).simplyConnectedSpace

private theorem simplyConnectedSpace_collarSlice_Ioi [SimplyConnectedSpace S] (a : ℝ) :
    SimplyConnectedSpace (h.collarSlice (Ioi a)) := by
  let _ : ContractibleSpace (Ioi a) := (convex_Ioi a).contractibleSpace ⟨a + 1, by change a < a + 1; linarith⟩
  let hp : S × Ioi a ≃ₕ S :=
    ((ContinuousMap.HomotopyEquiv.refl S).prodCongr
      (ContractibleSpace.hequiv_unit (Ioi a)).some).trans
        (Homeomorph.prodUnique S Unit).toHomotopyEquiv
  let he : S × Ioi a ≃ₜ h.collarSlice (Ioi a) :=
    (((Homeomorph.Set.univ S).symm.prodCongr (Homeomorph.refl (Ioi a))).trans
      (Homeomorph.Set.prod (univ : Set S) (Ioi a)).symm).trans
        (h.isOpenEmbedding_toFun.toIsEmbedding.homeomorphImage (univ ×ˢ Ioi a))
  exact (he.symm.toHomotopyEquiv.trans hp).simplyConnectedSpace

theorem simplyConnectedSpace_negativeSide
    [CompactSpace S] [T2Space X] [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace X] [SimplyConnectedSpace S] :
    SimplyConnectedSpace h.negativeSide := by
  let V := h.positiveSide ∪ h.range
  have hV : IsOpen V := h.isOpen_positiveSide.union h.isOpen_range
  have hc : h.negativeSide ∪ V = univ := by
    change h.negativeSide ∪ (h.positiveSide ∪ h.range) = univ
    rw [← union_assoc, ← h.complement_eq_negativeSide_union_positiveSide,
      h.complement_union_range]
  have hi : h.negativeSide ∩ V = h.collarSlice (Iio 0) := by
    ext x
    constructor
    · rintro ⟨hx, hp | hr⟩
      · exact (Set.disjoint_left.mp h.disjoint_negativeSide_positiveSide hx hp).elim
      · exact (h.mem_collarSlice_iff_time (Iio 0) ⟨x, hr⟩).mpr
          (h.time_neg_of_mem_negativeSide_range ⟨x, hr⟩ hx)
    · rintro ⟨p, hp, rfl⟩
      exact ⟨h.toFun_mem_negativeSide_of_neg p.1 hp.2, Or.inr ⟨p, rfl⟩⟩
  let _ : PathConnectedSpace h.negativeSide :=
    isPathConnected_iff_pathConnectedSpace.mp h.isPathConnected_negativeSide
  have hpV : IsPathConnected V := by
    refine h.isPathConnected_positiveSide.union ?_ ?_
    · exact isPathConnected_range h.isOpenEmbedding_toFun.continuous
    · let s : S := Classical.choice inferInstance
      exact ⟨h.toFun (s, 1), h.toFun_mem_positiveSide_of_pos s one_pos, ⟨(s, 1), rfl⟩⟩
  let _ : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp hpV
  let _ : SimplyConnectedSpace ↥(h.negativeSide ∩ V) := by
    rw [hi]
    exact h.simplyConnectedSpace_collarSlice_Iio 0
  let s : S := Classical.choice inferInstance
  exact (DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_union
    h.negativeSide V h.isOpen_negativeSide hV hc (h.toFun (s, -1))
    ⟨h.toFun_mem_negativeSide_of_neg s (by norm_num), Or.inr ⟨(s, -1), rfl⟩⟩).1

theorem simplyConnectedSpace_positiveSide
    [CompactSpace S] [T2Space X] [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace X] [SimplyConnectedSpace S] :
    SimplyConnectedSpace h.positiveSide := by
  let V := h.negativeSide ∪ h.range
  have hV : IsOpen V := h.isOpen_negativeSide.union h.isOpen_range
  have hc : h.positiveSide ∪ V = univ := by
    change h.positiveSide ∪ (h.negativeSide ∪ h.range) = univ
    rw [← union_assoc, union_comm h.positiveSide,
      ← h.complement_eq_negativeSide_union_positiveSide, h.complement_union_range]
  have hi : h.positiveSide ∩ V = h.collarSlice (Ioi 0) := by
    ext x
    constructor
    · rintro ⟨hx, hn | hr⟩
      · exact (Set.disjoint_left.mp h.disjoint_negativeSide_positiveSide hn hx).elim
      · exact (h.mem_collarSlice_iff_time (Ioi 0) ⟨x, hr⟩).mpr
          (h.time_pos_of_mem_positiveSide_range ⟨x, hr⟩ hx)
    · rintro ⟨p, hp, rfl⟩
      exact ⟨h.toFun_mem_positiveSide_of_pos p.1 hp.2, Or.inr ⟨p, rfl⟩⟩
  let _ : PathConnectedSpace h.positiveSide :=
    isPathConnected_iff_pathConnectedSpace.mp h.isPathConnected_positiveSide
  have hpV : IsPathConnected V := by
    refine h.isPathConnected_negativeSide.union ?_ ?_
    · exact isPathConnected_range h.isOpenEmbedding_toFun.continuous
    · let s : S := Classical.choice inferInstance
      exact ⟨h.toFun (s, -1), h.toFun_mem_negativeSide_of_neg s (by norm_num), ⟨(s, -1), rfl⟩⟩
  let _ : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp hpV
  let _ : SimplyConnectedSpace ↥(h.positiveSide ∩ V) := by
    rw [hi]
    exact h.simplyConnectedSpace_collarSlice_Ioi 0
  let s : S := Classical.choice inferInstance
  exact (DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_union
    h.positiveSide V h.isOpen_positiveSide hV hc (h.toFun (s, 1))
    ⟨h.toFun_mem_positiveSide_of_pos s one_pos, Or.inr ⟨(s, 1), rfl⟩⟩).1

theorem simplyConnectedSpace_connectedComponent_complement
    [CompactSpace S] [T2Space X] [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace X] [SimplyConnectedSpace S] (x : h.complement) :
    SimplyConnectedSpace ↥(connectedComponent x) := by
  rcases h.component_eq_negative_or_positive x with hx | hx
  · rw [ConnectedComponents.coe_eq_coe.mp hx]
    exact (Topology.IsEmbedding.subtypeVal.homeomorphImage
      (connectedComponent h.negativePoint)).toHomotopyEquiv.simplyConnectedSpace
      (hY := h.simplyConnectedSpace_negativeSide)
  · rw [ConnectedComponents.coe_eq_coe.mp hx]
    exact (Topology.IsEmbedding.subtypeVal.homeomorphImage
      (connectedComponent h.positivePoint)).toHomotopyEquiv.simplyConnectedSpace
      (hY := h.simplyConnectedSpace_positiveSide)

end

section

variable {S X ι : Type*} [TopologicalSpace S] [TopologicalSpace X]
  {e : ι → S → X} (c : ∀ i, TwoSidedCollar (e i))

omit [TopologicalSpace S] [TopologicalSpace X] in
private theorem zeroSlices_compl_insert [DecidableEq ι] (J : Finset ι) (i : ι) :
    (⋃ j ∈ (↑(insert i J) : Set ι), Set.range (e j))ᶜ =
      (⋃ j ∈ (↑J : Set ι), Set.range (e j))ᶜ \ Set.range (e i) := by
  ext x
  simp only [Finset.coe_insert, mem_compl_iff, mem_iUnion, mem_insert_iff,
    mem_sdiff]
  constructor
  · intro hx
    exact ⟨fun h => hx ⟨h.choose, Or.inr h.choose_spec.1, h.choose_spec.2⟩,
      fun h => hx ⟨i, Or.inl rfl, h⟩⟩
  · rintro ⟨hJ, hi⟩ ⟨j, hj | hj, hx⟩
    · exact hi (hj ▸ hx)
    · exact hJ ⟨j, hj, hx⟩

private theorem connectedComponentIn_compl_zeroSlices_insert_of_disjoint
    [DecidableEq ι] (J : Finset ι) (i : ι) {x : X}
    (hx : x ∈ (⋃ j ∈ (↑J : Set ι), Set.range (e j))ᶜ)
    (hd : Disjoint (connectedComponentIn (⋃ j ∈ (↑J : Set ι), Set.range (e j))ᶜ x)
      (c i).range) :
    connectedComponentIn (⋃ j ∈ (↑(insert i J) : Set ι), Set.range (e j))ᶜ x =
      connectedComponentIn (⋃ j ∈ (↑J : Set ι), Set.range (e j))ᶜ x := by
  rw [zeroSlices_compl_insert]
  apply Set.Subset.antisymm (connectedComponentIn_mono x sdiff_subset)
  apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hx)
  intro y hy
  refine ⟨connectedComponentIn_subset _ _ hy, ?_⟩
  rintro ⟨s, hs⟩
  exact Set.disjoint_left.mp hd hy ⟨(s, 0), ((c i).zero_eq s).trans hs⟩

private theorem simplyConnectedSpace_connectedComponentIn_compl_zeroSlices_finset
    [CompactSpace S] [SimplyConnectedSpace S] [T2Space X] [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace X]
    (hdisj : Pairwise fun i j => Disjoint (c i).range (c j).range)
    (J : Finset ι) {x : X} (hx : x ∈ (⋃ j ∈ (↑J : Set ι), Set.range (e j))ᶜ) :
    SimplyConnectedSpace ↥(connectedComponentIn
      (⋃ j ∈ (↑J : Set ι), Set.range (e j))ᶜ x) := by
  classical
  induction J using Finset.induction_on generalizing x with
  | empty =>
    have he : (⋃ j ∈ (↑(∅ : Finset ι) : Set ι), Set.range (e j)) = (∅ : Set X) := by
      simp
    rw [he, compl_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
    exact (Homeomorph.Set.univ X).toHomotopyEquiv.simplyConnectedSpace
  | @insert i J hi ih =>
    let A : Set X := (⋃ j ∈ (↑J : Set ι), Set.range (e j))ᶜ
    let B : Set X := (⋃ j ∈ (↑(insert i J) : Set ι), Set.range (e j))ᶜ
    have hBA : B ⊆ A := by
      dsimp [B, A]
      rw [zeroSlices_compl_insert]
      exact sdiff_subset
    have hxA : x ∈ A := hBA hx
    let C : Set X := connectedComponentIn A x
    have hxC : x ∈ C := mem_connectedComponentIn hxA
    have hAo : IsOpen A :=
      (isClosed_biUnion_finset (fun j _ => (isCompact_range (c j).continuous_e).isClosed)).isOpen_compl
    have hCo : IsOpen C := hAo.connectedComponentIn
    let _ : LocallyPathConnectedSpace C := hCo.locallyPathConnectedSpace
    let _ : SimplyConnectedSpace C := ih hxA
    by_cases hmeet : (C ∩ (c i).range).Nonempty
    · obtain ⟨z, hzC, hzr⟩ := hmeet
      have hrC : (c i).range ⊆ C := by
        have hsub := range_subset_connectedComponentIn_complement c hdisj (↑J : Set ι) hi hzr
        change (c i).range ⊆ connectedComponentIn A z at hsub
        rw [← connectedComponentIn_eq hzC] at hsub
        exact hsub
      let d := (c i).codRestrict C hrC
      have hd : d.complement = (Subtype.val ⁻¹' B : Set C) := by
        dsimp [d]
        rw [(c i).codRestrict_complement C hrC]
        ext y
        change y.1 ∉ Set.range (e i) ↔ y.1 ∈ B
        change y.1 ∉ Set.range (e i) ↔ y.1 ∈
          (⋃ j ∈ (↑(insert i J) : Set ι), Set.range (e j))ᶜ
        rw [zeroSlices_compl_insert]
        exact ⟨fun hy => ⟨connectedComponentIn_subset A x y.2, hy⟩, fun hy => hy.2⟩
      let y : C := ⟨x, hxC⟩
      have hy : y ∈ d.complement := by rw [hd]; exact hx
      have hsc : SimplyConnectedSpace ↥(connectedComponentIn d.complement y) :=
        (DifferentialGeometry.Topology.simplyConnectedSpace_connectedComponentIn_iff hy).mpr
          (d.simplyConnectedSpace_connectedComponent_complement ⟨y, hy⟩)
      have heq := image_connectedComponentIn_preimage_connectedComponentIn hBA hx
      change Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' B : Set C) y =
        connectedComponentIn B x at heq
      change SimplyConnectedSpace ↥(connectedComponentIn B x)
      rw [← heq]
      exact (Topology.IsEmbedding.subtypeVal.homeomorphImage
        (connectedComponentIn (Subtype.val ⁻¹' B : Set C) y)).symm.toHomotopyEquiv.simplyConnectedSpace
        (hY := hd ▸ hsc)
    · rw [connectedComponentIn_compl_zeroSlices_insert_of_disjoint c J i hxA
        (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hmeet))]
      exact ih hxA

theorem simplyConnectedSpace_connectedComponentIn_compl_iUnion
    [CompactSpace S] [SimplyConnectedSpace S] [T2Space X] [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace X] [Finite ι]
    (hdisj : Pairwise fun i j => Disjoint (c i).range (c j).range)
    {x : X} (hx : x ∈ (⋃ i, Set.range (e i))ᶜ) :
    SimplyConnectedSpace ↥(connectedComponentIn (⋃ i, Set.range (e i))ᶜ x) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have he : (⋃ j ∈ (↑(Finset.univ : Finset ι) : Set ι), Set.range (e j)) =
      ⋃ j, Set.range (e j) := by
    simp only [Finset.coe_univ, mem_univ, iUnion_true]
  have h := simplyConnectedSpace_connectedComponentIn_compl_zeroSlices_finset c hdisj
    Finset.univ (x := x) (by rw [he]; exact hx)
  rwa [he] at h

end

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
