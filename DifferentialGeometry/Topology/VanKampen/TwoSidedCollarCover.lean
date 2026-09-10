/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Analysis.Convex.Contractible
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation

set_option autoImplicit false

open Filter Topology
open scoped ContinuousMap

universe u v

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

open Set

variable {S : Type v} [TopologicalSpace S] {X : Type u} [TopologicalSpace X]
  {e : S → X} (h : TwoSidedCollar e)

include h

def collarSlice (I : Set ℝ) : Set X := h.toFun '' (Set.univ ×ˢ I)

theorem collarSlice_subset_range (I : Set ℝ) : h.collarSlice I ⊆ h.range := by
  rintro _ ⟨p, _, rfl⟩
  exact ⟨p, rfl⟩

theorem isOpen_collarSlice {I : Set ℝ} (hI : IsOpen I) : IsOpen (h.collarSlice I) := by
  exact h.isOpenEmbedding_toFun.isOpenMap _ (isOpen_univ.prod hI)

theorem mem_collarSlice_iff_time (I : Set ℝ) (x : h.range) :
    x.1 ∈ h.collarSlice I ↔ h.time x ∈ I := by
  constructor
  · rintro ⟨p, hpI, hp⟩
    have hpx : (⟨h.toFun p, ⟨p, rfl⟩⟩ : h.range) = x := Subtype.ext hp
    rw [← hpx, h.time_mk]
    exact hpI.2
  · intro ht
    let p := h.homeomorphRange.symm x
    refine ⟨p, ⟨trivial, ht⟩, ?_⟩
    exact congrArg Subtype.val (h.homeomorphRange.apply_symm_apply x)

noncomputable def negativeCover [Nonempty S] : Set X :=
  h.negativeSide ∪ h.collarSlice (Set.Iio 1)

noncomputable def positiveCover [Nonempty S] : Set X :=
  h.positiveSide ∪ h.collarSlice (Set.Ioi (-1))

theorem isOpen_negativeCover [CompactSpace S] [Nonempty S] [T2Space X]
    [LocallyPathConnectedSpace X] : IsOpen h.negativeCover :=
  h.isOpen_negativeSide.union (h.isOpen_collarSlice isOpen_Iio)

theorem isOpen_positiveCover [CompactSpace S] [Nonempty S] [T2Space X]
    [LocallyPathConnectedSpace X] : IsOpen h.positiveCover :=
  h.isOpen_positiveSide.union (h.isOpen_collarSlice isOpen_Ioi)

theorem negativeCover_union_positiveCover
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] :
    h.negativeCover ∪ h.positiveCover = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ h.complement
  · rw [h.complement_eq_negativeSide_union_positiveSide] at hx
    rcases hx with hxn | hxp
    · exact Or.inl (Or.inl hxn)
    · exact Or.inr (Or.inl hxp)
  · have hxZ : x ∈ Set.range e := by
      simpa only [complement, Set.mem_compl_iff, not_not] using hx
    rcases hxZ with ⟨s, rfl⟩
    apply Or.inl
    apply Or.inr
    refine ⟨(s, 0), ⟨trivial, by norm_num⟩, ?_⟩
    exact h.zero_eq s

theorem time_neg_of_mem_negativeSide_range
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X]
    (x : h.range) (hx : x.1 ∈ h.negativeSide) : h.time x < 0 := by
  have hxU : x.1 ∈ h.complement := h.negativeSide_subset_complement hx
  have hne := h.time_ne_zero_of_mem_complement x hxU
  rcases lt_or_gt_of_ne hne with ht | ht
  · exact ht
  · exfalso
    have hxp : x.1 ∈ h.positiveSide := by
      let p := h.homeomorphRange.symm x
      have hp : h.toFun p = x.1 :=
        congrArg Subtype.val (h.homeomorphRange.apply_symm_apply x)
      change p.2 > 0 at ht
      rw [← hp]
      exact h.toFun_mem_positiveSide_of_pos p.1 ht
    exact Set.disjoint_left.mp h.disjoint_negativeSide_positiveSide hx hxp

theorem time_pos_of_mem_positiveSide_range
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X]
    (x : h.range) (hx : x.1 ∈ h.positiveSide) : 0 < h.time x := by
  have hxU : x.1 ∈ h.complement := h.positiveSide_subset_complement hx
  have hne := h.time_ne_zero_of_mem_complement x hxU
  rcases lt_or_gt_of_ne hne with ht | ht
  · exfalso
    have hxn : x.1 ∈ h.negativeSide := by
      let p := h.homeomorphRange.symm x
      have hp : h.toFun p = x.1 :=
        congrArg Subtype.val (h.homeomorphRange.apply_symm_apply x)
      change p.2 < 0 at ht
      rw [← hp]
      exact h.toFun_mem_negativeSide_of_neg p.1 ht
    exact Set.disjoint_left.mp h.disjoint_negativeSide_positiveSide hxn hx
  · exact ht

theorem negativeCover_inter_positiveCover
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    h.negativeCover ∩ h.positiveCover = h.collarSlice (Set.Ioo (-1) 1) := by
  ext x
  constructor
  · rintro ⟨hxn | hxlt, hxp | hxgt⟩
    · exact False.elim (Set.disjoint_left.mp h.disjoint_negativeSide_positiveSide hxn hxp)
    · have hxrange : x ∈ h.range := h.collarSlice_subset_range _ hxgt
      have htimeN := h.time_neg_of_mem_negativeSide_range ⟨x, hxrange⟩ hxn
      have htimeGt := (h.mem_collarSlice_iff_time _ ⟨x, hxrange⟩).mp hxgt
      exact (h.mem_collarSlice_iff_time _ ⟨x, hxrange⟩).mpr
        ⟨htimeGt, htimeN.trans (by norm_num)⟩
    · have hxrange : x ∈ h.range := h.collarSlice_subset_range _ hxlt
      have htimeP := h.time_pos_of_mem_positiveSide_range ⟨x, hxrange⟩ hxp
      have htimeLt := (h.mem_collarSlice_iff_time _ ⟨x, hxrange⟩).mp hxlt
      exact (h.mem_collarSlice_iff_time _ ⟨x, hxrange⟩).mpr
        ⟨(by norm_num : (-1 : ℝ) < 0).trans htimeP, htimeLt⟩
    · have hxrange : x ∈ h.range := h.collarSlice_subset_range _ hxlt
      have htimeLt := (h.mem_collarSlice_iff_time _ ⟨x, hxrange⟩).mp hxlt
      have htimeGt := (h.mem_collarSlice_iff_time _ ⟨x, hxrange⟩).mp hxgt
      exact (h.mem_collarSlice_iff_time _ ⟨x, hxrange⟩).mpr ⟨htimeGt, htimeLt⟩
  · intro hx
    have hxlt : x ∈ h.collarSlice (Set.Iio 1) := by
      rcases hx with ⟨p, hp, rfl⟩
      exact ⟨p, ⟨trivial, hp.2.2⟩, rfl⟩
    have hxgt : x ∈ h.collarSlice (Set.Ioi (-1)) := by
      rcases hx with ⟨p, hp, rfl⟩
      exact ⟨p, ⟨trivial, hp.2.1⟩, rfl⟩
    exact ⟨Or.inr hxlt, Or.inr hxgt⟩

noncomputable def collarMiddleHomeomorph
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    S × Set.Ioo (-1 : ℝ) 1 ≃ₜ ↑(h.negativeCover ∩ h.positiveCover) :=
  (((Homeomorph.Set.univ S).symm.prodCongr
      (Homeomorph.refl (Set.Ioo (-1 : ℝ) 1))).trans
    (Homeomorph.Set.prod (Set.univ : Set S) (Set.Ioo (-1 : ℝ) 1)).symm).trans
      ((h.isOpenEmbedding_toFun.toIsEmbedding.homeomorphImage
        (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)).trans
          (Homeomorph.setCongr h.negativeCover_inter_positiveCover.symm))

theorem simplyConnectedSpace_negativeCover_inter_positiveCover
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] [SimplyConnectedSpace S] :
    SimplyConnectedSpace ↑(h.negativeCover ∩ h.positiveCover) := by
  let hinterval : ContractibleSpace (Set.Ioo (-1 : ℝ) 1) :=
    (convex_Ioo (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let _ := hinterval
  let Eprod : S × Set.Ioo (-1 : ℝ) 1 ≃ₕ S :=
    ((ContinuousMap.HomotopyEquiv.refl S).prodCongr
      (ContractibleSpace.hequiv_unit (Set.Ioo (-1 : ℝ) 1)).some).trans
        (Homeomorph.prodUnique S Unit).toHomotopyEquiv
  let E : ↑(h.negativeCover ∩ h.positiveCover) ≃ₕ S :=
    h.collarMiddleHomeomorph.symm.toHomotopyEquiv |>.trans
      Eprod
  exact E.simplyConnectedSpace

theorem isPathConnected_negativeSide [CompactSpace S] [Nonempty S] [T2Space X]
    [LocallyPathConnectedSpace X] : IsPathConnected h.negativeSide := by
  have hconn : IsConnected h.negativeSide :=
    isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn
  let _ : ConnectedSpace h.negativeSide := isConnected_iff_connectedSpace.mp hconn
  let _ : LocallyPathConnectedSpace h.negativeSide := h.isOpen_negativeSide.locallyPathConnectedSpace
  exact isPathConnected_iff_pathConnectedSpace.mpr
    PathConnectedSpace.of_locallyPathConnectedSpace

theorem isPathConnected_positiveSide [CompactSpace S] [Nonempty S] [T2Space X]
    [LocallyPathConnectedSpace X] : IsPathConnected h.positiveSide := by
  have hconn : IsConnected h.positiveSide :=
    isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn
  let _ : ConnectedSpace h.positiveSide := isConnected_iff_connectedSpace.mp hconn
  let _ : LocallyPathConnectedSpace h.positiveSide := h.isOpen_positiveSide.locallyPathConnectedSpace
  exact isPathConnected_iff_pathConnectedSpace.mpr
    PathConnectedSpace.of_locallyPathConnectedSpace

theorem isPathConnected_collarSlice_Iio_one [PathConnectedSpace S] :
    IsPathConnected (h.collarSlice (Set.Iio 1)) := by
  let _ : ContractibleSpace (Set.Iio (1 : ℝ)) :=
    (convex_Iio (1 : ℝ)).contractibleSpace ⟨0, by norm_num⟩
  rw [show h.collarSlice (Set.Iio 1) =
      Set.range (fun q : S × Set.Iio (1 : ℝ) => h.toFun (q.1, q.2.1)) by
    ext x
    simp only [collarSlice, Set.mem_image, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_range]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p.1, ⟨p.2, hp⟩), rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨(p.1, p.2.1), p.2.2, rfl⟩]
  exact isPathConnected_range (h.isOpenEmbedding_toFun.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

theorem isPathConnected_collarSlice_Ioi_neg_one [PathConnectedSpace S] :
    IsPathConnected (h.collarSlice (Set.Ioi (-1))) := by
  let _ : ContractibleSpace (Set.Ioi (-1 : ℝ)) :=
    (convex_Ioi (-1 : ℝ)).contractibleSpace ⟨0, by norm_num⟩
  rw [show h.collarSlice (Set.Ioi (-1)) =
      Set.range (fun q : S × Set.Ioi (-1 : ℝ) => h.toFun (q.1, q.2.1)) by
    ext x
    simp only [collarSlice, Set.mem_image, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_range]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p.1, ⟨p.2, hp⟩), rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨(p.1, p.2.1), p.2.2, rfl⟩]
  exact isPathConnected_range (h.isOpenEmbedding_toFun.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

theorem isPathConnected_negativeCover
    [CompactSpace S] [T2Space X] [LocallyPathConnectedSpace X] [PathConnectedSpace S] :
    IsPathConnected h.negativeCover := by
  apply h.isPathConnected_negativeSide.union h.isPathConnected_collarSlice_Iio_one
  let s : S := Classical.choice inferInstance
  exact ⟨h.toFun (s, -1 / 2),
    h.toFun_mem_negativeSide_of_neg s (by norm_num),
    ⟨(s, -1 / 2), ⟨trivial, by norm_num⟩, rfl⟩⟩

theorem isPathConnected_positiveCover
    [CompactSpace S] [T2Space X] [LocallyPathConnectedSpace X] [PathConnectedSpace S] :
    IsPathConnected h.positiveCover := by
  apply h.isPathConnected_positiveSide.union h.isPathConnected_collarSlice_Ioi_neg_one
  let s : S := Classical.choice inferInstance
  exact ⟨h.toFun (s, 1 / 2),
    h.toFun_mem_positiveSide_of_pos s (by norm_num),
    ⟨(s, 1 / 2), ⟨trivial, by norm_num⟩, rfl⟩⟩

theorem simplyConnectedSpace_negativeCover_and_positiveCover
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] [SimplyConnectedSpace S] :
    SimplyConnectedSpace h.negativeCover ∧ SimplyConnectedSpace h.positiveCover := by
  let _ : PathConnectedSpace h.negativeCover :=
    isPathConnected_iff_pathConnectedSpace.mp h.isPathConnected_negativeCover
  let _ : PathConnectedSpace h.positiveCover :=
    isPathConnected_iff_pathConnectedSpace.mp h.isPathConnected_positiveCover
  let _ : SimplyConnectedSpace ↑(h.negativeCover ∩ h.positiveCover) :=
    h.simplyConnectedSpace_negativeCover_inter_positiveCover
  let s : S := Classical.choice inferInstance
  let x₀ : X := h.toFun (s, 0)
  have hx₀N : x₀ ∈ h.negativeCover := Or.inr ⟨(s, 0), ⟨trivial, by norm_num⟩, rfl⟩
  have hx₀P : x₀ ∈ h.positiveCover := Or.inr ⟨(s, 0), ⟨trivial, by norm_num⟩, rfl⟩
  exact DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_union
    h.negativeCover h.positiveCover h.isOpen_negativeCover h.isOpen_positiveCover
      h.negativeCover_union_positiveCover x₀ ⟨hx₀N, hx₀P⟩

omit h [TopologicalSpace S] [TopologicalSpace X] in
theorem simplyConnectedSpace_of_retract
    {K U : Type*} [TopologicalSpace K] [TopologicalSpace U]
    (i : C(K, U)) (r : C(U, K)) (hri : r.comp i = ContinuousMap.id K)
    [SimplyConnectedSpace U] : SimplyConnectedSpace K := by
  have hr : Function.Surjective r := fun x =>
    ⟨i x, ContinuousMap.congr_fun hri x⟩
  let _ : PathConnectedSpace K := pathConnectedSpace_iff_univ.mpr (by
    rw [← hr.range_eq]
    exact isPathConnected_range r.continuous)
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro x γ
  have hnull : Path.Homotopic (γ.map i.continuous) (Path.refl (i x)) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have hmapped := hnull.map r
  have hx : r (i x) = x := ContinuousMap.congr_fun hri x
  have hcast := hmapped.pathCast hx.symm hx.symm
  have hleft : ((γ.map i.continuous).map r.continuous).cast hx.symm hx.symm = γ := by
    apply Path.ext
    funext t
    exact ContinuousMap.congr_fun hri (γ t)
  have hright : ((Path.refl (i x)).map r.continuous).cast hx.symm hx.symm =
      Path.refl x := by
    apply Path.ext
    funext t
    exact hx
  rw [← hleft, ← hright]
  exact hcast

theorem closure_negativeSide_subset_negativeCover
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    closure h.negativeSide ⊆ h.negativeCover := by
  intro x hx
  have hx' : x ∈ h.negativeSide ∪ Set.range e :=
    (Set.ext_iff.mp h.closure_negativeSide x).mp hx
  rcases hx' with hxn | hxz
  · exact Or.inl hxn
  · rcases hxz with ⟨s, hs⟩
    exact Or.inr ⟨(s, 0), ⟨trivial, by norm_num⟩, (h.zero_eq s).trans hs⟩

theorem closure_positiveSide_subset_positiveCover
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    closure h.positiveSide ⊆ h.positiveCover := by
  intro x hx
  have hx' : x ∈ h.positiveSide ∪ Set.range e :=
    (Set.ext_iff.mp h.closure_positiveSide x).mp hx
  rcases hx' with hxp | hxz
  · exact Or.inl hxp
  · rcases hxz with ⟨s, hs⟩
    exact Or.inr ⟨(s, 0), ⟨trivial, by norm_num⟩, (h.zero_eq s).trans hs⟩

def negativeClosureInclusion
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    C(closure h.negativeSide, h.negativeCover) where
  toFun x := ⟨x.1, h.closure_negativeSide_subset_negativeCover x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def positiveClosureInclusion
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    C(closure h.positiveSide, h.positiveCover) where
  toFun x := ⟨x.1, h.closure_positiveSide_subset_positiveCover x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

structure SideRetractions
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] where
  negative : C(h.negativeCover, closure h.negativeSide)
  negative_comp_inclusion : negative.comp h.negativeClosureInclusion =
    ContinuousMap.id (closure h.negativeSide)
  positive : C(h.positiveCover, closure h.positiveSide)
  positive_comp_inclusion : positive.comp h.positiveClosureInclusion =
    ContinuousMap.id (closure h.positiveSide)

theorem simplyConnectedSpace_closure_sides_of_retractions
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] [SimplyConnectedSpace S]
    (r : SideRetractions h) :
    SimplyConnectedSpace (closure h.negativeSide) ∧
      SimplyConnectedSpace (closure h.positiveSide) := by
  rcases h.simplyConnectedSpace_negativeCover_and_positiveCover with ⟨hneg, hpos⟩
  let _ : SimplyConnectedSpace h.negativeCover := hneg
  let _ : SimplyConnectedSpace h.positiveCover := hpos
  exact ⟨simplyConnectedSpace_of_retract h.negativeClosureInclusion r.negative
      r.negative_comp_inclusion,
    simplyConnectedSpace_of_retract h.positiveClosureInclusion r.positive
      r.positive_comp_inclusion⟩

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
