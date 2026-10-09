/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Connected.Clopen

open Set

namespace DifferentialGeometry.Topology

theorem isPreconnected_left_of_isClosed_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hunion : IsPreconnected (A ∪ B))
    (hinter : IsPreconnected (A ∩ B)) : IsPreconnected A := by
  have hside (U V : Set X) (hU : IsClosed U) (hV : IsClosed V)
      (hcover : A ⊆ U ∪ V) (hdis : Disjoint U V) (hIU : A ∩ B ⊆ U) :
      A ⊆ U ∨ A ⊆ V := by
    have hcover' : A ∪ B ⊆ (A ∩ U ∪ B) ∪ (A ∩ V) := by
      rintro x (hxA | hxB)
      · rcases hcover hxA with hxU | hxV
        · exact Or.inl (Or.inl ⟨hxA, hxU⟩)
        · exact Or.inr ⟨hxA, hxV⟩
      · exact Or.inl (Or.inr hxB)
    have hdis' : Disjoint (A ∩ U ∪ B) (A ∩ V) := by
      apply disjoint_left.mpr
      rintro x (hx | hx) hy
      · exact disjoint_left.mp hdis hx.2 hy.2
      · exact disjoint_left.mp hdis (hIU ⟨hy.1, hx⟩) hy.2
    rcases (isPreconnected_iff_subset_of_fully_disjoint_closed (hA.union hB)).mp hunion
      (A ∩ U ∪ B) (A ∩ V) ((hA.inter hU).union hB) (hA.inter hV) hcover' hdis' with h | h
    · left
      intro x hx
      rcases h (Or.inl hx) with hxU | hxB
      · exact hxU.2
      · exact hIU ⟨hx, hxB⟩
    · exact Or.inr (fun _ hx => (h (Or.inl hx)).2)
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hA).mpr
  intro U V hU hV hcover hdis
  have hcoverI : A ∩ B ⊆ U ∪ V := inter_subset_left.trans hcover
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed (hA.inter hB)).mp hinter
    U V hU hV hcoverI hdis with hIU | hIV
  · exact hside U V hU hV hcover hdis hIU
  · exact (hside V U hV hU (hcover.trans (by rw [union_comm])) hdis.symm hIV).symm

theorem connectedComponentIn_sdiff_inter_eq_sdiff
    {X : Type*} [TopologicalSpace X] {A B : Set X} {x : X}
    (hA : IsClosed A) (hB : IsClosed B) (hconn : IsPreconnected (A \ B)) (hx : x ∈ A \ B) :
    connectedComponentIn ((A ∪ B) \ (A ∩ B)) x = A \ B := by
  have hsub : A \ B ⊆ (A ∪ B) \ (A ∩ B) := fun _ hy =>
    ⟨Or.inl hy.1, fun hz => hy.2 hz.2⟩
  have hxC := mem_connectedComponentIn (hsub hx)
  apply Subset.antisymm _ (hconn.subset_connectedComponentIn hx hsub)
  intro y hy
  have hyU := connectedComponentIn_subset ((A ∪ B) \ (A ∩ B)) x hy
  have hyA : y ∈ A := by
    by_contra hynot
    obtain ⟨z, hz, hzA, hzB⟩ := isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn
      A B hA hB ((connectedComponentIn_subset _ _).trans sdiff_subset)
      ⟨x, hxC, hx.1⟩ ⟨y, hy, hyU.1.resolve_left hynot⟩
    exact (connectedComponentIn_subset _ _ hz).2 ⟨hzA, hzB⟩
  exact ⟨hyA, fun hyB => hyU.2 ⟨hyA, hyB⟩⟩

theorem isPreconnected_inter_connectedComponentIn
    {X : Type*} [TopologicalSpace X] {S N : Set X} (hS : IsPreconnected S)
    (hSN : S ⊆ N) (x : X) : IsPreconnected (S ∩ connectedComponentIn N x) := by
  by_cases hne : (S ∩ connectedComponentIn N x).Nonempty
  · obtain ⟨y, hyS, hyC⟩ := hne
    have hsub := hS.subset_connectedComponentIn hyS hSN
    rw [← connectedComponentIn_eq hyC] at hsub
    rwa [inter_eq_left.mpr hsub]
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty

theorem connectedComponentIn_union_inter_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hinter : IsPreconnected (A ∩ B)) {x : X} (hx : x ∈ A) :
    connectedComponentIn (A ∪ B) x ∩ A = connectedComponentIn A x := by
  let C := connectedComponentIn (A ∪ B) x
  let P := ((↑) : C → X) ⁻¹' A
  let Q := ((↑) : C → X) ⁻¹' B
  have hP : IsClosed P := hA.preimage continuous_subtype_val
  have hQ : IsClosed Q := hB.preimage continuous_subtype_val
  have hcover : P ∪ Q = univ := eq_univ_of_forall fun y =>
    connectedComponentIn_subset (A ∪ B) x y.property
  have hconn : IsPreconnected (P ∪ Q) := by
    rw [hcover]
    let _ : PreconnectedSpace C := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
    exact isPreconnected_univ
  have hPQ : IsPreconnected (P ∩ Q) := by
    change IsPreconnected ((((↑) : C → X) ⁻¹' A) ∩ (((↑) : C → X) ⁻¹' B))
    rw [← preimage_inter, ← _root_.Topology.IsInducing.subtypeVal.isPreconnected_image,
      Subtype.image_preimage_coe, inter_comm]
    exact isPreconnected_inter_connectedComponentIn hinter
      (inter_subset_left.trans subset_union_left) x
  have hPc := isPreconnected_left_of_isClosed_union hP hQ hconn hPQ
  have hCA : IsPreconnected (C ∩ A) := by
    simpa only [P, Subtype.image_preimage_coe] using
      (_root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mpr hPc)
  apply Subset.antisymm
  · exact hCA.subset_connectedComponentIn ⟨mem_connectedComponentIn (Or.inl hx), hx⟩
      inter_subset_right
  · exact fun y hy => ⟨connectedComponentIn_mono x subset_union_left hy,
      connectedComponentIn_subset A x hy⟩

theorem closure_connectedComponentIn_sdiff_inter_eq_or_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} {x : X}
    (hA : IsClosed A) (hB : IsClosed B)
    (hconnA : IsPreconnected (A \ B)) (hconnB : IsPreconnected (B \ A))
    (hclA : closure (A \ B) = A) (hclB : closure (B \ A) = B)
    (hx : x ∈ (A ∪ B) \ (A ∩ B)) :
    closure (connectedComponentIn ((A ∪ B) \ (A ∩ B)) x) = A ∨
      closure (connectedComponentIn ((A ∪ B) \ (A ∩ B)) x) = B := by
  rcases hx.1 with hxA | hxB
  · exact Or.inl ((congrArg closure (connectedComponentIn_sdiff_inter_eq_sdiff hA hB
      hconnA ⟨hxA, fun h => hx.2 ⟨hxA, h⟩⟩)).trans hclA)
  · right
    rw [union_comm A B, inter_comm A B]
    exact (congrArg closure (connectedComponentIn_sdiff_inter_eq_sdiff hB hA
      hconnB ⟨hxB, fun h => hx.2 ⟨h, hxB⟩⟩)).trans hclB

theorem interior_eq_compl_of_closure_sdiff_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hcover : A ∪ B = univ) (hB : closure (B \ A) = B) : interior A = Bᶜ := by
  have hcomp : Aᶜ = B \ A := by
    ext x
    constructor
    · intro hx
      exact ⟨(hcover.symm ▸ mem_univ x : x ∈ A ∪ B).resolve_left hx, hx⟩
    · exact fun hx => hx.2
  rw [interior_eq_compl_closure_compl, hcomp, hB]

theorem closure_interior_eq_of_closure_sdiff_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hcover : A ∪ B = univ) (hA : closure (A \ B) = A)
    (hB : closure (B \ A) = B) : closure (interior A) = A := by
  have hcomp : Bᶜ = A \ B := by
    ext x
    constructor
    · intro hx
      exact ⟨(hcover.symm ▸ mem_univ x : x ∈ A ∪ B).resolve_right hx, hx⟩
    · exact fun hx => hx.2
  rw [interior_eq_compl_of_closure_sdiff_eq hcover hB, hcomp, hA]

theorem frontier_eq_inter_of_closure_sdiff_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hcover : A ∪ B = univ) (hA : closure (A \ B) = A)
    (hB : closure (B \ A) = B) : frontier A = A ∩ B := by
  have hclosed : IsClosed A := hA ▸ isClosed_closure
  rw [hclosed.frontier_eq, interior_eq_compl_of_closure_sdiff_eq hcover hB, sdiff_compl]

end DifferentialGeometry.Topology
