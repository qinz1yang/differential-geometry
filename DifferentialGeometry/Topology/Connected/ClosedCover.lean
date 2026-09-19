/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Connected.Clopen

/-!
# Connectedness and components of closed covers
-/

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

end DifferentialGeometry.Topology
