/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryArcRibbon
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskArc
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDiskBoundaryTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C A B D U : Set E} {a b : E}

open Classical in
theorem IsBridgeDisk.boundary_eq (h : IsBridgeDisk C A B a b)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hKB : K.space = B) :
    (boundaryComplex 2 K).space = A ∪ (B ∩ frontier C) := by
  obtain ⟨q, hq, _, hbase, hsides, _, _⟩ := h
  rw [← hq.image_stdSimplexBoundary_eq_boundaryComplex K hKB,
    ← standardTriangleBase_union_sides, image_union, hbase, ← hsides]

theorem IsBridgeDisk.isPLBall_inter_frontier (h : IsBridgeDisk C A B a b) :
    IsPLBall 1 (B ∩ frontier C) := by
  classical
  have hcopy := h
  obtain ⟨q, hq, _, _, _, _, _⟩ := hcopy
  have hB : IsPLBall 2 B := ⟨q, hq⟩
  obtain ⟨K, hKfin, hKB⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := h.exists_parametrization
  have hbd := h.boundary_eq K hKB
  have hAβ : A ∩ (B ∩ frontier C) = {a, b} := by
    have hAB : A ⊆ B := (subset_union_left.trans hbd.symm.subset).trans
      ((boundaryComplex_space_subset 2 K).trans hKB.subset)
    calc
      A ∩ (B ∩ frontier C) = A ∩ frontier C := by
        ext x
        exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hAB hx.1, hx.2⟩⟩
      _ = {a, b} := h.inter_frontier
  obtain ⟨R, δ, hδ, _, _, hAR, hmeet⟩ := exists_complementary_arc_of_isPLSphere_one
    (isPLSphere_boundaryComplex_space_of_isPLBall K (hKB.symm ▸ hB)) hγ
    (hbd.symm ▸ subset_union_left)
  have hR : R = B ∩ frontier C := by
    rw [hγ0, hγ1] at hmeet
    ext x
    have hc := Set.ext_iff.mp (hAR.trans hbd) x
    have hm := Set.ext_iff.mp (hmeet.trans hAβ.symm) x
    simp only [mem_union, mem_inter_iff] at hc hm
    tauto
  rw [← hR]
  exact (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hδ

open Classical in
theorem IsBridgeDisk.closure_boundary_sdiff_inter_frontier
    (h : IsBridgeDisk C A B a b)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hKB : K.space = B) :
    closure ((boundaryComplex 2 K).space \ (B ∩ frontier C)) = A := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := h.exists_parametrization
  have hbd := h.boundary_eq K hKB
  have hAB : A ⊆ B :=
    (subset_union_left.trans hbd.symm.subset).trans
      ((boundaryComplex_space_subset 2 K).trans hKB.subset)
  have hdiff : (boundaryComplex 2 K).space \ (B ∩ frontier C) = A \ {a, b} := by
    rw [hbd]
    ext x
    have hmeet := Set.ext_iff.mp h.inter_frontier x
    simp only [mem_sdiff, mem_union, mem_inter_iff] at hmeet ⊢
    constructor
    · rintro ⟨hxA | hxβ, hnot⟩
      · exact ⟨hxA, fun hx => hnot ⟨hAB hxA, (hmeet.mpr hx).2⟩⟩
      · exact (hnot hxβ).elim
    · rintro ⟨hxA, hnot⟩
      exact ⟨Or.inl hxA, fun hxβ => hnot (hmeet.mp ⟨hxA, hxβ.2⟩)⟩
  rw [hdiff, ← hγ0, ← hγ1]
  exact hγ.closure_sdiff_endpoints zero_lt_one

theorem IsBridgeDisk.arc_eq (h : IsBridgeDisk C A B a b)
    {A' : Set E} {a' b' : E} (h' : IsBridgeDisk C A' B a' b') : A = A' := by
  have hcopy := h'
  obtain ⟨q, hq, _, _, _, _, _⟩ := hcopy
  have hB : IsPLBall 2 B := ⟨q, hq⟩
  obtain ⟨K, hKfin, hKB⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  exact (h.closure_boundary_sdiff_inter_frontier K hKB).symm.trans
    (h'.closure_boundary_sdiff_inter_frontier K hKB)

open Classical in
theorem IsBridgeDisk.exists_isPLHomeomorphOn_to_subdisk
    (h : IsBridgeDisk C A B a b) (hC : IsPolyhedron C)
    (hD : IsPLBall 2 D) (hDB : D ⊆ B) (hβD : B ∩ frontier C ⊆ D) :
    ∃ e : E ≃ₜ E, IsPLHomeomorphOn e univ univ ∧ EqOn e id Cᶜ ∧
      EqOn e id (frontier C) ∧ e '' C = C ∧ IsBridgeDisk C (e '' A) D a b := by
  have hcopy := h
  obtain ⟨q, hq, hBC, _, _, _, _⟩ := hcopy
  have hB : IsPLBall 2 B := ⟨q, hq⟩
  obtain ⟨K, hKfin, hKB⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hbd := h.boundary_eq K hKB
  have hβK : B ∩ frontier C ⊆ (boundaryComplex 2 K).space :=
    subset_union_right.trans hbd.symm.subset
  have hinside : K.space \ (B ∩ frontier C) ⊆ interior C := by
    rintro x ⟨hxK, hxβ⟩
    have hxB := hKB.subset hxK
    exact (mem_interior_iff_notMem_frontier (hBC hxB)).mpr fun hx => hxβ ⟨hxB, hx⟩
  obtain ⟨L, hLfin, hL, hLD, e, he, hfix, hfront, heC, hebd⟩ :=
    exists_isPLHomeomorphOn_disk_boundary_to_subdisk K (hKB.symm ▸ hB) hD
      (hDB.trans hKB.symm.subset) hβK hβD hC hinside
  let _ : Finite L.faces := hLfin.to_subtype
  have heβ : e '' (B ∩ frontier C) = B ∩ frontier C := by
    exact (show EqOn e id (B ∩ frontier C) from fun _ hx => hfront hx.2).image_eq.trans
      (image_id _)
  have hefront : e '' frontier C = frontier C := hfront.image_eq.trans (image_id _)
  have hLβ : L.space ∩ frontier C = B ∩ frontier C := by
    rw [hLD]
    exact Subset.antisymm (fun _ hx => ⟨hDB hx.1, hx.2⟩) fun _ hx => ⟨hβD hx, hx.2⟩
  have hbdL : (boundaryComplex 2 L).space = e '' A ∪ (B ∩ frontier C) := by
    rw [← hebd, hbd, image_union, heβ]
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := h.exists_parametrization
  have hγe := hγ.trans (he.restrict
    ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ).isPolyhedron (subset_univ _))
  have ha : a ∈ frontier C := (h.inter_frontier.symm.subset (Or.inl rfl)).2
  have hb : b ∈ frontier C := (h.inter_frontier.symm.subset (Or.inr rfl)).2
  have hγe0 : (e ∘ γ) 0 = a := by simp only [Function.comp_apply, hγ0, hfront ha, id_eq]
  have hγe1 : (e ∘ γ) 1 = b := by simp only [Function.comp_apply, hγ1, hfront hb, id_eq]
  have hends : e '' A ∩ frontier C = {(e ∘ γ) 0, (e ∘ γ) 1} := by
    rw [← hefront, ← image_inter e.injective, h.inter_frontier, image_pair,
      hfront ha, hfront hb, hγe0, hγe1]
    rfl
  have hnew := exists_isBridgeDisk_of_boundary_cover L hL (hLD.subset.trans (hDB.trans hBC))
    hγe (subset_union_left.trans hbdL.symm.subset)
    (hLβ.subset.trans (subset_union_right.trans hbdL.symm.subset))
    (hbdL.subset.trans (union_subset_union_right _ inter_subset_right)) hends
  rw [hLD, hγe0, hγe1] at hnew
  exact ⟨e, he, hfix, hfront, heC, hnew⟩

theorem IsBridgeDisk.exists_isPLHomeomorphOn_map_arc_to_subdisk
    (h : IsBridgeDisk C A B a b) (hC : IsPolyhedron C) {A' : Set E}
    (h' : IsBridgeDisk C A' D a b) (hDB : D ⊆ B) (hβD : B ∩ frontier C ⊆ D) :
    ∃ e : E ≃ₜ E, IsPLHomeomorphOn e univ univ ∧ EqOn e id Cᶜ ∧
      EqOn e id (frontier C) ∧ e '' C = C ∧ e '' A = A' := by
  have hcopy := h'
  obtain ⟨q, hq, _, _, _, _, _⟩ := hcopy
  obtain ⟨e, he, hfix, hfront, heC, hnew⟩ :=
    h.exists_isPLHomeomorphOn_to_subdisk hC ⟨q, hq⟩ hDB hβD
  exact ⟨e, he, hfix, hfront, heC, hnew.arc_eq h'⟩

theorem IsBridgeDisk.exists_isPLHomeomorphOn_arc_subset_open
    (h : IsBridgeDisk C A B a b) (hC : IsPolyhedron C)
    (hU : IsOpen U) (hβU : B ∩ frontier C ⊆ U) :
    ∃ (D : Set E) (e : E ≃ₜ E), IsPLBall 2 D ∧ D ⊆ B ∩ U ∧
      B ∩ frontier C ⊆ D ∧ D ∈ 𝓝ˢ[B] (B ∩ frontier C) ∧
      IsPLHomeomorphOn e univ univ ∧ EqOn e id Cᶜ ∧ EqOn e id (frontier C) ∧
      e '' C = C ∧ e '' A ⊆ U ∧ IsBridgeDisk C (e '' A) D a b := by
  have hcopy := h
  obtain ⟨q, hq, _, _, hβ, _, _⟩ := hcopy
  have hβbd : B ∩ frontier C ⊆ q '' stdSimplexBoundary 2 := by
    rw [hβ]
    exact image_mono (subset_union_right.trans standardTriangleBase_union_sides.subset)
  obtain ⟨D, hD, hDBU, hβD, hDnhds⟩ := hq.exists_isPLBall_neighborhood_boundary_arc
    h.isPLBall_inter_frontier hβbd hU hβU
  obtain ⟨e, he, hfix, hfront, heC, hbridge⟩ :=
    h.exists_isPLHomeomorphOn_to_subdisk hC hD (hDBU.trans inter_subset_left) hβD
  have heAD : e '' A ⊆ D := by
    obtain ⟨qD, hqD, _, hbase, _, _, _⟩ := hbridge
    rw [← hbase]
    exact (image_mono (fun _ hx => hx.1)).trans hqD.image_eq.subset
  exact ⟨D, e, hD, hDBU, hβD, hDnhds, he, hfix, hfront, heC,
    heAD.trans (hDBU.trans inter_subset_right), hbridge⟩

end DifferentialGeometry.Topology.PiecewiseLinear
