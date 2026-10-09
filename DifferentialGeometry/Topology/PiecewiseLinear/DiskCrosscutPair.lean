/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskCircleStep

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem exists_crosscut_pair_with_parameterized_arcs {D A : Set Plane}
    (hD : IsPLBall 2 D) (hA : IsPLBall 1 A) {p q : Plane}
    (hc : Schoenflies.IsCrosscut (frontier D) A p q) :
    ∃ (U V R S : Set Plane) (γ δ : ℝ → Plane),
      IsPLBall 2 U ∧ IsPLBall 2 V ∧
      IsPLHomeomorphOn γ (Icc 0 1) R ∧ IsPLHomeomorphOn δ (Icc 0 1) S ∧
      γ 0 = p ∧ γ 1 = q ∧ δ 0 = p ∧ δ 1 = q ∧
      U ∪ V = D ∧ U ∩ V = A ∧ frontier U = A ∪ R ∧ frontier V = A ∪ S ∧
      U ∩ frontier D = R ∧ V ∩ frontier D = S ∧ R ∪ S = frontier D ∧ R ∩ S = {p, q} := by
  obtain ⟨R, S, hcut, hR, hS⟩ := exists_isCutPair_isPLBall_of_isPLSphere_one
    hD.isPLSphere_frontier hc.left_mem hc.right_mem hc.arc.ne
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hR hcut.fst
  obtain ⟨δ, hδ, hδ0, hδ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hS hcut.snd
  have hRA := isPLSphere_one_union_of_isCrosscut hD.isPLSphere_frontier hA hc hcut
  have hSA := isPLSphere_one_union_of_isCrosscut hD.isPLSphere_frontier hA hc hcut.symm
  let U := closure (Schoenflies.inside (R ∪ A))
  let V := closure (Schoenflies.inside (S ∪ A))
  have hU : IsPLBall 2 U := isPLBall_closure_inside_of_isPLSphere_one hRA
  have hV : IsPLBall 2 V := isPLBall_closure_inside_of_isPLSphere_one hSA
  have hUV : U ∪ V = D := by
    rw [show U ∪ V = closure (Schoenflies.inside (frontier D)) from
      PlanarJordan.closure_inside_union_of_isCrosscut hc hcut, ← hD.interior_eq_inside_frontier]
    exact hD.closure_interior
  refine ⟨U, V, R, S, γ, δ, hU, hV, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hUV,
    PlanarJordan.closure_inside_inter_of_isCrosscut hc hcut, ?_, ?_, ?_, ?_,
    hcut.union_eq, hcut.inter_eq⟩
  · exact (frontier_closure_inside_of_isPLSphere_one hRA).trans (union_comm R A)
  · exact (frontier_closure_inside_of_isPLSphere_one hSA).trans (union_comm S A)
  · exact hc.closure_side_inter (fun _ => Schoenflies.jordan_curve_theorem) hcut
  · exact hc.closure_side_inter (fun _ => Schoenflies.jordan_curve_theorem) hcut.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_disk_pair_with_boundary_arcs_of_proper_arc {D A : Set E}
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    {η : ℝ → E} (hη : IsPLHomeomorphOn η (Icc 0 1) A) (hAD : A ⊆ D)
    (hmeet : A ∩ (r '' stdSimplexBoundary 2) = {η 0, η 1}) :
    ∃ (U V R S : Set E) (u v : (Fin 3 → ℝ) → E) (γ δ : ℝ → E),
      IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) U ∧
      IsPLHomeomorphOn v (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) V ∧
      IsPLHomeomorphOn γ (Icc 0 1) R ∧ IsPLHomeomorphOn δ (Icc 0 1) S ∧
      γ 0 = η 0 ∧ γ 1 = η 1 ∧ δ 0 = η 0 ∧ δ 1 = η 1 ∧
      U ∪ V = D ∧ U ∩ V = A ∧ u '' stdSimplexBoundary 2 = A ∪ R ∧
      v '' stdSimplexBoundary 2 = A ∪ S ∧ U ∩ (r '' stdSimplexBoundary 2) = R ∧
      V ∩ (r '' stdSimplexBoundary 2) = S ∧ R ∪ S = r '' stdSimplexBoundary 2 ∧
      R ∩ S = {η 0, η 1} := by
  classical
  obtain ⟨P, ρ, hP, hρ, hρbd⟩ := hr.exists_planarModel
  let σ := Function.invFunOn ρ P
  have hA : IsPLBall 1 A := (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hη
  let B := σ '' A
  have hη' : IsPLHomeomorphOn (σ ∘ η) (Icc 0 1) B :=
    hη.trans (hρ.symm.restrict hA.isPolyhedron hAD)
  have hBP : B ⊆ P := (image_mono hAD).trans hρ.symm.image_eq.subset
  have hbdD : r '' stdSimplexBoundary 2 ⊆ D := by
    rw [← hr.image_eq]
    exact image_mono fun x hx => hx.1
  have hσbd : σ '' (r '' stdSimplexBoundary 2) = frontier P := by
    rw [← hρbd, image_image]
    exact (show EqOn (σ ∘ ρ) id (frontier P) from fun x hx =>
      hρ.bijOn.invOn_invFunOn.1 (hP.isPolyhedron.isClosed.frontier_subset hx)).image_eq.trans
        (image_id _)
  have hBm : B ∩ frontier P = {σ (η 0), σ (η 1)} := by
    rw [← hσbd, ← hρ.symm.bijOn.injOn.image_inter hAD hbdD, hmeet, image_pair]
  have hη0 : η 0 ∈ A := hη.bijOn.mapsTo (by norm_num)
  have hη1 : η 1 ∈ A := hη.bijOn.mapsTo (by norm_num)
  have hinv : ∀ x ∈ A, ρ (σ x) = x := fun x hx => hρ.bijOn.invOn_invFunOn.2 (hAD hx)
  have hρB : ρ '' B = A := by
    rw [show B = σ '' A from rfl, image_image]
    exact (show EqOn (ρ ∘ σ) id A from hinv).image_eq.trans (image_id _)
  have hopen : (σ ∘ η) '' Ioo 0 1 ⊆ interior P := by
    rintro x ⟨t, ht, rfl⟩
    have hxB := hη'.bijOn.mapsTo (Ioo_subset_Icc_self ht)
    apply (mem_interior_iff_notMem_frontier (hBP hxB)).mpr
    intro hxfr
    have hx := hBm.subset ⟨hxB, hxfr⟩
    rcases hx with hx | hx
    · have ht0 := hη'.bijOn.injOn (Ioo_subset_Icc_self ht) (by norm_num) hx
      exact ht.1.ne' ht0
    · have ht1 := hη'.bijOn.injOn (Ioo_subset_Icc_self ht) (by norm_num) hx
      exact ht.2.ne ht1
  have hc := hη'.isCrosscut_of_image_Ioo_subset_interior hP
    (hBm.symm.subset (by simp)).2 (hBm.symm.subset (by simp)).2 hopen
  obtain ⟨U, V, R, S, γ, δ, hU, hV, hγ, hδ, hγ0, hγ1, hδ0, hδ1,
    hUV, hUiV, hUbd, hVbd, hUR, hVS, hRS, hRiS⟩ :=
    exists_crosscut_pair_with_parameterized_arcs hP
      ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hη') hc
  have hUP : U ⊆ P := subset_union_left.trans hUV.subset
  have hVP : V ⊆ P := subset_union_right.trans hUV.subset
  have hRP : R ⊆ P := hUR.symm.subset.trans (inter_subset_left.trans hUP)
  have hSP : S ⊆ P := hVS.symm.subset.trans (inter_subset_left.trans hVP)
  have hR : IsPLBall 1 R := (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ
  have hS : IsPLBall 1 S := (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hδ
  have hUPoly := hU.isPolyhedron
  have hVPoly := hV.isPolyhedron
  obtain ⟨u, hu⟩ := hU
  obtain ⟨v, hv⟩ := hV
  have hu' := hu.trans (hρ.restrict hUPoly hUP)
  have hv' := hv.trans (hρ.restrict hVPoly hVP)
  have hγ' := hγ.trans (hρ.restrict hR.isPolyhedron hRP)
  have hδ' := hδ.trans (hρ.restrict hS.isPolyhedron hSP)
  refine ⟨ρ '' U, ρ '' V, ρ '' R, ρ '' S, ρ ∘ u, ρ ∘ v, ρ ∘ γ, ρ ∘ δ,
    hu', hv', hγ', hδ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ρ (γ 0) = η 0
    rw [hγ0]
    exact hinv _ hη0
  · change ρ (γ 1) = η 1
    rw [hγ1]
    exact hinv _ hη1
  · change ρ (δ 0) = η 0
    rw [hδ0]
    exact hinv _ hη0
  · change ρ (δ 1) = η 1
    rw [hδ1]
    exact hinv _ hη1
  · rw [← image_union, hUV, hρ.image_eq]
  · rw [← hρ.bijOn.injOn.image_inter hUP hVP, hUiV, hρB]
  · rw [image_comp, hu.image_stdSimplexBoundary, hUbd, image_union, hρB]
  · rw [image_comp, hv.image_stdSimplexBoundary, hVbd, image_union, hρB]
  · rw [← hρbd, ← hρ.bijOn.injOn.image_inter hUP hP.isPolyhedron.isClosed.frontier_subset, hUR]
  · rw [← hρbd, ← hρ.bijOn.injOn.image_inter hVP hP.isPolyhedron.isClosed.frontier_subset, hVS]
  · rw [← image_union, hRS, hρbd]
  · rw [← hρ.bijOn.injOn.image_inter hRP hSP, hRiS, image_pair]
    change {ρ (σ (η 0)), ρ (σ (η 1))} = {η 0, η 1}
    rw [hinv _ hη0, hinv _ hη1]

end DifferentialGeometry.Topology.PiecewiseLinear
