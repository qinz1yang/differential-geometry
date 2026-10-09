/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcComplementAccess
import DifferentialGeometry.Topology.PiecewiseLinear.ArcFirstBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalArcBall
import DifferentialGeometry.External.Schoenflies.ArcComplement
import DifferentialGeometry.External.Schoenflies.MatchedArc

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem IsPLHomeomorphOn.exists_crosscut_extension_of_boundary_singleton
    {D A : Set Plane} (hD : IsPLBall 2 D) {η : ℝ → Plane}
    (hη : IsPLHomeomorphOn η (Icc 0 1) A) (hAD : A ⊆ D)
    (hmeet : A ∩ frontier D = {η 0}) :
    ∃ (Q R : Set Plane) (γ : ℝ → Plane),
      IsPLHomeomorphOn γ (Icc 0 1) Q ∧ Q = A ∪ R ∧ Q ⊆ D ∧
      A ∩ R = {η 1} ∧ γ 0 = η 0 ∧ γ (1 / 2) = η 1 ∧
      γ '' Icc (0 : ℝ) (1 / 2) = A ∧ Q ∩ frontier D = {γ 0, γ 1} := by
  have hA : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hη
  have harc : Schoenflies.IsArcBetween A (η 0) (η 1) :=
    ⟨η, hη.isPiecewiseAffineOn.continuousOn, hη.bijOn.injOn, hη.image_eq, rfl, rfl⟩
  have hη0 : η 0 ∈ A := hη.bijOn.mapsTo (by norm_num)
  have hη1 : η 1 ∈ A := hη.bijOn.mapsTo (by norm_num)
  have h1int : η 1 ∈ interior D := by
    apply (mem_interior_iff_notMem_frontier (hAD hη1)).mpr
    intro hfr
    exact harc.ne (hmeet.subset ⟨hη1, hfr⟩).symm
  obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem D).mp hD.isPolyhedron.isCompact.ne_univ
  have hzA : z ∉ A := fun h => hz (hAD h)
  have h1z : η 1 ≠ z := fun heq => hz (heq ▸ hAD hη1)
  obtain ⟨P, hPpoly, hParc, hPavoid⟩ := Schoenflies.exists_simple_arc_of_polyAccessible
    hA.isPolyhedron.isClosed.isOpen_compl (Schoenflies.arc_complement harc.isArc).isPreconnected
    h1z (harc.reverse.polyAccessible_compl_left (isPolygonal_of_isPLBall_one hA))
    (Schoenflies.polyAccessible_of_mem hzA)
  obtain ⟨δ, hδ, hδ0, hδ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween
    (isPLBall_one_of_isArcBetween_of_isPolygonal hParc hPpoly) hParc
  obtain ⟨R, α, hα, hRPD, hα0, hα1, hRfr⟩ := hδ.exists_initial_subarc_to_frontier
    hD.isPolyhedron.isClosed (hδ0.symm ▸ h1int)
    (by rw [hδ1]; exact fun h => hz (interior_subset h))
  have hαstart : α 0 = η 1 := hα0.trans hδ0
  have hAR : A ∩ R = {η 1} := by
    apply Subset.antisymm
    · rintro x ⟨hxA, hxR⟩
      by_contra hx1
      have hxz : x ≠ z := fun heq => hzA (heq ▸ hxA)
      exact hPavoid ⟨(hRPD hxR).1, by simp only [mem_insert_iff, mem_singleton_iff]; tauto⟩ hxA
    · rintro _ rfl
      exact ⟨hη1, hαstart ▸ hα.bijOn.mapsTo (by norm_num)⟩
  obtain ⟨γ, hγ, hγ0, hγmid, hγ1⟩ :=
    exists_isPLHomeomorphOn_Icc_concat hη hα hαstart hAR
  refine ⟨A ∪ R, R, γ, hγ, rfl, union_subset hAD (hRPD.trans inter_subset_right),
    hAR, hγ0, hγmid, ?_, ?_⟩
  · have hγarc : Schoenflies.IsArcBetween (A ∪ R) (γ 0) (γ 1) :=
      ⟨γ, hγ.isPiecewiseAffineOn.continuousOn, hγ.bijOn.injOn, hγ.image_eq, rfl, rfl⟩
    have hprefix : Schoenflies.IsArcBetween (γ '' Icc (0 : ℝ) (1 / 2)) (η 0) (η 1) := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), hγ0, hγmid] using
        Schoenflies.isArcBetween_subarc_of_injOn_I hγ.isPiecewiseAffineOn.continuousOn
          hγ.bijOn.injOn (by norm_num : (0 : ℝ) ∈ Icc 0 1)
          (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) ≠ 1 / 2)
    exact (harc.eq_of_subset_arc hprefix hγarc subset_union_left
      ((image_mono (Icc_subset_Icc le_rfl (by norm_num))).trans hγ.image_eq.subset)).symm
  · rw [union_inter_distrib_right, hmeet, hRfr, hγ0, hγ1]
    rfl

end DifferentialGeometry.Topology.PiecewiseLinear
