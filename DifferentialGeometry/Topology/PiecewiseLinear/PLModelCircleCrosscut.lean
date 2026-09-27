/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleDiskSubarc
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelArcCuts

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_model_circle_crosscut_ending_on_boundary_arc
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {u v : E3 → M} {P Q D B R : Set E3} {T : Set M} {β : ℝ → E3}
    (hu : IsPLHomeomorphInto 3 u P) (hv : IsPLHomeomorphInto 3 v Q)
    (hQ : IsPLSphere 1 Q) (hQT : v '' Q ⊆ T)
    (hD : IsPolyhedron D) (hDP : D ⊆ P)
    (hboundary : u '' D ∩ closure (T \ u '' D) = u '' (B ∪ R))
    (hβ : IsPLHomeomorphOn β (Icc 0 1) B) (hBP : B ⊆ P) (hRP : R ⊆ P)
    (hBR : B ∩ R = {β 0, β 1})
    (hrel : Disjoint (v '' Q) (u '' B) ∨ u '' B ⊆ v '' Q)
    (hfinite : (v '' Q ∩ u '' R).Finite) (hnot : ¬ v '' Q ⊆ u '' D)
    (hmeet : (v '' Q ∩ (u '' D \ u '' (B ∪ R))).Nonempty) :
    ∃ (A : Set E3) (α : ℝ → E3), IsPLHomeomorphOn α (Icc 0 1) A ∧
      u '' A ⊆ v '' Q ∧ A ⊆ D ∧
      A ∩ (B ∪ R) = {α 0, α 1} ∧ ({α 0, α 1} : Set E3) ⊆ R := by
  classical
  obtain ⟨x, ⟨z, hzQ, hzx⟩, hxD, hxJ⟩ := hmeet
  have hDc : IsClosed (u '' D) :=
    (hD.isCompact.image_of_continuousOn (hu.continuousOn.mono hDP)).isClosed
  have hsource : ∃ (C : Set E3) (η : ℝ → E3), IsPLHomeomorphOn η (Icc 0 1) C ∧
      C ⊆ Q ∧ x ∈ v '' C ∧ (v '' C ∩ u '' (B ∪ R)) ⊆ u '' R ∧
      (v (η 0) ∈ u '' (B ∪ R) ∨ v (η 0) ∉ u '' D) ∧
      (v (η 1) ∈ u '' (B ∪ R) ∨ v (η 1) ∉ u '' D) := by
    rcases hrel with hdis | hBF
    · obtain ⟨K, hK, hKeq⟩ := continuousOn_iff_isClosed.mp hv.continuousOn _ hDc
      have hnotK : ¬ Q ⊆ K := by
        intro hQK
        apply hnot
        rintro y ⟨r, hr, rfl⟩
        exact (hKeq.symm.subset ⟨hQK hr, hr⟩).1
      obtain ⟨C, η, hη, hCQ, hzC, hη0, hη1⟩ :=
        exists_arc_through_point_with_endpoints_outside hQ hK hnotK hzQ
      refine ⟨C, η, hη, hCQ, ⟨z, hzC, hzx⟩, ?_, Or.inr ?_, Or.inr ?_⟩
      · rintro y ⟨hyC, hy⟩
        rw [image_union] at hy
        exact hy.resolve_left fun hyB => disjoint_left.mp hdis (image_mono hCQ hyC) hyB
      · intro h
        exact hη0 (hKeq.subset ⟨h, hCQ (hη.bijOn.mapsTo (by norm_num))⟩).1
      · intro h
        exact hη1 (hKeq.subset ⟨h, hCQ (hη.bijOn.mapsTo (by norm_num))⟩).1
    · let g := Function.invFunOn v Q
      let K := (g ∘ u) '' B
      have hBpoly : IsPolyhedron B :=
        ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hβ).isPolyhedron
      have hcomp : IsPLHomeomorphOn (g ∘ u) B K :=
        (hu.mono_of_polyhedron hBpoly hBP).isPLHomeomorphOn_invFunOn_comp hBpoly hv hBF
      have hright : RightInvOn g v (v '' Q) := hv.injOn.bijOn_image.invOn_invFunOn.2
      have hKQ : K ⊆ Q := by
        rintro y ⟨r, hr, rfl⟩
        exact hv.injOn.bijOn_image.surjOn.mapsTo_invFunOn (hBF ⟨r, hr, rfl⟩)
      have hval : ∀ r ∈ B, v (g (u r)) = u r :=
        fun r hr => hright (hBF ⟨r, hr, rfl⟩)
      have hβ0 : v (((g ∘ u) ∘ β) 0) = u (β 0) :=
        hval _ (hβ.bijOn.mapsTo (by norm_num))
      have hβ1 : v (((g ∘ u) ∘ β) 1) = u (β 1) :=
        hval _ (hβ.bijOn.mapsTo (by norm_num))
      have hKimage : v '' K = u '' B := by
        rw [image_image]
        exact image_congr fun r hr => hval r hr
      obtain ⟨C, η, hη, hη0, hη1, hcover, hinter⟩ :=
        exists_complementary_arc_of_isPLSphere_one hQ (hβ.trans hcomp) hKQ
      have hCQ : C ⊆ Q := subset_union_right.trans hcover.subset
      have hzC : z ∈ C := (hcover.symm.subset hzQ).resolve_left fun hzK =>
        hxJ ((image_mono subset_union_left) (hKimage ▸ ⟨z, hzK, hzx⟩))
      have hBC : u '' B ∩ v '' C = {u (β 0), u (β 1)} := by
        rw [← hKimage, ← hv.injOn.image_inter hKQ hCQ, hinter, image_pair, hβ0, hβ1]
      have hendsR : ({u (β 0), u (β 1)} : Set M) ⊆ u '' R := by
        rw [← image_pair]
        exact image_mono (hBR.symm.subset.trans inter_subset_right)
      refine ⟨C, η, hη, hCQ, ⟨z, hzC, hzx⟩, ?_, Or.inl ?_, Or.inl ?_⟩
      · rintro y ⟨hyC, hy⟩
        rw [image_union] at hy
        exact hy.elim (fun hyB => hendsR (hBC.subset ⟨hyB, hyC⟩)) id
      · rw [hη0, hβ0]
        exact image_mono subset_union_right (hendsR (by simp))
      · rw [hη1, hβ1]
        exact image_mono subset_union_right (hendsR (by simp))
  obtain ⟨C, η, hη, hCQ, hxC, hCJ, h0, h1⟩ := hsource
  have hCfin : (v '' C ∩ u '' (B ∪ R)).Finite := hfinite.subset fun y hy =>
    ⟨image_mono hCQ hy.1, hCJ hy⟩
  obtain ⟨A, α, hα, hAD, hAC, hα0, hα1, hAL⟩ :=
    exists_model_subarc_of_finite_boundary_intersection hu hv hη hCQ
      ((image_mono hCQ).trans hQT) hD hDP hboundary hCfin h0 h1 ⟨x, hxC, hxD, hxJ⟩
  have hAP : A ⊆ P := hAD.trans hDP
  have hαR : ({α 0, α 1} : Set E3) ⊆ R := by
    intro y hy
    have hyA := (pair_subset (hα.bijOn.mapsTo (by norm_num))
      (hα.bijOn.mapsTo (by norm_num))) hy
    have huyJ : u y ∈ u '' (B ∪ R) := by
      rcases hy with rfl | rfl
      · exact hα0
      · exact hα1
    have huyR := hCJ ⟨hAC ⟨y, hyA, rfl⟩, huyJ⟩
    obtain ⟨z, hz, hzy⟩ := huyR
    exact hu.injOn (hRP hz) (hAP hyA) hzy ▸ hz
  refine ⟨A, α, hα, hAC.trans (image_mono hCQ), hAD, ?_, hαR⟩
  apply Subset.antisymm
  · rintro y ⟨hyA, hy⟩
    exact hAL.subset ⟨hyA, ⟨y, hy, rfl⟩⟩
  · intro y hy
    exact ⟨(pair_subset (hα.bijOn.mapsTo (by norm_num))
      (hα.bijOn.mapsTo (by norm_num))) hy, Or.inr (hαR hy)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
