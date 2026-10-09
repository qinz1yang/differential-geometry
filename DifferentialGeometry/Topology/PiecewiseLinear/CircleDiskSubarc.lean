/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcBoundaryCuts
import DifferentialGeometry.Topology.PiecewiseLinear.CircleComplementaryArc
import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_arc_through_point_with_endpoints_outside {S D : Set E}
    (hS : IsPLSphere 1 S) (hD : IsClosed D) (hnot : ¬ S ⊆ D) {x : E} (hx : x ∈ S) :
    ∃ (A : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (Icc 0 1) A ∧ A ⊆ S ∧ x ∈ A ∧
      γ 0 ∉ D ∧ γ 1 ∉ D := by
  obtain ⟨p, hpS, hpD⟩ := Set.not_subset.mp hnot
  obtain ⟨q, hqS, hqD, hqp⟩ : ∃ q, q ∈ S ∧ q ∉ D ∧ q ≠ p := by
    by_contra hn
    have hnh : S ∩ Dᶜ ∈ 𝓝[S] p := Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (hD.isOpen_compl.mem_nhds hpD))
    have hsub : S ∩ Dᶜ ⊆ {p} := by
      intro q hq
      by_contra hqp
      exact hn ⟨q, hq.1, hq.2, by simpa only [mem_singleton_iff] using hqp⟩
    exact hS.not_singleton_mem_nhdsWithin_one hpS (Filter.mem_of_superset hnh hsub)
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hcover, -⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hpS hqS hqp.symm
  rcases hcover.symm.subset hx with hxA | hxB
  · exact ⟨A, γ, hγ, subset_union_left.trans hcover.subset, hxA, hγ0.symm ▸ hpD, hγ1.symm ▸ hqD⟩
  · exact ⟨B, δ, hδ, subset_union_right.trans hcover.subset, hxB, hδ0.symm ▸ hpD, hδ1.symm ▸ hqD⟩

theorem exists_crossing_subarc_ending_on_boundary_arc {F T D B R : Set E}
    (hF : IsPLSphere 1 F) (hFT : F ⊆ T) (hD : IsClosed D)
    (hboundary : D ∩ closure (T \ D) = B ∪ R)
    {β : ℝ → E} (hβ : IsPLHomeomorphOn β (Icc 0 1) B)
    (hBR : B ∩ R = {β 0, β 1}) (hrel : Disjoint F B ∨ B ⊆ F)
    (hfinite : (F ∩ R).Finite) (hnot : ¬ F ⊆ D) {x : E} (hx : x ∈ F ∩ (D \ (B ∪ R))) :
    ∃ (A : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (Icc 0 1) A ∧ A ⊆ F ∩ D ∧
      γ 0 ∈ R ∧ γ 1 ∈ R ∧ A ∩ R = {γ 0, γ 1} ∧
      A \ {γ 0, γ 1} ⊆ D \ (B ∪ R) ∧ x ∈ A \ {γ 0, γ 1} := by
  have hsource : ∃ (A : Set E) (η : ℝ → E), IsPLHomeomorphOn η (Icc 0 1) A ∧
      A ⊆ F ∧ x ∈ A ∧ A ∩ (B ∪ R) ⊆ R ∧
      (η 0 ∈ B ∪ R ∨ η 0 ∉ D) ∧ (η 1 ∈ B ∪ R ∨ η 1 ∉ D) := by
    rcases hrel with hdis | hBF
    · obtain ⟨A, η, hη, hAF, hxA, hη0, hη1⟩ :=
        exists_arc_through_point_with_endpoints_outside hF hD hnot hx.1
      refine ⟨A, η, hη, hAF, hxA, ?_, Or.inr hη0, Or.inr hη1⟩
      rintro y ⟨hyA, hyB | hyR⟩
      · exact (Set.disjoint_left.mp hdis (hAF hyA) hyB).elim
      · exact hyR
    · obtain ⟨A, η, hη, hη0, hη1, hcover, hmeet⟩ :=
        exists_complementary_arc_of_isPLSphere_one hF hβ hBF
      have hxA : x ∈ A := (hcover.symm.subset hx.1).resolve_left
        (fun hxB => hx.2.2 (Or.inl hxB))
      have hη0R : η 0 ∈ R := by rw [hη0]; exact (hBR.symm.subset (by simp)).2
      have hη1R : η 1 ∈ R := by rw [hη1]; exact (hBR.symm.subset (by simp)).2
      refine ⟨A, η, hη, subset_union_right.trans hcover.subset, hxA, ?_,
        Or.inl (Or.inr hη0R), Or.inl (Or.inr hη1R)⟩
      rintro y ⟨hyA, hyB | hyR⟩
      · exact (hBR.symm.subset (hmeet.subset ⟨hyB, hyA⟩)).2
      · exact hyR
  obtain ⟨A, η, hη, hAF, hxA, hAJR, h0, h1⟩ := hsource
  have hAJfin : (A ∩ (B ∪ R)).Finite := hfinite.subset fun y hy => ⟨hAF hy.1, hAJR hy⟩
  obtain ⟨C, γ, hγ, hCA, hγ0, hγ1, hCJ, hopen, hxC⟩ :=
    exists_crossing_subarc_of_finite_boundary_intersection hη (hAF.trans hFT)
      hD hboundary hAJfin h0 h1 ⟨hxA, hx.2⟩
  have h0R : γ 0 ∈ R := hAJR ⟨(hCA (hγ.bijOn.mapsTo (by norm_num))).1, hγ0⟩
  have h1R : γ 1 ∈ R := hAJR ⟨(hCA (hγ.bijOn.mapsTo (by norm_num))).1, hγ1⟩
  refine ⟨C, γ, hγ, fun y hy => ⟨hAF (hCA hy).1, (hCA hy).2⟩, h0R, h1R, ?_, hopen, hxC⟩
  apply Subset.antisymm
  · exact fun y hy => hCJ.subset ⟨hy.1, Or.inr hy.2⟩
  · intro y hy
    exact ⟨(pair_subset (hγ.bijOn.mapsTo (by norm_num)) (hγ.bijOn.mapsTo (by norm_num))) hy,
      (pair_subset h0R h1R) hy⟩

end DifferentialGeometry.Topology.PiecewiseLinear
