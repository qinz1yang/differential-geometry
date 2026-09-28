/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonBoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutPair
import DifferentialGeometry.Topology.PiecewiseLinear.InnermostBoundaryDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasPLCurveCrossingOnAt.swap {S A B : Set E} {x : E}
    (hc : HasPLCurveCrossingOnAt S A B x) : HasPLCurveCrossingOnAt S B A x := by
  obtain ⟨U, V, φ, T, P, Q, hU, hV, hxU, hφ, hφx, hT, hP, hQ, hPT, hQT, hPQ, hloc⟩ := hc
  refine ⟨U, V, φ, T, Q, P, hU, hV, hxU, hφ, hφx, hT, hQ, hP, hQT, hPT,
    (inf_comm Q P).trans hPQ, ?_⟩
  filter_upwards [hloc] with y hy using ⟨hy.1, hy.2.2, hy.2.1⟩

variable [FiniteDimensional ℝ E]

theorem exists_boundary_arc_avoiding_disjoint_circles
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsCombinatorialManifold 2 L)
    {D J : Set E} {q : (Fin 3 → ℝ) → E} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDJ : q '' stdSimplexBoundary 2 = J) (hDL : D ⊆ L.space)
    {ι : Type*} {F : ι → Set E} (hF : ∀ i, IsPLSphere 1 (F i)) (hFL : ∀ i, F i ⊆ L.space)
    (hdis : Pairwise fun i j => Disjoint (F i) (F j))
    (hfinite : (J ∩ ⋃ i, F i).Finite) (hno : ∀ i, ¬ F i ⊆ D)
    (hcross : ∀ i, ∀ x ∈ J ∩ F i, HasPLCurveCrossingOnAt L.space J (F i) x)
    (hmeet : (J ∩ ⋃ i, F i).Nonempty) :
    ∃ (i : ι) (B : Set E) (η : ℝ → E), IsPLHomeomorphOn η (Icc 0 1) B ∧
      B ⊆ J ∧ ({η 0, η 1} : Set E) ⊆ F i ∧ B ∩ (⋃ j, F j) = {η 0, η 1} := by
  obtain ⟨p, hpJ, hpF⟩ := hmeet
  obtain ⟨i₀, hpi₀⟩ := mem_iUnion.mp hpF
  have hcl := (hcross i₀ p ⟨hpJ, hpi₀⟩).swap.mem_closure_inter_diskInterior hq hDL
    (Filter.Eventually.of_forall fun _ => by rw [hDJ])
  rw [hDJ] at hcl
  have hnon : (F i₀ ∩ (D \ J)).Nonempty := by
    by_contra hnon
    rw [Set.not_nonempty_iff_eq_empty.mp hnon, closure_empty] at hcl
    exact hcl
  obtain ⟨x, hxF, hxD, hxJ⟩ := hnon
  have hDclosed := (show IsPLBall 2 D from ⟨q, hq⟩).isPolyhedron.isClosed
  have hboundary := (hL.inter_closure_sdiff_disk L hq hDL).trans hDJ
  obtain ⟨A₀, α₀, hα₀, hA₀F, hxA₀, hα₀0, hα₀1⟩ :=
    exists_arc_through_point_with_endpoints_outside (hF i₀) hDclosed (hno i₀) hxF
  have hA₀fin : (A₀ ∩ J).Finite := hfinite.subset fun y hy =>
    ⟨hy.2, mem_iUnion.mpr ⟨i₀, hA₀F hy.1⟩⟩
  obtain ⟨A, α, hα, hAA₀, hα0J, hα1J, hAJ, -, -⟩ :=
    exists_crossing_subarc_of_finite_boundary_intersection hα₀ (hA₀F.trans (hFL i₀))
      hDclosed hboundary hA₀fin (Or.inr hα₀0) (Or.inr hα₀1) ⟨hxA₀, hxD, hxJ⟩
  have hAD : A ⊆ D := fun y hy => (hAA₀ hy).2
  have hAF : A ⊆ F i₀ := fun y hy => hA₀F (hAA₀ hy).1
  obtain ⟨D₀, _, R₀, _, q₀, _, δ₀, _, hq₀, _, hδ₀, _, hδ₀0, hδ₀1, _, _,
      hDunion, _, hq₀A, _, hD₀J, _, hRunion, _⟩ :=
    exists_disk_pair_with_boundary_arcs_of_proper_arc hq hα hAD (by rw [hDJ]; exact hAJ)
  have hD₀D : D₀ ⊆ D := subset_union_left.trans hDunion.subset
  have hR₀J : R₀ ⊆ J := subset_union_left.trans (hRunion.trans hDJ).subset
  have hAR₀ : A ∩ R₀ = {α 0, α 1} := by
    apply Subset.antisymm
    · exact fun y hy => hAJ.subset ⟨hy.1, hR₀J hy.2⟩
    · intro y hy
      have hyR : y ∈ R₀ := by
        rw [← hδ₀0, ← hδ₀1] at hy
        exact (pair_subset (hδ₀.bijOn.mapsTo (by norm_num))
          (hδ₀.bijOn.mapsTo (by norm_num))) hy
      exact ⟨(pair_subset (hα.bijOn.mapsTo (by norm_num))
        (hα.bijOn.mapsTo (by norm_num))) hy, hyR⟩
  obtain ⟨i, A', B, D', q', β, η, hβ, hη, hη0, hη1, hA'F, hBR₀, hA'B,
      hq', hD'D₀, _, hq'B, hclean⟩ :=
    exists_innermost_disk_with_boundary_subarc L hL hq₀ (hD₀D.trans hDL)
      hα hδ₀ hδ₀0 hδ₀1 hAR₀ hq₀A hF hFL hdis
      (hfinite.subset fun y hy => ⟨hR₀J hy.1, hy.2⟩)
      (fun j hj => hno j (hj.trans hD₀D)) i₀ hAF
  have hBJ : B ⊆ J := hBR₀.trans hR₀J
  have hends : ({η 0, η 1} : Set E) ⊆ F i := by
    rw [hη0, hη1]
    exact (pair_subset (hβ.bijOn.mapsTo (by norm_num))
      (hβ.bijOn.mapsTo (by norm_num))).trans hA'F
  refine ⟨i, B, η, hη, hBJ, hends, Subset.antisymm ?_ ?_⟩
  · rintro y ⟨hyB, hyF⟩
    by_contra hyends
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hyF
    have hyA' : y ∉ A' := by
      intro hy
      exact hyends (by simpa only [hη0, hη1] using hA'B.subset ⟨hy, hyB⟩)
    have hcc := (hcross j y ⟨hBJ hyB, hyj⟩).swap
    have hlocB := hcc.eventually_mem_arc_iff hη hBJ ⟨hyB, hyends⟩
    have hclosedA' := ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn
      hβ).isPolyhedron.isClosed
    have hlocbd : ∀ᶠ z in 𝓝 y, z ∈ q' '' stdSimplexBoundary 2 ↔ z ∈ J := by
      filter_upwards [hclosedA'.isOpen_compl.mem_nhds hyA', hlocB] with z hz hzB
      rw [hq'B]
      exact (or_iff_right hz).trans hzB
    have hcy := hcc.mem_closure_inter_diskInterior hq' ((hD'D₀.trans hD₀D).trans hDL) hlocbd
    rw [hq'B, (hclean j).symm.inter_eq, closure_empty] at hcy
    exact hcy
  · intro y hy
    exact ⟨(pair_subset (hη.bijOn.mapsTo (by norm_num))
      (hη.bijOn.mapsTo (by norm_num))) hy, mem_iUnion.mpr ⟨i, hends hy⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
