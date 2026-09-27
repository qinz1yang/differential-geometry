/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeConnected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Transfer

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_of_separating_surface
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (hconn : IsConnected K.space) (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) (Bc : Geometry.SimplicialComplex ℝ E3)
    [Finite Bc.faces] (hBm : IsCombinatorialManifold 2 Bc) (hBconn : IsConnected Bc.space)
    (hsepB : Separates Bc.space (h '' K.space) (interior N')ᶜ)
    (hBE : ∀ e ∈ K.faces, e.card = 2 → Ec e ∩ Bc.space ⊆ frontier XK.space)
    (hloc : ∀ e ∈ K.faces, e.card = 2 → ∀ x ∈ Ec e ∩ Bc.space,
      ∀ᶠ y in 𝓝 x, y ∈ Bc.space ↔ y ∈ frontier XK.space) :
    ∃ XK' : Geometry.SimplicialComplex ℝ E3,
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧
        HasSinglePolygonTraces K h Ec XK'.space ∧ IsConnected XK'.space ∧
          frontier XK'.space = Bc.space := by
  classical
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have ht := hd.tube
  have hXc : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  have hKN : K.space ⊆ N :=
    (subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood).trans interior_subset
  have hKconn : IsConnected (h '' K.space) := hconn.image h (ht.continuousOn.mono hKN)
  have hH := hd.isConnected_compl_interior hconn
  obtain ⟨R, hRfin, hRm, -, hRfr, hRcl, hRint, hRcompl⟩ :=
    hBm.exists_isCombinatorialManifoldWithBoundary_boundaryComplex _ finrank_euclideanSpace_fin
      hBconn
  have : Finite R.faces := hRfin.to_subtype
  have hRc : IsCompact R.space := (isPolyhedron_space R).isCompact
  have hfrB : frontier R.space = Bc.space := hRfr
  have hBR : Bc.space ⊆ R.space :=
    hfrB ▸ hRc.isClosed.frontier_subset
  have hsplit : ∀ A : Set E3, IsPreconnected A → Disjoint A (Bc.space) →
      A ⊆ interior R.space ∨ A ⊆ R.spaceᶜ := by
    intro A hA hAB
    refine hA.subset_or_subset isOpen_interior hRc.isClosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) fun y hy => ?_
    by_cases hyR : y ∈ R.space
    · refine Or.inl ((mem_interior_iff_notMem_frontier hyR).mpr fun hyfr => ?_)
      rw [hfrB] at hyfr
      exact Set.disjoint_left.mp hAB hy hyfr
    · exact Or.inr hyR
  have hN'c : IsCompact N' := by
    rw [ht.imageEq]
    exact ht.isCompact.image_of_continuousOn ht.continuousOn
  have hHR : (interior N')ᶜ ⊆ R.spaceᶜ := by
    rcases hsplit _ hH.isPreconnected
        (Set.disjoint_left.mpr fun y hy hyB => hsepB.right_subset_compl hy hyB) with h1 | h1
    · exfalso
      apply (hN'c.union hRc).ne_univ
      refine eq_univ_of_forall fun y => ?_
      by_cases hy : y ∈ interior N'
      · exact Or.inl (interior_subset hy)
      · exact Or.inr (interior_subset (h1 hy))
    · exact h1
  have hKR : h '' K.space ⊆ interior R.space := by
    rcases hsplit _ hKconn.isPreconnected
        (Set.disjoint_left.mpr fun y hy hyB => hsepB.left_subset_compl hy hyB) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨y, hyB, hyR⟩ := hsepB.inter_nonempty_of_isPreconnected
        hRcompl.isPreconnected (hKconn.nonempty.mono fun z hz => ⟨hz, h1 hz⟩)
        (hH.nonempty.mono fun z hz => ⟨hz, hHR hz⟩)
      exact hyR (hBR hyB)
  have hRN' : R.space ⊆ interior N' := fun y hy => by
    by_contra hyn
    exact hHR hyn hy
  have hrimR : ∀ e ∈ K.faces, e.card = 2 → Ebd e ⊆ R.spaceᶜ := by
    intro e he hcard y hy
    have hyfr : y ∈ frontier N' := by
      rw [← hd.rimFrontier e he hcard] at hy
      exact hy.2
    exact hHR hyfr.2
  have htrace : ∀ e ∈ K.faces, e.card = 2 → Ec e ∩ R.space = Ec e ∩ XK.space ∧
      Ec e ∩ frontier R.space = Ec e ∩ frontier XK.space := by
    intro e he hcard
    have hpc := hd.pseudoCell e he hcard
    obtain ⟨hJ, DJint, hcell, hdiff, hPD⟩ := h34 e he hcard
    have hEEc : Eint e ⊆ Ec e := by
      rw [hpc.carrierEq]
      exact subset_union_left
    have hEconn : IsPreconnected (Eint e) := by
      obtain ⟨ψ⟩ := hpc.isOpenCell
      have : PreconnectedSpace (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
        isPreconnected_iff_preconnectedSpace.mp (convex_ball 0 1).isPreconnected
      have hr := isPreconnected_range (continuous_subtype_val.comp ψ.symm.continuous)
      rwa [range_comp, ψ.symm.surjective.range_eq, image_univ, Subtype.range_coe] at hr
    have hEcconn : IsPreconnected (Ec e) := by
      rw [hpc.carrierEq, ← hpc.closureEq]
      exact hEconn.closure
    have hPK : h (e.centroid ℝ id) ∈ h '' K.space :=
      ⟨_, K.convexHull_subset_space he (e.centroid_mem_convexHull (K.nonempty_of_mem_faces he)),
        rfl⟩
    have hPint : h (e.centroid ℝ id) ∈ interior R.space := hKR hPK
    have hPEc : h (e.centroid ℝ id) ∈ Ec e := hEEc hpc.centerMem
    have hrimne : (Ebd e).Nonempty := by
      obtain ⟨ψ⟩ := hpc.isSphere
      have hs : ((EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))) ∈
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        simp
      exact ⟨ψ.symm ⟨_, hs⟩, (ψ.symm ⟨_, hs⟩).2⟩
    have hrimEc : Ebd e ⊆ Ec e := by
      rw [hpc.carrierEq]
      exact subset_union_right
    have hEB : (Ec e ∩ Bc.space).Nonempty := by
      by_contra hne
      rcases hsplit (Ec e) hEcconn (Set.disjoint_iff_inter_eq_empty.mpr
          (not_nonempty_iff_eq_empty.mp hne)) with h1 | h1
      · obtain ⟨z, hz⟩ := hrimne
        exact hrimR e he hcard hz (interior_subset (h1 (hrimEc hz)))
      · exact h1 hPEc (interior_subset hPint)
    have hJB : Ec e ∩ frontier XK.space ⊆ Bc.space := by
      obtain ⟨z, hzE, hzB⟩ := hEB
      have hzJ : z ∈ Ec e ∩ frontier XK.space := ⟨hzE, hBE e he hcard ⟨hzE, hzB⟩⟩
      have hBclosed : IsClosed Bc.space := (isPolyhedron_space Bc).isClosed
      set O := interior {w | w ∈ Bc.space ↔ w ∈ frontier XK.space} with hOdef
      have hJsub : Ec e ∩ frontier XK.space ⊆ O ∪ Bc.spaceᶜ := by
        intro y hy
        by_cases hyB : y ∈ Bc.space
        · exact Or.inl (mem_interior_iff_mem_nhds.mpr (hloc e he hcard y ⟨hy.1, hyB⟩))
        · exact Or.inr hyB
      have hdisj : Ec e ∩ frontier XK.space ∩ (O ∩ Bc.spaceᶜ) = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun y ⟨hy, hyO, hyB⟩ => hyB ?_
        exact (interior_subset hyO : y ∈ {w | w ∈ Bc.space ↔ w ∈ frontier XK.space}).mpr hy.2
      rcases isPreconnected_iff_subset_of_disjoint.mp hJ.isConnected_one.isPreconnected O
          Bc.spaceᶜ isOpen_interior hBclosed.isOpen_compl hJsub hdisj with h1 | h1
      · intro y hy
        exact (interior_subset (h1 hy) :
          y ∈ {w | w ∈ Bc.space ↔ w ∈ frontier XK.space}).mpr hy.2
      · exact absurd hzB (h1 hzJ)
    have hEBJ : Ec e ∩ Bc.space ⊆ Ec e ∩ frontier XK.space :=
      fun y hy => ⟨hy.1, hBE e he hcard hy⟩
    have hfr : Ec e ∩ frontier R.space = Ec e ∩ frontier XK.space := by
      rw [hfrB]
      exact Subset.antisymm hEBJ fun y hy => ⟨hy.1, hJB hy⟩
    have hDJsub : DJint ⊆ Ec e ∩ XK.space := by
      obtain ⟨φ, hφ⟩ := hcell
      rw [hφ]
      rintro _ ⟨q, -, rfl⟩
      exact q.2
    have hDJJ : Disjoint DJint (Ec e ∩ frontier XK.space) := by
      rw [← hdiff]
      exact Set.disjoint_sdiff_right
    have hDJconn : IsPreconnected DJint := by
      obtain ⟨φ, hφ⟩ := hcell
      rw [hφ]
      refine IsPreconnected.image ?_ _ continuous_subtype_val.continuousOn
      refine IsPreconnected.image ?_ _ φ.continuous.continuousOn
      rw [← IsInducing.subtypeVal.isPreconnected_image]
      have himg : (Subtype.val : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 →
          EuclideanSpace ℝ (Fin 2)) '' {q | ‖(q : EuclideanSpace ℝ (Fin 2))‖ < 1} =
            Metric.ball 0 1 := by
        ext z
        constructor
        · rintro ⟨q, hq, rfl⟩
          exact mem_ball_zero_iff.mpr hq
        · intro hz
          exact ⟨⟨z, Metric.ball_subset_closedBall hz⟩, mem_ball_zero_iff.mp hz, rfl⟩
      rw [himg]
      exact (convex_ball 0 1).isPreconnected
    have hDJint : DJint ⊆ interior R.space := by
      rcases hsplit DJint hDJconn (Set.disjoint_left.mpr fun y hy hyB =>
          Set.disjoint_left.mp hDJJ hy (hEBJ ⟨(hDJsub hy).1, hyB⟩)) with h1 | h1
      · exact h1
      · exact (h1 hPD (interior_subset hPint)).elim
    have hXR : Ec e ∩ XK.space ⊆ R.space := by
      intro y hy
      by_cases hyD : y ∈ DJint
      · exact interior_subset (hDJint hyD)
      · have hyJ : y ∈ Ec e ∩ frontier XK.space := by
          rw [← hdiff]
          exact ⟨hy, hyD⟩
        exact hBR (hJB hyJ)
    have hXE : Ec e ∩ XK.space ⊆ Eint e := by
      rintro y ⟨hyEc, hyX⟩
      rw [hpc.carrierEq] at hyEc
      exact hyEc.resolve_right fun hyB =>
        Set.disjoint_left.mp (h2.rimDisjoint e he hcard) hyB hyX
    refine ⟨Subset.antisymm (fun y hy => ?_) fun y hy => ⟨hy.1, hXR hy⟩, hfr⟩
    refine ⟨hy.1, ?_⟩
    by_contra hyX
    have hyE : y ∈ Eint e := by
      have hyEc := hy.1
      rw [hpc.carrierEq] at hyEc
      exact hyEc.resolve_right fun hyB => hrimR e he hcard hyB hy.2
    have hA := IsOpenTopologicalCell.isPreconnected_sdiff hpc.isOpenCell hcell hXE
    have hAB : Disjoint (Eint e \ (Ec e ∩ XK.space)) (Bc.space) :=
      Set.disjoint_left.mpr fun z hz hzB =>
        hz.2 ⟨hEEc hz.1, hXc.frontier_subset (hEBJ ⟨hEEc hz.1, hzB⟩).2⟩
    have hEnR : ∃ z ∈ Eint e, z ∉ R.space := by
      by_contra hall
      push Not at hall
      obtain ⟨z, hz⟩ := hrimne
      have hzcl : z ∈ closure (Eint e) := by
        rw [hpc.closureEq]
        exact Or.inr hz
      exact hrimR e he hcard hz (closure_minimal hall hRc.isClosed hzcl)
    obtain ⟨z, hzE, hzR⟩ := hEnR
    have hzA : z ∈ Eint e \ (Ec e ∩ XK.space) := ⟨hzE, fun hzX => hzR (hXR hzX)⟩
    rcases hsplit _ hA hAB with h1 | h1
    · exact hzR (interior_subset (h1 hzA))
    · exact h1 ⟨hyE, fun hyX' => hyX hyX'.2⟩ hy.2
  refine ⟨R, ⟨hRfin, hRm, subset_interior_iff_mem_nhdsSet.mp hKR, hRN', fun e he hcard =>
    Set.disjoint_left.mpr fun y hy hyR => hrimR e he hcard hy hyR, ?_⟩, ?_, ?_, ?_⟩
  · intro e he hcard x hx
    have hxX : x ∈ Ec e ∩ frontier XK.space := (htrace e he hcard).2 ▸ hx
    refine (h2.crossing e he hcard x hxX).congr
      (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_
    have hxB : x ∈ Bc.space := hfrB ▸ hx.2
    filter_upwards [hloc e he hcard x ⟨hx.1, hxB⟩] with y hy
    rw [hfrB]
    exact hy.symm
  · intro e he hcard
    rw [(htrace e he hcard).1, (htrace e he hcard).2]
    exact h34 e he hcard
  · rw [← hRcl]
    exact hRint.closure
  · exact hfrB

end Transfer

end DifferentialGeometry.Topology.PiecewiseLinear
