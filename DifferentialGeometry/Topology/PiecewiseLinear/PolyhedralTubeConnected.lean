/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CurveInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeOuterTrace
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceFilling
import DifferentialGeometry.Topology.PiecewiseLinear.TubeFrontierConnected
import DifferentialGeometry.Topology.PlanarJordan.DiskUnion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsOpenTopologicalCell.isPreconnected_sdiff {X : Type*} [TopologicalSpace X]
    {M D Dint : Set X} (hM : IsOpenTopologicalCell 2 M)
    (hD : IsTopologicalCellWithInterior 2 D Dint) (hDM : D ⊆ M) : IsPreconnected (M \ D) := by
  classical
  obtain ⟨Ψ, Φ, hΨc, hΦc, hΨb, hΦb, hΦΨ, hΨΦ, -⟩ := hM.exists_planarChart
  have hΨi : InjOn Ψ M := fun x hx y hy hxy => by
    rw [← hΦΨ x hx, ← hΦΨ y hy, hxy]
  obtain ⟨φ, -⟩ := hD
  let g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → Schoenflies.Plane :=
    fun q => Ψ (φ q)
  have hgc : Continuous g :=
    hΨc.comp_continuous (continuous_subtype_val.comp φ.continuous) fun q => hDM (φ q).2
  have hgi : Function.Injective g := fun q q' hqq' =>
    φ.injective (Subtype.ext (hΨi (hDM (φ q).2) (hDM (φ q').2) hqq'))
  have _ : CompactSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hemb := (hgc.isClosedEmbedding hgi).isEmbedding
  have hrange : range g = Ψ '' D := by
    have hg : g = Ψ ∘ (Subtype.val ∘ φ) := rfl
    rw [hg, range_comp, range_comp, φ.surjective.range_eq, image_univ, Subtype.range_coe]
  let θ : (Ψ '' D : Set Schoenflies.Plane) ≃ₜ Metric.closedBall (0 : Schoenflies.Plane) 1 :=
    ((hemb.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm
  have hCc : IsCompact (Ψ '' D) := hrange ▸ isCompact_range hgc
  have hJ := PlanarJordan.isJordanCurve_frontier_of_homeomorphClosedBall θ
  have hCeq := PlanarJordan.closure_inside_frontier_eq_of_isCompact hCc hJ
    (interior_nonempty_of_homeomorphClosedBall θ)
  have hCb : Ψ '' D ⊆ Metric.ball 0 1 := image_subset_iff.mpr fun x hx => hΨb (hDM hx)
  have hGL := isPreconnected_compl_union_iUnion_closure_inside {frontier (Ψ '' D)}
    (fun γ hγ => by rw [Finset.mem_singleton.mp hγ]; exact hJ)
    (fun γ hγ γ' hγ' hne => (hne ((Finset.mem_singleton.mp hγ).trans
      (Finset.mem_singleton.mp hγ').symm)).elim)
    (F₀ := (Metric.ball (0 : Schoenflies.Plane) 1)ᶜ) Metric.isOpen_ball.isClosed_compl
    (by rw [compl_compl]; exact (convex_ball 0 1).isPreconnected)
    (fun γ hγ => by
      rw [Finset.mem_singleton.mp hγ, hCeq]
      exact Set.disjoint_compl_left_iff_subset.mpr hCb)
  rw [Finset.set_biUnion_singleton, hCeq, compl_union, compl_compl] at hGL
  have heq : M \ D = Φ '' (Metric.ball 0 1 ∩ (Ψ '' D)ᶜ) := by
    ext y
    constructor
    · rintro ⟨hyM, hyD⟩
      refine ⟨Ψ y, ⟨hΨb hyM, fun ⟨d, hd, hdy⟩ => hyD ?_⟩, hΦΨ y hyM⟩
      rw [← hΨi (hDM hd) hyM hdy]
      exact hd
    · rintro ⟨p, ⟨hp, hpD⟩, rfl⟩
      refine ⟨hΦb hp, fun hΦD => hpD ⟨Φ p, hΦD, hΨΦ p hp⟩⟩
  rw [heq]
  exact hGL.image _ (hΦc.mono inter_subset_left)

section Connected

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_isConnected
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (hconn : IsConnected K.space) (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) :
    ∃ XK' : Geometry.SimplicialComplex ℝ E3,
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧
        HasSinglePolygonTraces K h Ec XK'.space ∧ IsConnected XK'.space ∧
          IsConnected (frontier XK'.space) := by
  classical
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have ht := hd.tube
  have hXc : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  obtain ⟨Dc, hDfin, hDm, hDsp⟩ :=
    h2.isManifold.exists_isCombinatorialManifold_space_eq_frontier (n := 2) (by simp)
  have : Finite Dc.faces := hDfin.to_subtype
  have hKN : K.space ⊆ N :=
    (subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood).trans interior_subset
  have hKconn : IsConnected (h '' K.space) := hconn.image h (ht.continuousOn.mono hKN)
  have hKint : h '' K.space ⊆ interior XK.space :=
    subset_interior_iff_mem_nhdsSet.mpr h2.isNeighborhood
  have hH := hd.isConnected_compl_interior hconn
  have hHX : (interior N')ᶜ ⊆ interior XK.spaceᶜ := by
    rw [hXc.isOpen_compl.interior_eq]
    exact fun x hx hxX => hx (h2.subsetInterior hxX)
  have hsep : Separates Dc.space (h '' K.space) (interior N')ᶜ := by
    rw [hDsp]
    exact separates_frontier hKint hHX
  have : Finite (ConnectedComponents Dc.space) := finite_connectedComponents_space Dc
  obtain ⟨p, hp, hsepB⟩ :=
    exists_separating_component (isPolyhedron_space Dc).isClosed hKconn hH hsep
  have : Finite (restrict Dc (connectedComponentIn Dc.space p)).faces :=
    (restrict_faces_finite Dc _).to_subtype
  have hBsp := restrict_connectedComponentIn_space Dc p
  have hBm : IsCombinatorialManifold 2 (restrict Dc (connectedComponentIn Dc.space p)) :=
    hDm.restrict_connectedComponentIn p
  have hBconn : IsConnected (restrict Dc (connectedComponentIn Dc.space p)).space := by
    rw [hBsp]
    exact isConnected_connectedComponentIn_iff.mpr hp
  obtain ⟨R, hRfin, hRm, -, hRfr, hRcl, hRint, hRcompl⟩ :=
    hBm.exists_isCombinatorialManifoldWithBoundary_boundaryComplex _ finrank_euclideanSpace_fin
      hBconn
  have : Finite R.faces := hRfin.to_subtype
  have hRc : IsCompact R.space := (isPolyhedron_space R).isCompact
  have hfrB : frontier R.space = connectedComponentIn Dc.space p := hRfr.trans hBsp
  have hBX : connectedComponentIn Dc.space p ⊆ frontier XK.space :=
    hDsp ▸ connectedComponentIn_subset Dc.space p
  have hBR : connectedComponentIn Dc.space p ⊆ R.space :=
    hfrB ▸ hRc.isClosed.frontier_subset
  have hsplit : ∀ A : Set E3, IsPreconnected A → Disjoint A (connectedComponentIn Dc.space p) →
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
    have hEB : (Ec e ∩ connectedComponentIn Dc.space p).Nonempty := by
      by_contra hne
      rcases hsplit (Ec e) hEcconn (Set.disjoint_iff_inter_eq_empty.mpr
          (not_nonempty_iff_eq_empty.mp hne)) with h1 | h1
      · obtain ⟨z, hz⟩ := hrimne
        exact hrimR e he hcard hz (interior_subset (h1 (hrimEc hz)))
      · exact h1 hPEc (interior_subset hPint)
    have hJB : Ec e ∩ frontier XK.space ⊆ connectedComponentIn Dc.space p := by
      obtain ⟨z, hzE, hzB⟩ := hEB
      have hzJ : z ∈ Ec e ∩ frontier XK.space := ⟨hzE, hBX hzB⟩
      have hsub := hJ.isConnected_one.isPreconnected.subset_connectedComponentIn
        (F := Dc.space) hzJ (fun y hy => by rw [hDsp]; exact hy.2)
      rwa [← connectedComponentIn_eq hzB] at hsub
    have hEBJ : Ec e ∩ connectedComponentIn Dc.space p ⊆ Ec e ∩ frontier XK.space :=
      fun y hy => ⟨hy.1, hBX hy.2⟩
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
    have hAB : Disjoint (Eint e \ (Ec e ∩ XK.space)) (connectedComponentIn Dc.space p) :=
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
    have hxB : x ∈ connectedComponentIn Dc.space p := hfrB ▸ hx.2
    have hxD : x ∈ Dc.space := connectedComponentIn_subset Dc.space p hxB
    have : LocallyConnectedSpace Dc.space := locallyConnectedSpace_space Dc
    have hopen : IsOpen (connectedComponent (⟨x, hxD⟩ : Dc.space)) := isOpen_connectedComponent
    obtain ⟨t, ht, htx⟩ := isOpen_induced_iff.mp hopen
    have hxt : x ∈ t := by
      have hmem : (⟨x, hxD⟩ : Dc.space) ∈ Subtype.val ⁻¹' t := by
        rw [htx]
        exact mem_connectedComponent
      exact hmem
    filter_upwards [ht.mem_nhds hxt] with y hyt
    rw [hfrB, ← hDsp]
    constructor
    · intro hyD
      have hmem : (⟨y, hyD⟩ : Dc.space) ∈ connectedComponent (⟨x, hxD⟩ : Dc.space) := by
        rw [← htx]
        exact hyt
      rw [connectedComponentIn_eq hxB, connectedComponentIn_eq_image hxD]
      exact ⟨_, hmem, rfl⟩
    · exact fun hyB => connectedComponentIn_subset Dc.space p hyB
  · intro e he hcard
    rw [(htrace e he hcard).1, (htrace e he hcard).2]
    exact h34 e he hcard
  · rw [← hRcl]
    exact hRint.closure
  · rw [hfrB]
    exact isConnected_connectedComponentIn_iff.mpr hp

end Connected

end DifferentialGeometry.Topology.PiecewiseLinear
