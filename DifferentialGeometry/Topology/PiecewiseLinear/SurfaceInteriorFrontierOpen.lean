/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.StarComponents
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLBall_neighborhood_pair_sdiff_of_isCombinatorialManifoldWithBoundary
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hLK : L.space ⊆ K.space) {p : E}
    (hp : p ∈ L.space \ (boundaryComplex 2 L).space)
    (hpB : p ∉ (boundaryComplex 3 K).space) {U : Set E} (hU : U ∈ 𝓝[K.space] p) :
    ∃ C : Set E, IsPLBall 3 C ∧ C ⊆ K.space ∩ U ∧ C ∈ 𝓝[K.space] p ∧
      IsPLBall 2 (C ∩ L.space) ∧
      ∃ x ∈ C \ L.space, ∃ y ∈ C \ L.space,
        Disjoint (connectedComponentIn (C \ L.space) x) (connectedComponentIn (C \ L.space) y) ∧
        connectedComponentIn (C \ L.space) x ∪ connectedComponentIn (C \ L.space) y =
          C \ L.space ∧
        IsPLBall 3 (closure (connectedComponentIn (C \ L.space) x)) ∧
        IsPLBall 3 (closure (connectedComponentIn (C \ L.space) y)) ∧
        closure (connectedComponentIn (C \ L.space) x) ∪
          closure (connectedComponentIn (C \ L.space) y) = C ∧
        closure (connectedComponentIn (C \ L.space) x) ∩
          closure (connectedComponentIn (C \ L.space) y) = C ∩ L.space := by
  classical
  obtain ⟨V, hV, hVU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hU
  obtain ⟨R, hR, hRfin, hpR, hRV⟩ :=
    exists_isSubdivision_closedStar_subset_of_mem_nhds K (hLK hp.1) hV
  let : Finite R.faces := hRfin.to_subtype
  obtain ⟨T, hT, hTfin, hTL⟩ :=
    exists_isSubdivision_restrict_isSubdivision R L (by rwa [hR.space_eq])
  let : Finite T.faces := hTfin.to_subtype
  have hTK : IsSubdivision T K := hT.trans hR
  have hpT : {p} ∈ T.faces := hT.singleton_mem hpR
  let A := restrict T L.space
  let : Finite A.faces := (restrict_faces_finite T L.space).to_subtype
  have hA : A.space = L.space := hTL.space_eq
  have hAT : A.faces ⊆ T.faces := restrict_faces_subset T L.space
  have hpA : {p} ∈ A.faces := by
    refine ⟨hpT, ?_⟩
    simpa only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff] using hp.1
  have hKlink : IsPLSphere 2 (SimplicialComplex.geometricLink T {p}).space := by
    rcases hK.of_isSubdivision hTK p hpT with hsphere | hball
    · exact hsphere
    · exact (hpB ((isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision
        K T hK hTK hpT).mp hball)).elim
  have hAlink : IsPLSphere 1 (SimplicialComplex.geometricLink A {p}).space := by
    rcases hL.of_isSubdivision hTL p hpA with hsphere | hball
    · exact hsphere
    · exfalso
      have hmem := (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision
        L A hL hTL hpA).mp hball
      exact hp.2 hmem
  let C := closedStar (PiecewiseLinear.barycentricSubdivision T) p
  have hpTb : {p} ∈ (PiecewiseLinear.barycentricSubdivision T).faces :=
    (barycentricSubdivision_isSubdivision T).singleton_mem hpT
  have hC : IsPLBall 3 C := isPLBall_closedStar (PiecewiseLinear.barycentricSubdivision T) hpTb
    ((isPLSphere_geometricLink_iff_of_isSubdivision (barycentricSubdivision_isSubdivision T)
      hpT).mpr hKlink)
  have hCsub : C ⊆ K.space := by
    rw [← hTK.space_eq, ← (barycentricSubdivision_isSubdivision T).space_eq]
    exact closedStar_subset_space (PiecewiseLinear.barycentricSubdivision T) p
  have hCV : C ⊆ V :=
    (closedStar_subset_of_isSubdivision (barycentricSubdivision_isSubdivision T) p).trans
      ((closedStar_subset_of_isSubdivision hT p).trans hRV)
  have hCnhds : C ∈ 𝓝[K.space] p := by
    rw [← hTK.space_eq, ← (barycentricSubdivision_isSubdivision T).space_eq]
    exact closedStar_mem_nhdsWithin (PiecewiseLinear.barycentricSubdivision T) p
  have htrace : C ∩ L.space = closedStar (PiecewiseLinear.barycentricSubdivision A) p := by
    rw [← hA]
    exact closedStar_barycentricSubdivision_inter_space_eq hAT hpA
  have hpAb : {p} ∈ (PiecewiseLinear.barycentricSubdivision A).faces :=
    (barycentricSubdivision_isSubdivision A).singleton_mem hpA
  have htraceball : IsPLBall 2 (C ∩ L.space) := by
    rw [htrace]
    exact isPLBall_closedStar (PiecewiseLinear.barycentricSubdivision A) hpAb
      ((isPLSphere_geometricLink_iff_of_isSubdivision (barycentricSubdivision_isSubdivision A)
        hpA).mpr hAlink)
  refine ⟨C, hC, fun z hz => ⟨hCsub hz, hVU ⟨hCV hz, hCsub hz⟩⟩, hCnhds, htraceball, ?_⟩
  have hcomponents := exists_connectedComponentIn_pair_closedStar_sdiff hAT hpA hKlink hAlink
  rwa [hA] at hcomponents

open Classical in
theorem exists_connected_neighborhood_pair_sdiff_of_isCombinatorialManifoldWithBoundary
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 2 L) (hdim : Module.finrank ℝ E = 3)
    {p : E} (hp : p ∈ L.space \ (boundaryComplex 2 L).space) {U : Set E} (hU : U ∈ 𝓝 p) :
    ∃ C ∈ 𝓝 p, C ⊆ U ∧
      ∃ A B : Set E, IsConnected A ∧ IsConnected B ∧ A ∪ B = C \ L.space ∧
        C ∩ L.space ⊆ closure A ∧ C ∩ L.space ⊆ closure B := by
  obtain ⟨T, hT, hTcard, hLT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (isPolyhedron_space L).isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKspace : K.space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hK := hKball.isCombinatorialManifoldWithBoundary
  have hint : interior K.space = openSimplex T := by
    rw [hKspace, interior_convexHull_eq_openSimplex hT (by omega)]
  have hLint : L.space ⊆ interior K.space := hLT.trans hint.symm.subset
  have hpB : p ∉ (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK]
    exact fun h => h.2 (hLint hp.1)
  obtain ⟨C, _, hCU, hCnhds, _, a, ha, b, hb, _, hunion, _, _, _, hinter⟩ :=
    exists_isPLBall_neighborhood_pair_sdiff_of_isCombinatorialManifoldWithBoundary
      hK hL (hLint.trans interior_subset) hp hpB (nhdsWithin_le_nhds hU)
  rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hLint hp.1))] at hCnhds
  refine ⟨C, hCnhds, hCU.trans inter_subset_right,
    connectedComponentIn (C \ L.space) a,
    connectedComponentIn (C \ L.space) b,
    isConnected_connectedComponentIn_iff.mpr ha,
    isConnected_connectedComponentIn_iff.mpr hb,
    hunion, hinter.symm.subset.trans inter_subset_left, hinter.symm.subset.trans inter_subset_right⟩

open Classical in
theorem isOpen_preimage_frontier_component_surface_interior_of_finrank
    (hdim : Module.finrank ℝ E = 3)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {T : Set E}
    (hT : IsClosed T) (hinter : K.space ∩ T ⊆ (boundaryComplex 2 K).space) (x : E) :
    IsOpen (((↑) : ↥(K.space \ (boundaryComplex 2 K).space) → E) ⁻¹'
      frontier (connectedComponentIn (K.space ∪ T)ᶜ x)) := by
  classical
  let U := (K.space ∪ T)ᶜ
  let F := connectedComponentIn U x
  have hKclosed : IsClosed K.space := (isPolyhedron_space K).isClosed
  have hUopen : IsOpen U := (hKclosed.union hT).isOpen_compl
  have hFopen : IsOpen F := hUopen.connectedComponentIn
  by_cases hx : x ∈ U
  · rw [isOpen_iff_mem_nhds]
    intro ⟨p, hpS⟩ hpF
    have hpT : p ∉ T := fun hpT =>
      hpS.2 (hinter ⟨hpS.1, hpT⟩)
    let _ : Finite (boundaryComplex 2 K).faces :=
      (boundaryComplex_faces_finite 2 K).to_subtype
    have hBclosed : IsClosed (boundaryComplex 2 K).space :=
      (isPolyhedron_space (boundaryComplex 2 K)).isClosed
    let V := Tᶜ ∩ ((boundaryComplex 2 K).space)ᶜ
    have hVopen : IsOpen V := hT.isOpen_compl.inter hBclosed.isOpen_compl
    have hpV : p ∈ V := ⟨hpT, hpS.2⟩
    have hVT : Disjoint V T := disjoint_left.mpr fun _ hz hzT => hz.1 hzT
    have hVB : Disjoint V (boundaryComplex 2 K).space :=
      disjoint_left.mpr fun _ hz hzB => hz.2 hzB
    have hpair :=
      exists_connected_neighborhood_pair_sdiff_of_isCombinatorialManifoldWithBoundary
        K hK hdim hpS (hVopen.mem_nhds hpV)
    rcases hpair with ⟨C, hCnhds, hCV, A, B, hAconn, hBconn, hAB, hclA, hclB⟩
    have hCU : C \ K.space ⊆ U := by
      rintro y ⟨hyC, hyK⟩
      intro hyUnion
      rcases hyUnion with hyK' | hyT
      · exact hyK hyK'
      · exact disjoint_left.mp hVT (hCV hyC) hyT
    have hFmeet : (C ∩ F).Nonempty := by
      have hpcl : p ∈ closure F := (frontier_subset_closure hpF)
      exact mem_closure_iff_nhds.mp hpcl C hCnhds
    have hFsub : C ∩ F ⊆ C \ K.space := by
      rintro y ⟨hyC, hyF⟩
      have hyU : y ∈ U := connectedComponentIn_subset U x hyF
      exact ⟨hyC, fun hyK => hyU (Or.inl hyK)⟩
    have hsplit : (A ∩ F).Nonempty ∨ (B ∩ F).Nonempty := by
      obtain ⟨y, hyCF⟩ := hFmeet
      have hyAB : y ∈ A ∪ B := hAB.symm.subset (hFsub hyCF)
      rcases hyAB with hyA | hyB
      · exact Or.inl ⟨y, hyA, hyCF.2⟩
      · exact Or.inr ⟨y, hyB, hyCF.2⟩
    have hsubfront : C ∩ K.space ⊆ frontier F := by
      rcases hsplit with ⟨y, hyA, hyF⟩ | ⟨y, hyB, hyF⟩
      · have hAF : A ⊆ F :=
          (hAconn.isPreconnected.subset_connectedComponentIn hyA
            (subset_union_left.trans (hAB.subset.trans hCU))).trans
            (connectedComponentIn_eq hyF).symm.subset
        intro z hz
        have hzcl : z ∈ closure F := closure_mono hAF (hclA hz)
        have hznot : z ∉ interior F := fun hzint =>
          (connectedComponentIn_subset U x (hFopen.interior_eq.subset hzint)) (Or.inl hz.2)
        exact ⟨hzcl, hznot⟩
      · have hBF : B ⊆ F :=
          (hBconn.isPreconnected.subset_connectedComponentIn hyB
            (subset_union_right.trans (hAB.subset.trans hCU))).trans
            (connectedComponentIn_eq hyF).symm.subset
        intro z hz
        have hzcl : z ∈ closure F := closure_mono hBF (hclB hz)
        have hznot : z ∉ interior F := fun hzint =>
          (connectedComponentIn_subset U x (hFopen.interior_eq.subset hzint)) (Or.inl hz.2)
        exact ⟨hzcl, hznot⟩
    have hCS : C ∩ (K.space \ (boundaryComplex 2 K).space) ⊆ frontier F := by
      intro z hz
      exact hsubfront ⟨hz.1, hz.2.1⟩
    have hCrel : (Subtype.val ⁻¹' C : Set ↥(K.space \ (boundaryComplex 2 K).space)) ∈ 𝓝 ⟨p, hpS⟩ :=
      preimage_coe_mem_nhds_subtype.mpr (nhdsWithin_le_nhds hCnhds)
    refine Filter.mem_of_superset hCrel ?_
    rintro ⟨z, hzS⟩ hzC
    exact hCS ⟨hzC, hzS⟩
  · have hFempty : connectedComponentIn U x = ∅ := connectedComponentIn_eq_empty hx
    change IsOpen (((↑) : ↥(K.space \ (boundaryComplex 2 K).space) → E) ⁻¹'
      frontier (connectedComponentIn U x))
    rw [hFempty, frontier_empty, preimage_empty]
    exact isOpen_empty

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem isOpen_preimage_frontier_component_surface_interior
    (K : Geometry.SimplicialComplex ℝ E3) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {T : Set E3}
    (hT : IsClosed T) (hinter : K.space ∩ T ⊆ (boundaryComplex 2 K).space) (x : E3) :
    IsOpen (((↑) : ↥(K.space \ (boundaryComplex 2 K).space) → E3) ⁻¹'
      frontier (connectedComponentIn (K.space ∪ T)ᶜ x)) := by
  have hd : (inferInstance : DecidableEq E3) = (fun a b => Classical.propDecidable (a = b)) := by
    ext a b
    exact Subsingleton.elim _ _
  have hB : (boundaryComplex 2 K).space =
      (@boundaryComplex E3 _ _ (fun a b => Classical.propDecidable (a = b)) 2 K).space :=
    congrArg (fun d : DecidableEq E3 => (@boundaryComplex E3 _ _ d 2 K).space) hd
  rw [hB] at hinter ⊢
  exact isOpen_preimage_frontier_component_surface_interior_of_finrank
    finrank_euclideanSpace_fin K hK hT hinter x

end DifferentialGeometry.Topology.PiecewiseLinear
