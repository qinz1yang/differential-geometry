import DifferentialGeometry.Topology.PiecewiseLinear.StarComponents
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_neighborhood_pair_sdiff
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) {p : E} (hp : p ∈ L.space)
    (hpB : p ∉ (boundaryComplex 3 K).space) {U : Set E} (hU : U ∈ 𝓝[K.space] p) :
    ∃ C : Set E, IsPLBall 3 C ∧ C ⊆ K.space ∩ U ∧ C ∈ 𝓝[K.space] p ∧
      IsPLBall 2 (C ∩ L.space) ∧
      ∃ x ∈ C \ L.space, ∃ y ∈ C \ L.space,
        let C₀ := connectedComponentIn (C \ L.space) x
        let C₁ := connectedComponentIn (C \ L.space) y
        Disjoint C₀ C₁ ∧ C₀ ∪ C₁ = C \ L.space ∧
        IsPLBall 3 (closure C₀) ∧ IsPLBall 3 (closure C₁) ∧
        closure C₀ ∪ closure C₁ = C ∧ closure C₀ ∩ closure C₁ = C ∩ L.space := by
  classical
  obtain ⟨V, hV, hVU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hU
  obtain ⟨R, hR, hRfin, hpR, hRV⟩ :=
    exists_isSubdivision_closedStar_subset_of_mem_nhds K (hLK hp) hV
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
    simpa only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff] using hp
  have hAM : IsCombinatorialManifold 2 A := hL.of_isSubdivision hTL
  have hKlink : IsPLSphere 2 (SimplicialComplex.geometricLink T {p}).space := by
    rcases hK.of_isSubdivision hTK p hpT with hsphere | hball
    · exact hsphere
    · exact (hpB ((isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision
        K T hK hTK hpT).mp hball)).elim
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
  have htraceball : IsPLBall 2 (C ∩ L.space) := by
    rw [htrace]
    exact (hAM.of_isSubdivision (barycentricSubdivision_isSubdivision A)).isPLBall_closedStar
      ((barycentricSubdivision_isSubdivision A).singleton_mem hpA)
  refine ⟨C, hC, fun z hz => ⟨hCsub hz, hVU ⟨hCV hz, hCsub hz⟩⟩, hCnhds, htraceball, ?_⟩
  have hcomponents := exists_connectedComponentIn_pair_closedStar_sdiff hAT hpA hKlink (hAM p hpA)
  rwa [hA] at hcomponents

end DifferentialGeometry.Topology.PiecewiseLinear
