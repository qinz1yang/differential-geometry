/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeComponents
import DifferentialGeometry.Topology.PiecewiseLinear.StarIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_connectedComponentIn_pair_closedStar_sdiff
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hLK : L.faces ⊆ K.faces) {p : E} (hp : {p} ∈ L.faces)
    (hK : IsPLSphere 2 (SimplicialComplex.geometricLink K {p}).space)
    (hL : IsPLSphere 1 (SimplicialComplex.geometricLink L {p}).space) :
    ∃ x ∈ closedStar (barycentricSubdivision K) p \ L.space,
      ∃ y ∈ closedStar (barycentricSubdivision K) p \ L.space,
        let C₀ := connectedComponentIn (closedStar (barycentricSubdivision K) p \ L.space) x
        let C₁ := connectedComponentIn (closedStar (barycentricSubdivision K) p \ L.space) y
        Disjoint C₀ C₁ ∧ C₀ ∪ C₁ = closedStar (barycentricSubdivision K) p \ L.space ∧
        IsPLBall 3 (closure C₀) ∧ IsPLBall 3 (closure C₁) ∧
        closure C₀ ∪ closure C₁ = closedStar (barycentricSubdivision K) p ∧
        closure C₀ ∩ closure C₁ = closedStar (barycentricSubdivision K) p ∩ L.space := by
  classical
  let : Finite L.faces := ((Set.toFinite K.faces).subset hLK).to_subtype
  let K' := barycentricSubdivision K
  let L' := barycentricSubdivision L
  have hpK' : {p} ∈ K'.faces := (barycentricSubdivision_isSubdivision K).singleton_mem (hLK hp)
  have hpL' : {p} ∈ L'.faces := (barycentricSubdivision_isSubdivision L).singleton_mem hp
  have hL'K' : L'.faces ⊆ K'.faces := barycentricSubdivision_faces_subset hLK
  have hlinks : (SimplicialComplex.geometricLink L' {p}).faces ⊆
      (SimplicialComplex.geometricLink K' {p}).faces := by
    intro t ht
    rw [SimplicialComplex.mem_geometricLink_singleton] at ht ⊢
    exact ⟨ht.1, ht.2.1, hL'K' ht.2.2⟩
  have hK' : IsPLSphere 2 (SimplicialComplex.geometricLink K' {p}).space :=
    (isPLSphere_geometricLink_iff_of_isSubdivision (barycentricSubdivision_isSubdivision K)
      (hLK hp)).mpr hK
  have hL' : IsPLSphere 1 (SimplicialComplex.geometricLink L' {p}).space :=
    (isPLSphere_geometricLink_iff_of_isSubdivision (barycentricSubdivision_isSubdivision L) hp).mpr
        hL
  have h := (isConeBase_geometricLink K').exists_connectedComponentIn_pair_sdiff hlinks hK' hL'
  rw [← closedStar_eq_coneComplex_space K' hpK',
    ← closedStar_eq_coneComplex_space L' hpL'] at h
  have hinter : closedStar K' p ∩ L.space = closedStar L' p :=
    closedStar_barycentricSubdivision_inter_space_eq hLK hp
  have hdiff : closedStar K' p \ closedStar L' p = closedStar K' p \ L.space := by
    rw [← hinter]
    ext z
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hdiff, ← hinter] at h
  exact h

end DifferentialGeometry.Topology.PiecewiseLinear
