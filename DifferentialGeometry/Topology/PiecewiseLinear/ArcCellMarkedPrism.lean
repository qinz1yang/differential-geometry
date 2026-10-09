/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeMarkedPrism
import DifferentialGeometry.Topology.PiecewiseLinear.ArcCellGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_arcCell_prism_marked
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hj0 : 1 ≤ j) (hjn : j + 1 ≤ 2 * n)
    (hjB : arcChainFace v j ∉ (boundaryComplex 3 K).faces)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsHPolytope P)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ interior P)
    {g : EuclideanSpace ℝ (Fin 2) → E}
    (hg : IsPLHomeomorphOn g P
      (coneSet (arcCellCrossing v (j - 1)) (arcCellInterfaceBase K v (j - 1)).space))
    (hga : g a = arcCellCrossing v (j - 1)) :
    ∃ G : EuclideanSpace ℝ (Fin 2) × ℝ → E,
      IsPLHomeomorphOn G (P ×ˢ Icc (0 : ℝ) 1)
        (derivedNeighborhoodCell K (arcChainFace v j)).space ∧
      (∀ x ∈ P, G (x, 0) = g x) ∧ G (a, 1 / 2) = arcCellApex v j ∧
      G '' (P ×ˢ ({1} : Set ℝ)) =
        coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space ∧
      G (a, 1) = arcCellCrossing v j ∧
      G '' ({a} ×ˢ Icc (0 : ℝ) 1) =
        (derivedNeighborhoodCell K (arcChainFace v j)).space ∩
          (arcComplexIn K v n).space := by
  classical
  let _ : Finite (arcCellBase K v j).faces := (arcCellBase_faces_finite v j).to_subtype
  let _ : Finite (arcCellInterfaceBase K v j).faces :=
    (arcCellInterfaceBase_faces_finite v j).to_subtype
  have hc := isConeBase_arcCellBase (K := K) hvert hedge (j := j) (by omega)
  have hS := hK.isPLSphere_arcCellBase_of_interior hvert hedge (by omega) hjB
  have hd := isConeBase_arcCellInterfaceBase (K := K) hvert hedge hinj hjn
  have hSd := hK.isPLSphere_arcCellInterfaceBase_of_interior_left hvert hedge hinj hjn hjB
  have hD₀ := arcCellInterface_subset_arcCellBase_right
    (K := K) hvert hedge hinj (j := j - 1) (by omega)
  rw [Nat.sub_add_cancel hj0] at hD₀
  have hD₁ := arcCellInterface_subset_arcCellBase_left (K := K) hvert hedge hinj hjn
  have hprev := adjacent_derivedNeighborhoodCell_arcChainFace_inter_eq_coneSet
    (K := K) hvert hedge hinj (j := j - 1) (by omega)
  rw [Nat.sub_add_cancel hj0] at hprev
  have hnext := adjacent_derivedNeighborhoodCell_arcChainFace_inter_eq_coneSet
    (K := K) hvert hedge hinj hjn
  have hdis : Disjoint
      (coneSet (arcCellCrossing v (j - 1)) (arcCellInterfaceBase K v (j - 1)).space)
      (coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space) := by
    rw [← hprev, ← hnext]
    exact (disjoint_derivedNeighborhoodCell_arcChainFace (K := K) hvert hedge hinj
      (i := j - 1) (j := j + 1) (by omega) (by omega) (by omega)).mono
      inter_subset_left inter_subset_right
  obtain ⟨q₀, hq₀⟩ := hSd
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hqbase : IsPLHomeomorphOn q₀
      (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).space
      (arcCellInterfaceBase K v j).space := by
    rwa [simplexBoundary_stdVertices_space]
  obtain ⟨q, hq, -, hqa, -⟩ :=
    exists_isPLHomeomorphOn_coneComplex (isConeBase_std 1) hd hqbase
  rw [coneComplex_std_space, coneComplex_space_eq_coneSet] at hq
  obtain ⟨G, hG, hG0, hGc, hG1, hGa, hGaxis⟩ :=
    exists_isPLHomeomorphOn_prism_cone_marked hP ha hc hS hD₀ hD₁ hdis hg hq
  rw [← derivedNeighborhoodCell_arcChainFace_space_eq_coneSet hvert hedge (by omega)] at hG
  refine ⟨G, hG, hG0, hGc, hG1, hGa.trans hqa, ?_⟩
  rw [hGaxis, hga, hqa,
    derivedNeighborhoodCell_arcChainFace_inter_arcComplexIn_space_eq hvert hedge hinj hj0 hjn]

end DifferentialGeometry.Topology.PiecewiseLinear
