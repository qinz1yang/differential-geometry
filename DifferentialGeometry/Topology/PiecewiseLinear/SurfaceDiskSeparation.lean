/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskCircleComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingPolygonDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.inter_closure_sdiff_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    {D : Set E} {q : (Fin 3 → ℝ) → E} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDK : D ⊆ K.space) : D ∩ closure (K.space \ D) = q '' stdSimplexBoundary 2 := by
  classical
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  obtain ⟨A, hAfin, hAD⟩ := (IsPLBall.isPolyhedron ⟨q, hq⟩).exists_simplicialComplex
  have : Finite A.faces := hAfin.to_subtype
  have hqA : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A.space := hAD.symm ▸ hq
  have hA : IsPLBall 2 A.space := ⟨q, hqA⟩
  have hKA : A.space ⊆ K.space := hAD.subset.trans hDK
  have hKb : (boundaryComplex 2 K).space = ∅ := by
    rw [Geometry.SimplicialComplex.space, hK.boundaryComplex_faces_eq_empty K]
    simp
  have hAb : (boundaryComplex 2 A).space = q '' stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex A hqA,
      simplexBoundary_stdVertices_space]
  have hmeet := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary K A
    hK.isCombinatorialManifoldWithBoundary hA.isCombinatorialManifoldWithBoundary hKA
    (by rw [hKb]; exact disjoint_empty _)
  rwa [hAD, hAb] at hmeet

theorem IsCombinatorialManifold.subset_or_disjoint_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    {D Y : Set E} {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (hY : IsPreconnected Y) (hYK : Y ⊆ K.space)
    (hYJ : Disjoint Y (q '' stdSimplexBoundary 2)) : Y ⊆ D ∨ Disjoint D Y := by
  have hD : IsPLBall 2 D := ⟨q, hq⟩
  have hmeet := hK.inter_closure_sdiff_disk K hq hDK
  have hcover : Y ⊆ D ∪ closure (K.space \ D) := fun y hy => by
    by_cases hyD : y ∈ D
    · exact Or.inl hyD
    · exact Or.inr (subset_closure ⟨hYK hy, hyD⟩)
  have hdis : Y ∩ (D ∩ closure (K.space \ D)) = ∅ := by
    rw [hmeet]
    exact hYJ.inter_eq
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hY D (closure (K.space \ D))
      hD.isPolyhedron.isClosed isClosed_closure hcover hdis with h | h
  · exact Or.inl h
  · right
    apply Set.disjoint_left.mpr
    intro y hyD hyY
    exact Set.disjoint_left.mp hYJ hyY (hmeet.subset ⟨hyD, h hyY⟩)

theorem IsCombinatorialManifold.disjoint_disk_of_essential_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    {D G : Set E} {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (hG : IsPLSphere 1 G) (hGK : G ⊆ K.space)
    (hGJ : Disjoint G (q '' stdSimplexBoundary 2))
    (hess : ¬ ∃ (D' : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' ∧ D' ⊆ K.space ∧
        G = r '' stdSimplexBoundary 2) : Disjoint D G := by
  rcases hK.subset_or_disjoint_disk K hq hDK hG.isConnected.isPreconnected hGK hGJ with hGD | hd
  · obtain ⟨R, Q, r, -, hr, hcover, -, hbd, -⟩ :=
      hq.exists_disk_complement_of_circle hG hGD hGJ
    exact (hess ⟨Q, r, hr, (subset_union_right.trans hcover.subset).trans hDK, hbd.symm⟩).elim
  · exact hd

theorem IsPLTorus.disjoint_disk_of_essential_circle
    {T D G : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsPLTorus T)
    {q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDT : D ⊆ T)
    (hG : IsPLSphere 1 G) (hGT : G ⊆ T) (hGJ : Disjoint G (q '' stdSimplexBoundary 2))
    (hess : ¬ ∃ (D' : Set (EuclideanSpace ℝ (Fin 3)))
      (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' ∧ D' ⊆ T ∧
        G = r '' stdSimplexBoundary 2) : Disjoint D G := by
  obtain ⟨K, hKfin, hK, -, hKT⟩ := hT.exists_combinatorial_triangulation
  have : Finite K.faces := hKfin.to_subtype
  exact hK.disjoint_disk_of_essential_circle K hq (hDT.trans hKT.symm.subset)
    hG (hGT.trans hKT.symm.subset) hGJ (by simpa only [hKT] using hess)

end DifferentialGeometry.Topology.PiecewiseLinear
