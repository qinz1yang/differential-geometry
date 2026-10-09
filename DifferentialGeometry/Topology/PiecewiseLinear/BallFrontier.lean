/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.image_stdSimplexBoundary {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {f : (Fin (n + 2) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) P) :
    f '' stdSimplexBoundary (n + 1) = frontier P := by
  classical
  have hP : IsPLBall (n + 1) P := ⟨f, hf⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hfK : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) K.space := hKP.symm ▸ hf
  have hK : IsPLBall (n + 1) K.space := ⟨f, hfK⟩
  rw [← hKP, frontier_space_eq_boundaryComplex_space (n := n)
      hK.isCombinatorialManifoldWithBoundary]
  have hboundary := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hfK
  rw [simplexBoundary_stdVertices_space] at hboundary
  convert hboundary.symm using 1
  congr 2
  exact Subsingleton.elim _ _

theorem IsPLBall.isPLSphere_frontier {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPLBall (n + 1) P) :
    IsPLSphere n (frontier P) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  obtain ⟨K, hfin, rfl⟩ := hP.isPolyhedron.exists_simplicialComplex
  have := hfin.to_subtype
  rw [frontier_space_eq_boundaryComplex_space (n := n) (K := K)
    (IsPLBall.isCombinatorialManifoldWithBoundary (n := n) (K := K) hP)]
  exact isPLSphere_boundaryComplex_space_of_isPLBall (n := n) K hP

theorem IsPLHomeomorphOn.image_stdSimplexBoundary_eq_frontier {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {f : (Fin (n + 2) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) P) :
    f '' stdSimplexBoundary (n + 1) = frontier P := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  have hP : IsPLBall (n + 1) P := ⟨f, hf⟩
  obtain ⟨K, hfin, hKspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hfin.to_subtype
  have hK : IsPLBall (n + 1) K.space := hKspace.symm ▸ hP
  rw [← hKspace, frontier_space_eq_boundaryComplex_space hK.isCombinatorialManifoldWithBoundary,
    boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K (hKspace.symm ▸ hf),
    simplexBoundary_stdVertices_space]

theorem IsPLBall.interior_nonempty {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPLBall (n + 1) P) :
    (interior P).Nonempty := by
  obtain ⟨f, hf⟩ := hP
  exact ⟨f (stdCenter n),
    mem_interior_image_of_isPLHomeomorphOn_stdSimplex hf (stdCenter_mem_openSimplex n)⟩

theorem IsPLBall.closure_interior {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPLBall (n + 1) P) :
    closure (interior P) = P := by
  apply Subset.antisymm (closure_minimal interior_subset hP.isPolyhedron.isCompact.isClosed)
  obtain ⟨f, hf⟩ := hP
  have hmap : MapsTo f (openSimplex (stdVertices n)) (interior P) :=
    fun _ hx => mem_interior_image_of_isPLHomeomorphOn_stdSimplex hf hx
  have hclsub : closure (openSimplex (stdVertices n)) ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)) :=
    closure_minimal openSimplex_stdVertices_subset_stdSimplex (Convexity.StdSimplex.isCompact_coordinateSet ℝ _).isClosed
  have hclmap := hmap.closure_of_continuousOn (hf.isPiecewiseAffineOn.continuousOn.mono hclsub)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hf.bijOn.surjOn hy
  apply hclmap
  apply convexHull_subset_closure_openSimplex
    (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) (two_le_card_stdVertices n)))
  rwa [convexHull_stdVertices]

theorem IsPLBall.interior_eq_empty_of_lt_finrank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {P : Set E} (hP : IsPLBall n P) (hn : n < Module.finrank ℝ E) : interior P = ∅ := by
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall n K.space := hKP.symm ▸ hP
  rw [← hKP, Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨s, hs, hcard, -⟩ := exists_face_card_eq_finrank_succ_of_mem_closure K
    isOpen_interior interior_subset (subset_closure hx)
  have hle := card_le_of_isPLBall K hK hs
  omega

theorem IsPLBall.inter_subset_frontier_of_isPLBall {n m : ℕ}
    {P Q : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hQ : IsPLBall (n + 1) Q)
    (hI : IsPLBall m (P ∩ Q)) (hm : m < n + 1) : P ∩ Q ⊆ frontier P := by
  have hempty : interior (P ∩ Q) = ∅ :=
    hI.interior_eq_empty_of_lt_finrank (by simpa using hm)
  have hdis : interior P ∩ interior Q = ∅ := by rwa [interior_inter] at hempty
  intro x hx
  refine ⟨subset_closure hx.1, fun hxint => ?_⟩
  have hxcl : x ∈ closure (interior P ∩ interior Q) :=
    isOpen_interior.inter_closure ⟨hxint, hQ.closure_interior.symm ▸ hx.2⟩
  simp only [hdis, closure_empty, mem_empty_iff_false] at hxcl

theorem exists_isPLHomeomorphOn_of_frontier {n : ℕ}
    {P Q : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hP : IsPLBall (n + 1) P) (hQ : IsPLBall (n + 1) Q)
    {g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hg : IsPLHomeomorphOn g (frontier P) (frontier Q)) :
    ∃ G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      IsPLHomeomorphOn G P Q ∧ EqOn G g (frontier P) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  obtain ⟨K, hfinK, rfl⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hfinL, rfl⟩ := hQ.isPolyhedron.exists_simplicialComplex
  have := hfinK.to_subtype
  have := hfinL.to_subtype
  rw [frontier_space_eq_boundaryComplex_space (n := n) (K := K)
    (IsPLBall.isCombinatorialManifoldWithBoundary (n := n) (K := K) hP),
    frontier_space_eq_boundaryComplex_space (n := n) (K := L)
      (IsPLBall.isCombinatorialManifoldWithBoundary (n := n) (K := L) hQ)] at hg
  rw [frontier_space_eq_boundaryComplex_space (n := n) (K := K)
    (IsPLBall.isCombinatorialManifoldWithBoundary (n := n) (K := K) hP)]
  exact exists_isPLHomeomorphOn_of_boundaryComplex (n := n) K L hP hQ hg

end DifferentialGeometry.Topology.PiecewiseLinear
