/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.RelativePush
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_frontier_of_delete_free_tetrahedron
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces] (hK : IsPLBall 3 K.space) (hL : IsPLBall 3 L.space)
    (hLK : L.faces ⊆ K.faces) {t : Finset (EuclideanSpace ℝ (Fin 3))}
    (ht : t ∈ K.faces) (htcard : t.card = 4)
    (hdelete : ∀ u ∈ K.faces, u.card = 4 → (u ∈ L.faces ↔ u ≠ t))
    (hD : IsPLBall 2 (frontier K.space ∩ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3)))))
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (htU : convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3))) ⊆ U) :
    ∃ h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn h univ univ ∧ h '' frontier K.space = frontier L.space ∧ EqOn h id Uᶜ := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  let S := frontier K.space
  let Q := convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3)))
  let D := S ∩ Q
  let A := closure (S \ D)
  have hQclosed : IsClosed Q := (t.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hQK : Q ⊆ K.space := K.convexHull_subset_space ht
  have hSQ : D ⊆ frontier Q := by
    rintro x ⟨hxS, hxQ⟩
    exact ⟨subset_closure hxQ, fun hxint => hxS.2 (interior_mono hQK hxint)⟩
  have hS : IsPLSphere 2 S := hK.isPLSphere_frontier
  have hDS : D ⊆ S := inter_subset_left
  have hA : IsPLBall 2 A := hS.isPLBall_closure_sdiff hD hDS
  obtain ⟨f, hf⟩ := hD
  have hJ : D ∩ A = f '' stdSimplexBoundary 2 :=
    hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hf hDS
  have hAS : A ⊆ S := closure_minimal sdiff_subset isClosed_frontier
  have hQA : Q ∩ A ⊆ f '' stdSimplexBoundary 2 := by
    rintro x ⟨hxQ, hxA⟩
    rw [← hJ]
    exact ⟨⟨hAS hxA, hxQ⟩, hxA⟩
  have hdense : A ⊆ closure (A \ Q) := by
    apply closure_mono
    rintro x ⟨hxS, hxD⟩
    exact ⟨subset_closure ⟨hxS, hxD⟩, fun hxQ => hxD ⟨hxS, hxQ⟩⟩
  have hpush : HasPushPropertyAt Q D :=
    (hasPushProperty_convexHull_simplex t (K.indep ht) htcard).2 D ⟨f, hf⟩ hSQ
  obtain ⟨h, hh, -, -, hfix, himage⟩ :=
    hpush.exists_homeomorph_fixed_on_of_inter_subset hf hA.isPolyhedron hQA hdense hU htU
  have hSA : D ∪ A = S := by
    apply Subset.antisymm (union_subset hDS hAS)
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  rw [hSA] at himage
  have hAeq : A = closure (S \ Q) := by
    apply congrArg closure
    ext x
    simp only [mem_sdiff, mem_inter_iff, D]
    tauto
  have hside : closure (frontier Q \ D) = closure (frontier Q \ S) := by
    apply congrArg closure
    ext x
    constructor
    · rintro ⟨hxQ, hxD⟩
      exact ⟨hxQ, fun hxS => hxD ⟨hxS, hQclosed.frontier_subset hxQ⟩⟩
    · rintro ⟨hxQ, hxS⟩
      exact ⟨hxQ, fun hxD => hxS hxD.1⟩
  have htarget : frontier L.space = A ∪ closure (frontier Q \ D) := by
    have hbd := boundaryComplex_space_of_delete_facet (n := 2) K L hK hL hLK ht htcard hdelete
    rw [← frontier_space_eq_boundaryComplex_space hK.isCombinatorialManifoldWithBoundary,
      ← frontier_space_eq_boundaryComplex_space hL.isCombinatorialManifoldWithBoundary,
      ← frontier_convexHull_eq_simplexBoundary (K.indep ht) (by
        simpa only [finrank_euclideanSpace, Fintype.card_fin] using htcard)] at hbd
    rw [hAeq, hside]
    exact hbd
  refine ⟨h, hh, ?_, hfix⟩
  exact (himage.trans (union_comm _ _)).trans htarget.symm

end DifferentialGeometry.Topology.PiecewiseLinear
