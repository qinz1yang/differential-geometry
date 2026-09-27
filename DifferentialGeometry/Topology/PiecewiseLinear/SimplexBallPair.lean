/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCornerChart
import DifferentialGeometry.Topology.PiecewiseLinear.ConeBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem boundaryComplex_simplexAvoiding_erase_space {n : ℕ}
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = n + 3)
    {a : E} (ha : a ∈ T) :
    (boundaryComplex (n + 1) (simplexAvoiding T hT {T.erase a})).space =
      (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).space
          := by
  let _ : DecidableEq E := Classical.decEq _
  let L := simplexAvoiding T hT {T.erase a}
  let F := T.erase a
  let hF := affineIndependent_of_subset hT (Finset.erase_subset a T)
  let M := simplexComplex F hF
  let B := simplexBoundary F hF
  have hFcard : F.card = n + 2 := by dsimp [F]; rw [Finset.card_erase_of_mem ha, hcard]; omega
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  let _ : Finite L.faces := (simplexAvoiding_faces_finite T hT {T.erase a}).to_subtype
  let _ : Finite M.faces := (simplexComplex_faces_finite F hF).to_subtype
  have hL : IsPLBall (n + 1) L.space :=
    isPLBall_simplexAvoiding_singleton (hT := hT) (by omega) (Finset.erase_subset a T) hFne
      (fun h => Finset.notMem_erase a T (h.symm ▸ ha))
  let g := simplicialMap (starComplex (simplexBoundary T hT) a)
    (Function.update id a (F.centroid ℝ id))
  have hg : IsPLHomeomorphOn g L.space M.space := by
    rw [simplexComplex_space F hF hFne]
    change IsPLHomeomorphOn g (simplexAvoiding T hT {T.erase a}).space (convexHull ℝ (F : Set E))
    rw [simplexAvoiding_erase_eq_starComplex T hT ha]
    exact isPLHomeomorphOn_simplicialMap_simplex_vertex_star T hT (by omega) ha
  have hBsub : B.space ⊆ L.space := space_mono_of_faces_subset
    (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a)
  have hfix : EqOn g id B.space := eqOn_simplicialMap_simplex_vertex_star_boundary T hT ha
  have hImageB : g '' B.space = B.space := hfix.image_eq.trans (image_id _)
  have hboundary := boundaryComplex_space_of_isPLHomeomorphOn L M
      hL.isCombinatorialManifoldWithBoundary hg
  have hBM : (boundaryComplex (n + 1) M).space = B.space := by
    rw [boundaryComplex_simplexComplex hF hFcard]
  apply (hg.bijOn.injOn.image_eq_image_iff (boundaryComplex_space_subset (n + 1) L) hBsub).mp
  rw [← hboundary, hBM, hImageB]

theorem exists_isPLBall_pair_with_disk_inter :
    ∃ P Q : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLBall 3 Q ∧ IsPLBall 3 (P ∪ Q) ∧ IsPLBall 2 (P ∩ Q) ∧
        P ∩ Q ⊆ frontier P ∧ P ∩ Q ⊆ frontier Q := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (E := EuclideanSpace ℝ (Fin 3)) (n := 2) (by simp) 0 (U := univ) Filter.univ_mem
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  let F := T.erase a
  let hF := affineIndependent_of_subset hT (Finset.erase_subset a T)
  let B := simplexBoundary F hF
  let L := simplexAvoiding T hT {T.erase a}
  let p := T.centroid ℝ id
  have hpopen : p ∈ openSimplex T := centroid_mem_openSimplex (Finset.card_pos.mp (by omega))
  have hFcard : F.card = 3 := by dsimp [F]; rw [Finset.card_erase_of_mem ha, hcard]
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  have hpF : p ∉ F := notMem_erase_of_mem_openSimplex hT hpopen ha
  have hpind : AffineIndependent ℝ ((↑) : ↥(insert p F : Finset _) → EuclideanSpace ℝ (Fin 3)) :=
    affineIndependent_insert_erase hT hpopen ha
  have hpFcard : (insert p F).card = 4 := by rw [Finset.card_insert_of_notMem hpF, hFcard]
  have hspan : affineSpan ℝ ((insert p F : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) = ⊤ := by
    have h := hpind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simp only [Fintype.card_coe, hpFcard, finrank_euclideanSpace, Fintype.card_fin])
    have hrange : range ((↑) : ↥(insert p F : Finset _) → EuclideanSpace ℝ (Fin 3)) =
        ((insert p F : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) := Subtype.range_coe
    rwa [hrange] at h
  let hp : IsConeBase p L := (isConeBase_simplexBoundary hT (by omega) hpopen).of_faces_subset
    (simplexAvoiding_erase_faces_subset_simplexBoundary T hT a)
  let hpB : IsConeBase p B :=
    hp.of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a)
  let _ : Finite B.faces := (simplexBoundary_faces_finite F hF).to_subtype
  let _ : Finite L.faces := (simplexAvoiding_faces_finite T hT {T.erase a}).to_subtype
  have hL : IsPLBall 2 L.space :=
    isPLBall_simplexAvoiding_singleton (hT := hT) hcard (Finset.erase_subset a T) hFne
      (fun h => Finset.notMem_erase a T (h.symm ▸ ha))
  have hB : IsPLSphere 1 B.space := by
    let _ : Finite (simplexComplex F hF).faces := (simplexComplex_faces_finite F hF).to_subtype
    have hball : IsPLBall 2 (simplexComplex F hF).space := by
      rw [simplexComplex_space F hF hFne]
      exact isPLBall_convexHull_of_affineIndependent F hF hFcard
    have h := isPLSphere_boundaryComplex_space_of_isPLBall (simplexComplex F hF) hball
    rw [boundaryComplex_simplexComplex hF hFcard] at h
    exact h
  let P := (coneComplex hp).space
  let Q := convexHull ℝ ((insert p F : Finset _) : Set (EuclideanSpace ℝ (Fin 3)))
  have hP : IsPLBall 3 P := hp.isPLBall_of_isPLBall hL
  have hQ : IsPLBall 3 Q := isPLBall_convexHull_of_affineIndependent _ hpind hpFcard
  have hunion : P ∪ Q = convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) :=
    coneComplex_simplexAvoiding_union_convexHull T hT ha hpopen hp
  have hinter : P ∩ Q = (coneComplex hpB).space :=
    coneComplex_simplexAvoiding_inter_convexHull T hT (by omega) ha hpopen hp
  have hBP : (coneComplex hpB).space ⊆ frontier P := by
    rw [frontier_coneComplex (n := 1) (by simp) hp hL]
    have hbase : (boundaryComplex 2 L).space = B.space :=
      boundaryComplex_simplexAvoiding_erase_space T hT hcard ha
    have hcones : (coneComplex hpB).space =
        (coneComplex (hp.of_faces_subset (boundaryComplex_faces_subset 2 L))).space := by
      ext x
      rw [mem_coneComplex_space_iff, mem_coneComplex_space_iff, hbase]
    rw [hcones]
    exact subset_union_right
  have hBQ : (coneComplex hpB).space ⊆ frontier Q := by
    rw [frontier_convexHull_insert_eq_union_coneComplex F hF hFne hpF hpind hspan hpB]
    exact subset_union_right
  refine ⟨P, Q, hP, hQ, ?_, ?_, ?_, ?_⟩
  · rw [hunion]
    exact isPLBall_convexHull_of_affineIndependent T hT hcard
  · rw [hinter]
    exact hpB.isPLBall_of_isPLSphere hB
  · rwa [hinter]
  · rwa [hinter]

end DifferentialGeometry.Topology.PiecewiseLinear
