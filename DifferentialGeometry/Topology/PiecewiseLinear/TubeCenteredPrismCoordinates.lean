/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SplitDiskCenter
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitCenteredPrism

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem exists_prism_coordinates_of_PL_ball_pair
    {P Q D : Set E3} (hP : IsPLBall 3 P) (hQ : IsPLBall 3 Q)
    (hPQ : P ∩ Q = D) (hDP : D ⊆ frontier P) (hDQ : D ⊆ frontier Q)
    {r : (Fin 3 → ℝ) → E3}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) :
    ∃ ρ : (Fin 3 → ℝ) × ℝ → E3,
      IsPLHomeomorphOn ρ
        (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) (P ∪ Q) ∧
      (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), ρ (x, 0) = r x) ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = P ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = Q := by
  classical
  obtain ⟨L, hLfin, hLspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨M, hMfin, hMspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  let _ : Finite M.faces := hMfin.to_subtype
  have hL : IsPLBall 3 L.space := hLspace.symm ▸ hP
  have hM : IsPLBall 3 M.space := hMspace.symm ▸ hQ
  have hLman : IsCombinatorialManifoldWithBoundary 3 L :=
    IsPLBall.isCombinatorialManifoldWithBoundary hL
  have hMman : IsCombinatorialManifoldWithBoundary 3 M :=
    IsPLBall.isCombinatorialManifoldWithBoundary hM
  have hDL : D ⊆ (@boundaryComplex E3 _ _ (Classical.decEq E3) 3 L).space := by
    have hbd : frontier L.space =
        (@boundaryComplex E3 _ _ (Classical.decEq E3) 3 L).space :=
      frontier_space_eq_boundaryComplex_space hLman
    rw [← hbd, hLspace]
    exact hDP
  have hDM : D ⊆ (@boundaryComplex E3 _ _ (Classical.decEq E3) 3 M).space := by
    have hbd : frontier M.space =
        (@boundaryComplex E3 _ _ (Classical.decEq E3) 3 M).space :=
      frontier_space_eq_boundaryComplex_space hMman
    rw [← hbd, hMspace]
    exact hDQ
  have hLM : L.space ∩ M.space = D := by
    rw [hLspace, hMspace]
    exact hPQ
  obtain ⟨ρ, hρ, hρmid, hρminus, hρplus⟩ :=
    exists_isPLHomeomorphOn_centered_prism_of_boundary_disk_pair
      (E := Fin 3 → ℝ) (F := E3) (P := Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      (D := D) (g := r) (isPLBall_stdSimplex 2) L M hL hM hDL hDM hLM hr
  simp only [hLspace, hMspace] at hρ hρminus hρplus
  exact ⟨ρ, hρ, hρmid, hρminus, hρplus⟩

open Classical in
theorem IsTube.exists_prism_coordinates_extending_split_disk
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N')
    {u v : E3} (hu : u ∈ K.vertices) (hv : v ∈ K.vertices)
    (huv : u ≠ v) (he : ({u, v} : Finset E3) ∈ K.faces) :
    ∃ (r : (Fin 3 → ℝ) → E3) (ρ : (Fin 3 → ℝ) × ℝ → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D {u, v}) ∧
      r '' stdSimplexBoundary 2 = Dbd {u, v} ∧
      r (stdCenter 1) = ({u, v} : Finset E3).centroid ℝ id ∧
      IsPLHomeomorphOn ρ
        (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) (C u ∪ C v) ∧
      (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), ρ (x, 0) = r x) ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = C u ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = C v := by
  have hcard : ({u, v} : Finset E3).card = 2 := Finset.card_pair huv
  obtain ⟨r, hr, hrbd, hrcenter⟩ :=
    ht.exists_centered_splitDisk_parametrization he hcard
  have hPQ : C u ∩ C v = D {u, v} := ht.interEdge hu hv huv he
  have hDP : D {u, v} ⊆ frontier (C u) :=
    ht.splitDisk_subset_frontier hu he hcard (by simp)
  have hDQ : D {u, v} ⊆ frontier (C v) :=
    ht.splitDisk_subset_frontier hv he hcard (by simp)
  obtain ⟨ρ, hρ, hρmid, hρminus, hρplus⟩ :=
    exists_prism_coordinates_of_PL_ball_pair
      (ht.dualBall u hu) (ht.dualBall v hv) hPQ hDP hDQ hr
  exact ⟨r, ρ, hr, hrbd, hrcenter, hρ, hρmid, hρminus, hρplus⟩

theorem IsTube.isEmbedding_dualBall_pair
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N')
    {u v : E3} (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) :
    IsEmbedding ((C u ∪ C v).domRestrict h) := by
  have hsub : C u ∪ C v ⊆ N := by
    rw [ht.unionEq]
    rintro x (hx | hx)
    · exact mem_iUnion₂.mpr ⟨u, hu, hx⟩
    · exact mem_iUnion₂.mpr ⟨v, hv, hx⟩
  exact ht.isEmbedding.comp (IsEmbedding.inclusion hsub)

open Classical in
theorem IsTube.exists_centered_prism_coordinates
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N')
    {u v : E3} (hu : u ∈ K.vertices) (hv : v ∈ K.vertices)
    (huv : u ≠ v) (he : ({u, v} : Finset E3) ∈ K.faces) :
    ∃ ρ : (Fin 3 → ℝ) × ℝ → E3,
      IsPLHomeomorphOn ρ
        (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) (C u ∪ C v) ∧
      ρ (stdCenter 1, 0) = ({u, v} : Finset E3).centroid ℝ id ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(0 : ℝ)}) = D {u, v} ∧
      ρ '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}) = Dbd {u, v} ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = C u ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = C v := by
  obtain ⟨r, ρ, hr, hrbd, hrcenter, hρ, hρmid, hρminus, hρplus⟩ :=
    ht.exists_prism_coordinates_extending_split_disk hu hv huv he
  refine ⟨ρ, hρ, ?_, ?_, ?_, hρminus, hρplus⟩
  · have hc : stdCenter 1 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
      openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 1)
    rw [hρmid _ hc, hrcenter]
  · ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      change t = 0 at ht
      subst t
      rw [hρmid x hx]
      exact hr.bijOn.mapsTo hx
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hr.bijOn.surjOn hy
      exact ⟨(x, 0), ⟨hx, rfl⟩, (hρmid x hx).trans hxy⟩
  · calc
      ρ '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}) = r '' stdSimplexBoundary 2 := by
        ext y
        constructor
        · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
          change t = 0 at ht
          subst t
          exact ⟨x, hx, (hρmid x hx.1).symm⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨(x, 0), ⟨hx, rfl⟩, hρmid x hx.1⟩
      _ = Dbd {u, v} := hrbd

end DifferentialGeometry.Topology.PiecewiseLinear
