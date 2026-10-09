/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryBallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsIsPLBallSupersetOfExteriorCompression
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorDensity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable local instance boundaryBallComplementDecidableEq :
    DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_of_isPLSphere_boundaryComplex
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hB : IsPLSphere 2 (boundaryComplex 3 K).space) : IsPLBall 3 K.space := by
  have hfront : frontier K.space = (boundaryComplex 3 K).space :=
    frontier_space_eq_boundaryComplex_space hK
  have hopen : IsOpen (K.space \ (boundaryComplex 3 K).space) := by
    rw [← hfront, self_sdiff_frontier]
    exact isOpen_interior
  have hne : (K.space \ (boundaryComplex 3 K).space).Nonempty :=
    closure_nonempty_iff.mp ((hB.nonempty.mono (boundaryComplex_space_subset 3 K)).mono
      hK.space_subset_closure_sdiff_boundaryComplex_space)
  exact (hB.isPLBall_of_isOpen_sdiff (isPolyhedron_space K).isCompact
    (boundaryComplex_space_subset 3 K) hopen hne).1

open Classical in
theorem isPLBall_closure_sdiff_of_boundary_disk_euclidean
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsPLBall 3 K.space) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : IsPLBall 3 A) (hAK : A ⊆ K.space)
    (hD : IsPLBall 2 (A ∩ (boundaryComplex 3 K).space)) :
    IsPLBall 3 (closure (K.space \ A)) := by
  obtain ⟨C, hCfin, hCspace⟩ := hA.isPolyhedron.exists_simplicialComplex
  let _ : Finite C.faces := hCfin.to_subtype
  obtain ⟨R, H, hRfin, hR, hRspace, hH, -⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_boundary_complement K C
      (hCspace.symm ▸ hA) (hCspace.symm ▸ hAK) (by rw [hCspace]; exact hD)
  let _ : Finite R.faces := hRfin.to_subtype
  have hsphere := (isPLSphere_boundaryComplex_space_of_isPLBall K hK).of_isPLHomeomorphOn hH
  have hball := hR.isPLBall_of_isPLSphere_boundaryComplex R hsphere
  simpa only [hRspace, hCspace] using hball

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isPLBall_closure_sdiff_of_boundary_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    {A : Set E} (hA : IsPLBall 3 A) (hAK : A ⊆ K.space)
    (hD : IsPLBall 2 (A ∩ (boundaryComplex 3 K).space)) :
    IsPLBall 3 (closure (K.space \ A)) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := 2) (by simp) (0 : EuclideanSpace ℝ (Fin 3)) Filter.univ_mem
  let R := simplexComplex T hT
  let _ : Finite R.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hRspace : R.space = convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hR : IsPLBall 3 R.space := hRspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hcard
  obtain ⟨f, hf⟩ := hK
  obtain ⟨g, hg⟩ := hR
  have hK : IsPLBall 3 K.space := ⟨f, hf⟩
  have hR : IsPLBall 3 R.space := ⟨g, hg⟩
  let u := g ∘ Function.invFunOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 4))
  have hu : IsPLHomeomorphOn u K.space R.space := hf.symm.trans hg
  have hA' := hA.of_isPLHomeomorphOn (hu.restrict hA.isPolyhedron hAK)
  have hD' : IsPLBall 2 ((u '' A) ∩ (boundaryComplex 3 R).space) := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn K R
      hK.isCombinatorialManifoldWithBoundary hu,
      ← hu.bijOn.injOn.image_inter hAK (boundaryComplex_space_subset 3 K)]
    exact hD.of_isPLHomeomorphOn
      (hu.restrict hD.isPolyhedron (inter_subset_left.trans hAK))
  have hball := isPLBall_closure_sdiff_of_boundary_disk_euclidean R hR hA'
    ((image_mono hAK).trans hu.image_eq.subset) hD'
  have himage : u '' closure (K.space \ A) = closure (R.space \ u '' A) := by
    rw [hu.image_closure hK.isPolyhedron.isCompact sdiff_subset,
      hu.bijOn.injOn.image_sdiff_subset hAK, hu.image_eq]
  rw [← himage] at hball
  exact hball.of_isPLHomeomorphOn (hu.restrict
    (hK.isPolyhedron.closure_sdiff hA.isPolyhedron)
    (closure_minimal sdiff_subset hK.isPolyhedron.isClosed)).symm

end DifferentialGeometry.Topology.PiecewiseLinear
