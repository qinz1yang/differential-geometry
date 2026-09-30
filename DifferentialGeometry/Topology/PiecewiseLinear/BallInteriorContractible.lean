/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import Mathlib.Analysis.Convex.Contractible

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLBall.contractibleSpace_interior_of_finrank {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 1) {P : Set E} (hP : IsPLBall (n + 1) P) :
    ContractibleSpace (interior P) := by
  classical
  obtain ⟨f, hf⟩ := hP
  have hP : IsPLBall (n + 1) P := ⟨f, hf⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hfK : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) K.space := hKP.symm ▸ hf
  have hK : IsPLBall (n + 1) K.space := ⟨f, hfK⟩
  have hboundary : f '' stdSimplexBoundary (n + 1) = frontier P := by
    rw [← hKP, frontier_space_eq_boundaryComplex_space_of_finrank hdim K
      hK.isCombinatorialManifoldWithBoundary,
      boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hfK,
      simplexBoundary_stdVertices_space]
  have himage : f '' openSimplex (stdVertices n) = interior P := by
    rw [hf.image_openSimplex_stdVertices, hboundary, hP.isPolyhedron.isClosed.frontier_eq,
      sdiff_sdiff_cancel_left interior_subset]
  have hfull : IsEmbedding ((Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))).domRestrict f) :=
    Topology.IsEmbedding.subtypeVal.comp hf.homeomorph.isEmbedding
  have hopen : IsEmbedding ((openSimplex (stdVertices n)).domRestrict f) :=
    hfull.comp (Topology.IsEmbedding.inclusion openSimplex_stdVertices_subset_stdSimplex)
  let e : openSimplex (stdVertices n) ≃ₜ interior P := hopen.toHomeomorph.trans
    (Homeomorph.setCongr ((Set.range_domRestrict f _).trans himage))
  let _ : ContractibleSpace (openSimplex (stdVertices n)) :=
    (convex_openSimplex (stdVertices n)).contractibleSpace
      ⟨stdCenter n, stdCenter_mem_openSimplex n⟩
  exact e.symm.contractibleSpace

end DifferentialGeometry.Topology.PiecewiseLinear
