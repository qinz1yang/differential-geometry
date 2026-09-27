/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLBall.dim_le_of_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n m : ℕ} {P Q : Set E} (hP : IsPLBall n P) (hQ : IsPLBall m Q) (hPQ : P ⊆ Q) :
    n ≤ m := by
  classical
  obtain ⟨K, hKfin, hKQ⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨R, hRK, hRfin, hPcov⟩ := exists_isSubdivision_subcomplexes K
    (fun _ : Unit => P) (fun _ => hP.isPolyhedron) (fun _ => hPQ.trans hKQ.symm.subset)
  let _ : Finite R.faces := hRfin.to_subtype
  let S := restrict R P
  let _ : Finite S.faces := ((Set.toFinite R.faces).subset (restrict_faces_subset R P)).to_subtype
  have hSP : S.space = P := restrict_space_of_eq_biUnion R P (hPcov ())
  have hS : IsPLBall n S.space := hSP.symm ▸ hP
  have hR : IsPLBall m R.space := (hRK.space_eq.trans hKQ).symm ▸ hQ
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨s, hs, -⟩ := S.mem_space_iff.mp hx
  obtain ⟨t, ht, -, hcard⟩ := exists_face_superset_card_eq_of_isPLBall S hS hs
  have hle := card_le_of_isPLBall R hR ((restrict_faces_subset R P) ht)
  omega

theorem IsPLCellOn.dim_le_of_subset
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {n m : ℕ} {S SB T TB : Set M} (hS : IsPLCellOn n S SB) (hT : IsPLCellOn m T TB)
    (hST : S ⊆ T) : n ≤ m := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hS
  obtain ⟨Q, s, v, hs, hv, rfl, -⟩ := hT
  have hP : IsPLBall n P := ⟨r, hr⟩
  have hQ : IsPLBall m Q := ⟨s, hs⟩
  have hf := hu.isPLHomeomorphOn_invFunOn_comp hP.isPolyhedron hv hST
  apply (hP.of_isPLHomeomorphOn hf).dim_le_of_subset hQ
  rintro _ ⟨x, hx, rfl⟩
  exact hv.injOn.bijOn_image.surjOn.mapsTo_invFunOn (hST ⟨x, hx, rfl⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
