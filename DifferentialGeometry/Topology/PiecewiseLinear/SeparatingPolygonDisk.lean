/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleComponentClosure
import DifferentialGeometry.Topology.PiecewiseLinear.EuclideanSurfaceOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.EulerUnion
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsIsPLBallSupersetOfExteriorCompression
import DifferentialGeometry.Topology.PiecewiseLinear.OrientableSurfaceEulerParity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCombinatorialManifold.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hconn : IsConnected K.space) (hor : IsOrientable 2 K) (hχ : 0 ≤ eulerChar K)
    {J : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hsep : ¬ IsPreconnected (K.space \ J)) :
    ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E), IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
      Δ ⊆ K.space ∧ J = r '' stdSimplexBoundary 2 := by
  obtain ⟨A, B, hAfin, hBfin, hA, hB, hAo, hBo, hAc, hBc, hcover, hmeet, hAbd, hBbd, -⟩ :=
    hK.exists_manifold_pair_of_separating_circle K hor hconn.isPreconnected hJ hJK hsep
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hsum : eulerChar K = eulerChar A + eulerChar B :=
    eulerChar_eq_add_of_space_union_of_isPLSphere_one K A B hcover.symm (hmeet.symm ▸ hJ)
  obtain ⟨a, ha⟩ := hA.odd_eulerChar_of_isOrientable A hAc hAo hJ hAbd
  obtain ⟨b, hb⟩ := hB.odd_eulerChar_of_isOrientable B hBc hBo hJ hBbd
  have hA1 := hA.eulerChar_le_one_of_isPLSphere_one A hAc hJ hAbd
  have hB1 := hB.eulerChar_le_one_of_isPLSphere_one B hBc hJ hBbd
  have hdisk (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
      (hM : IsCombinatorialManifoldWithBoundary 2 M) (hMc : IsConnected M.space)
      (hMbd : (boundaryComplex 2 M).space = J) (hMK : M.space ⊆ K.space)
      (hM1 : eulerChar M = 1) :
      ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E), IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
        Δ ⊆ K.space ∧ J = r '' stdSimplexBoundary 2 := by
    obtain ⟨r, hr, hrJ⟩ := hM.exists_isPLHomeomorphOn_of_eulerChar_eq_one M hMc hJ hMbd hM1
    exact ⟨M.space, r, hr, hMK, hrJ.symm⟩
  rcases (by omega : eulerChar A = 1 ∨ eulerChar B = 1) with hA1' | hB1'
  · exact hdisk A hA hAc hAbd (hcover ▸ subset_union_left) hA1'
  · exact hdisk B hB hBc hBbd (hcover ▸ subset_union_right) hB1'

theorem IsPLTorus.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff
    {T G : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsPLTorus T) (hG : IsPLSphere 1 G)
    (hGT : G ⊆ T) (hsep : ¬ IsPreconnected (T \ G)) :
    ∃ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T ∧ G = r '' stdSimplexBoundary 2 := by
  obtain ⟨L, hLfin, hL, hLc, hLT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hLo := hL.isOrientable_euclidean_three L hLc
  have hβ := hT.bettiOne_le_two
  have hχ := hL.eulerChar_eq_two_sub_bettiOne_of_isOrientable L hLc hLo
  subst hLT
  exact hL.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff L hLc hLo
    (by omega) hG hGT hsep

end DifferentialGeometry.Topology.PiecewiseLinear
