/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CommonCircleSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalShell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_spanning_disk_annular_neighborhood
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifoldWithBoundary 2 S) (hor : IsOrientable 2 S)
    (hdim : Module.finrank ℝ E = 3) {D U F : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2)
    (hF : IsClosed F) (hJF : Disjoint (r '' stdSimplexBoundary 2) F)
    (hU : IsOpen U) (hJU : r '' stdSimplexBoundary 2 ⊆ U) :
    ∃ K N : Geometry.SimplicialComplex ℝ E,
      K.faces.Finite ∧ IsPLBall 3 K.space ∧ N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 N ∧ IsTopologicalSolidTorus N.space ∧
      r '' stdSimplexBoundary 2 ⊆ interior N.space ∧ N.space ⊆ U ∧
      Disjoint N.space F ∧ (D \ N.space).Nonempty ∧
      IsCommonAnnularDerivedNeighborhood K N.space (r '' stdSimplexBoundary 2) S.space D := by
  let J := r '' stdSimplexBoundary 2
  let p := r (stdCenter 1)
  have hp : p ∈ D \ J := by
    rw [← hr.image_openSimplex_stdVertices]
    exact mem_image_of_mem r (stdCenter_mem_openSimplex 1)
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  obtain ⟨Q, hQfin, hQspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQ : IsPLBall 2 Q.space := hQspace.symm ▸ hD
  have hJ : IsPLSphere 1 J := hr.isPLSphere_image_stdSimplexBoundary
  have hJS : J ⊆ S.space := hmeet.symm.subset.trans inter_subset_right
  have hJQ : J ⊆ Q.space :=
    hmeet.symm.subset.trans (inter_subset_left.trans hQspace.symm.subset)
  have hJO : J ⊆ U \ (F ∪ {p}) := by
    intro x hx
    refine ⟨hJU hx, ?_⟩
    rintro (hxF | hxp)
    · exact disjoint_left.mp hJF hx hxF
    · exact hp.2 (mem_singleton_iff.mp hxp ▸ hx)
  obtain ⟨K, N, hKfin, hK, hNfin, hN, hsolid, hJN, hNO, hcommon⟩ :=
    exists_common_solid_torus_neighborhood_of_finrank_eq_three S Q hS
      hQ.isCombinatorialManifoldWithBoundary hor (isOrientable_of_isPLBall hQ)
      hdim hJ hJS hJQ (hU.sdiff (hF.union isClosed_singleton)) hJO
  refine ⟨K, N, hKfin, hK, hNfin, hN, hsolid, hJN, hNO.trans sdiff_subset, ?_,
    ⟨p, hp.1, ?_⟩, ?_⟩
  · exact disjoint_left.mpr fun x hx hxF => (hNO hx).2 (Or.inl hxF)
  · exact fun hpN => (hNO hpN).2 (Or.inr (mem_singleton p))
  · rwa [hQspace] at hcommon

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
open Classical in
theorem IsSphericalShell.exists_spanning_disk_annular_neighborhood
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (hX : IsSphericalShell X B₀ B₁)
    (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hconn : IsConnected S.space)
    (hsep : Separates S.space B₀ B₁)
    {D : Set (EuclideanSpace ℝ (Fin 3))} {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2) :
    ∃ K N : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      K.faces.Finite ∧ IsPLBall 3 K.space ∧ N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 N ∧ IsTopologicalSolidTorus N.space ∧
      r '' stdSimplexBoundary 2 ⊆ interior N.space ∧ N.space ⊆ interior X ∧
      Disjoint N.space B₀ ∧ Disjoint N.space B₁ ∧ (D \ N.space).Nonempty ∧
      IsCommonAnnularDerivedNeighborhood K N.space (r '' stdSimplexBoundary 2) S.space D := by
  have hJS := hmeet.symm.subset.trans inter_subset_right
  have hJF : Disjoint (r '' stdSimplexBoundary 2) (B₀ ∪ B₁) := by
    apply disjoint_left.mpr
    rintro x hx (hx₀ | hx₁)
    · exact hsep.left_subset_compl hx₀ (hJS hx)
    · exact hsep.right_subset_compl hx₁ (hJS hx)
  obtain ⟨K, N, hKfin, hK, hNfin, hN, hsolid, hJN, hNX, hdis, hremain, hcommon⟩ :=
    hS.isCombinatorialManifoldWithBoundary.exists_spanning_disk_annular_neighborhood S
      (hS.isOrientable_of_finrank_eq_three S (by simp) hconn) (by simp) hr hmeet
      (hX.isCompact_left.isClosed.union hX.isCompact_right.isClosed) hJF isOpen_interior
      (hJS.trans (hX.subset_interior_of_separates hconn.isPreconnected hsep))
  exact ⟨K, N, hKfin, hK, hNfin, hN, hsolid, hJN, hNX,
    hdis.mono_right subset_union_left, hdis.mono_right subset_union_right, hremain, hcommon⟩

end DifferentialGeometry.Topology.PiecewiseLinear
