/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness
import DifferentialGeometry.Topology.Connected.BicollarSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    (hconn : IsPreconnected K.space) {J : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hBd : Disjoint J (boundaryComplex 2 K).space) :
    ∃ a ∈ K.space \ J, ∃ b ∈ K.space \ J, ∀ x ∈ K.space \ J,
      connectedComponentIn (K.space \ J) x = connectedComponentIn (K.space \ J) a ∨
      connectedComponentIn (K.space \ J) x = connectedComponentIn (K.space \ J) b := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  obtain ⟨W, ρ, _, hWK, _, hW, hρ, hzero⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK hBd
      (U := univ) Filter.univ_mem
  exact Topology.exists_connectedComponentIn_pair_sdiff_of_bicollar hconn hJ.isConnected
    hJ.isPolyhedron.isClosed (hWK.trans sdiff_subset) hW
    hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero

theorem IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    (hconn : IsPreconnected K.space) {J : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space) :
    ∃ a ∈ K.space \ J, ∃ b ∈ K.space \ J, ∀ x ∈ K.space \ J,
      connectedComponentIn (K.space \ J) x = connectedComponentIn (K.space \ J) a ∨
      connectedComponentIn (K.space \ J) x = connectedComponentIn (K.space \ J) b := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  obtain ⟨W, ρ, _, hWK, _, hW, hρ, hzero⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK (U := univ) Filter.univ_mem
  exact Topology.exists_connectedComponentIn_pair_sdiff_of_bicollar hconn hJ.isConnected
    hJ.isPolyhedron.isClosed hWK hW hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero

open Classical in
theorem
    IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_separating_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    (hconn : IsPreconnected K.space) {J : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hBd : Disjoint J (boundaryComplex 2 K).space) (hsep : ¬ IsPreconnected (K.space \ J)) :
    ∃ a ∈ K.space \ J, ∃ b ∈ K.space \ J,
      let A := connectedComponentIn (K.space \ J) a
      let B := connectedComponentIn (K.space \ J) b
      Disjoint A B ∧ A ∪ B = K.space \ J ∧
        closure A ∪ closure B = K.space ∧ closure A ∩ closure B = J := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  obtain ⟨W, ρ, _, hWK, _, hW, hρ, hzero⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK hBd
      (U := univ) Filter.univ_mem
  exact Topology.exists_connectedComponentIn_pair_sdiff_of_separating_bicollar
    hconn (isPolyhedron_space K).isClosed hJ.isConnected hJ.isPolyhedron.isClosed
    (hWK.trans sdiff_subset) hW hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero hsep

theorem IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_separating_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    (hconn : IsPreconnected K.space) {J : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hsep : ¬ IsPreconnected (K.space \ J)) :
    ∃ a ∈ K.space \ J, ∃ b ∈ K.space \ J,
      let A := connectedComponentIn (K.space \ J) a
      let B := connectedComponentIn (K.space \ J) b
      Disjoint A B ∧ A ∪ B = K.space \ J ∧
        closure A ∪ closure B = K.space ∧ closure A ∩ closure B = J := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  obtain ⟨W, ρ, _, hWK, _, hW, hρ, hzero⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK (U := univ) Filter.univ_mem
  exact Topology.exists_connectedComponentIn_pair_sdiff_of_separating_bicollar
    hconn (isPolyhedron_space K).isClosed hJ.isConnected hJ.isPolyhedron.isClosed
    hWK hW hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero hsep

end DifferentialGeometry.Topology.PiecewiseLinear
