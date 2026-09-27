/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness
import DifferentialGeometry.Topology.Connected.LocalSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem local_separation_of_surface
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space) :
    ∀ p ∈ L.space, ∃ C ∈ 𝓝[K.space] p, C ⊆ K.space ∧
      ∃ A B : Set E, IsConnected A ∧ IsConnected B ∧ A ∪ B = C \ L.space ∧
        C ∩ L.space ⊆ closure A ∧ C ∩ L.space ⊆ closure B := by
  intro p hp
  obtain ⟨C, -, hCsub, hCnhds, -, a, ha, b, hb, -, hunion, -, -, -, hinter⟩ :=
    hK.exists_isPLBall_neighborhood_pair_sdiff hL hLK hp
      (fun hpB => disjoint_left.mp hB hp hpB) Filter.univ_mem
  exact ⟨C, hCnhds, hCsub.trans inter_subset_left,
    connectedComponentIn (C \ L.space) a, connectedComponentIn (C \ L.space) b,
    isConnected_connectedComponentIn_iff.mpr ha, isConnected_connectedComponentIn_iff.mpr hb,
    hunion, hinter.symm.subset.trans inter_subset_left, hinter.symm.subset.trans inter_subset_right⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.subset_closure_connectedComponentIn_sdiff_of_surface
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    (hconn : IsPreconnected L.space) {x : E}
    (hx : (L.space ∩ closure (connectedComponentIn (K.space \ L.space) x)).Nonempty) :
    L.space ⊆ closure (connectedComponentIn (K.space \ L.space) x) :=
  Topology.subset_closure_connectedComponentIn_of_local_separation hLK hconn
    (local_separation_of_surface hK hL hLK hB) hx

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_adjacent_to_surface
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    (hconn : IsConnected L.space) :
    ∃ a ∈ K.space \ L.space, ∃ b ∈ K.space \ L.space, ∀ x : E,
      (L.space ∩ closure (connectedComponentIn (K.space \ L.space) x)).Nonempty →
        connectedComponentIn (K.space \ L.space) x = connectedComponentIn (K.space \ L.space) a ∨
        connectedComponentIn (K.space \ L.space) x = connectedComponentIn (K.space \ L.space) b :=
  Topology.exists_connectedComponentIn_pair_of_local_separation hLK hconn
    (local_separation_of_surface hK hL hLK hB)

open Classical in
theorem
    IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_separating_surface
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    (hconnK : IsPreconnected K.space) (hconnL : IsConnected L.space)
    (hsep : ¬IsPreconnected (K.space \ L.space)) :
    ∃ a ∈ K.space \ L.space, ∃ b ∈ K.space \ L.space,
      let A := connectedComponentIn (K.space \ L.space) a
      let B := connectedComponentIn (K.space \ L.space) b
      Disjoint A B ∧ A ∪ B = K.space \ L.space ∧
      closure A ∪ closure B = K.space ∧ closure A ∩ closure B = L.space := by
  let : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  exact Topology.exists_connectedComponentIn_pair_sdiff_of_local_separation hconnK
    (isPolyhedron_space K).isClosed hconnL (isPolyhedron_space L).isClosed hLK
    (local_separation_of_surface hK hL hLK hB) hsep

end DifferentialGeometry.Topology.PiecewiseLinear
