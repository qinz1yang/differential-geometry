/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComplementComponents
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComponents
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity
import DifferentialGeometry.Topology.Connected.ComponentNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]

private theorem closure_component_mem_nhdsWithin {a p : E}
    (hp : p ∈ closure (connectedComponentIn (K.space \ L.space) a))
    (hpK : p ∈ K.space) (hpL : p ∉ L.space) :
    closure (connectedComponentIn (K.space \ L.space) a) ∈ 𝓝[K.space] p := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  have hpA := (Topology.closure_connectedComponentIn_inter (K.space \ L.space) a).subset
    ⟨hp, hpK, hpL⟩
  have hopen := Topology.isOpen_preimage_connectedComponentIn_sdiff
    (N := K.space) (isPolyhedron_space L).isClosed a
  have hnhds : connectedComponentIn (K.space \ L.space) a ∈ 𝓝[K.space] p :=
    preimage_coe_mem_nhds_subtype.mp
      (hopen.mem_nhds (show (⟨p, hpK⟩ : K.space) ∈ ((↑) : K.space → E) ⁻¹'
        connectedComponentIn (K.space \ L.space) a from hpA))
  exact Filter.mem_of_superset hnhds subset_closure

open Classical in
private theorem exists_ball_pair_in_component_closure
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    {a b p : E} (hp : p ∈ L.space)
    (hdis : Disjoint (connectedComponentIn (K.space \ L.space) a)
      (connectedComponentIn (K.space \ L.space) b))
    (hmeet : closure (connectedComponentIn (K.space \ L.space) a) ∩
      closure (connectedComponentIn (K.space \ L.space) b) = L.space) :
    ∃ C D : Set E, IsPLBall 3 C ∧ IsPLBall 3 D ∧
      C ⊆ closure (connectedComponentIn (K.space \ L.space) a) ∧
      C ∈ 𝓝[closure (connectedComponentIn (K.space \ L.space) a)] p ∧ D ⊆ K.space ∧
      p ∈ C ∩ D ∧ IsPLBall 2 (C ∩ D) := by
  obtain ⟨W, -, hW, hWnhds, htrace, x, -, y, -, -, hcover, hX, hY, hclcover, hclmeet⟩ :=
    hK.exists_isPLBall_neighborhood_pair_sdiff hL hLK hp
      (fun hpB => disjoint_left.mp hB hp hpB) Filter.univ_mem
  have hWK : W ⊆ K.space := hW.trans inter_subset_left
  have hpW : p ∈ W := mem_of_mem_nhdsWithin (hLK hp) hWnhds
  have hXK : closure (connectedComponentIn (W \ L.space) x) ⊆ K.space :=
    (subset_union_left.trans hclcover.subset).trans hWK
  have hYK : closure (connectedComponentIn (W \ L.space) y) ⊆ K.space :=
    (subset_union_right.trans hclcover.subset).trans hWK
  have hpI := hclmeet.symm.subset ⟨hpW, hp⟩
  have hI : IsPLBall 2 (closure (connectedComponentIn (W \ L.space) x) ∩
      closure (connectedComponentIn (W \ L.space) y)) := hclmeet.symm ▸ htrace
  rcases Topology.local_component_closure_neighborhood (isPolyhedron_space K).isClosed
    hWK hWnhds hp hdis hmeet hcover hclmeet with ⟨hsub, hnhds⟩ | ⟨hsub, hnhds⟩
  · exact ⟨_, _, hX, hY, hsub, hnhds, hYK, hpI, hI⟩
  · exact ⟨_, _, hY, hX, hsub, hnhds, hXK, ⟨hpI.2, hpI.1⟩, by rwa [inter_comm]⟩

open Classical in
theorem isCombinatorialManifoldWithBoundary_of_space_eq_closure_connectedComponentIn_sdiff
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    {a b : E} (hdis : Disjoint (connectedComponentIn (K.space \ L.space) a)
      (connectedComponentIn (K.space \ L.space) b))
    (hmeet : closure (connectedComponentIn (K.space \ L.space) a) ∩
      closure (connectedComponentIn (K.space \ L.space) b) = L.space)
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : R.space = closure (connectedComponentIn (K.space \ L.space) a)) :
    IsCombinatorialManifoldWithBoundary 3 R := by
  have hRK : R.space ⊆ K.space := by
    rw [hR]
    exact closure_minimal ((connectedComponentIn_subset _ _).trans sdiff_subset)
      (isPolyhedron_space K).isClosed
  apply isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods R
  intro p hp
  by_cases hpL : p ∈ L.space
  · obtain ⟨C, D, hC, -, hsub, hnhds, -, -, -⟩ :=
      exists_ball_pair_in_component_closure hK hL hLK hB hpL hdis hmeet
    exact ⟨C, hC, by rwa [hR], by rwa [hR]⟩
  · have hRnhds : R.space ∈ 𝓝[K.space] p := by
      rw [hR]
      exact closure_component_mem_nhdsWithin (hR.subset hp) (hRK hp) hpL
    obtain ⟨C, hC, hsub, hnhds⟩ :=
      hK.exists_isPLBall_subset_of_mem_nhdsWithin (hRK hp) hRnhds
    exact ⟨C, hC, hsub.trans inter_subset_right, nhdsWithin_mono p hRK hnhds⟩

open Classical in
theorem boundaryComplex_space_of_space_eq_closure_connectedComponentIn_sdiff
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    {a b : E} (hdis : Disjoint (connectedComponentIn (K.space \ L.space) a)
      (connectedComponentIn (K.space \ L.space) b))
    (hmeet : closure (connectedComponentIn (K.space \ L.space) a) ∩
      closure (connectedComponentIn (K.space \ L.space) b) = L.space)
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : R.space = closure (connectedComponentIn (K.space \ L.space) a)) :
    (boundaryComplex 3 R).space = L.space ∪ (R.space ∩ (boundaryComplex 3 K).space) := by
  have hman := isCombinatorialManifoldWithBoundary_of_space_eq_closure_connectedComponentIn_sdiff
    hK hL hLK hB hdis hmeet R hR
  have hRK : R.space ⊆ K.space := by
    rw [hR]
    exact closure_minimal ((connectedComponentIn_subset _ _).trans sdiff_subset)
      (isPolyhedron_space K).isClosed
  apply Subset.antisymm
  · intro p hp
    have hpR := boundaryComplex_space_subset 3 R hp
    by_cases hpL : p ∈ L.space
    · exact Or.inl hpL
    · have hRnhds : R.space ∈ 𝓝[K.space] p := by
        rw [hR]
        exact closure_component_mem_nhdsWithin (hR.subset hpR) (hRK hpR) hpL
      exact Or.inr ⟨hpR, (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin
        K R hK hman hRK hpR hRnhds).mp hp⟩
  · rintro p (hpL | hpB)
    · obtain ⟨C, D, hC, hD, hsub, hnhds, hDK, hpI, hI⟩ :=
        exists_ball_pair_in_component_closure hK hL hLK hB hpL hdis hmeet
      obtain ⟨Q, hQfin, hQC⟩ := hC.isPolyhedron.exists_simplicialComplex
      let _ : Finite Q.faces := hQfin.to_subtype
      have hQ : IsPLBall 3 Q.space := hQC.symm ▸ hC
      have hQR : Q.space ⊆ R.space := by rwa [hQC, hR]
      have hQnhds : Q.space ∈ 𝓝[R.space] p := by rwa [hQC, hR]
      have hpQ : p ∈ Q.space := hQC.symm.subset hpI.1
      have hpB : p ∈ (boundaryComplex 3 Q).space :=
        hK.inter_subset_boundaryComplex_of_isPLBall Q hQ (hQR.trans hRK) hD hDK
          (by rwa [hQC]) ⟨hpQ, hpI.2⟩
      exact (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin R Q hman
        hQ.isCombinatorialManifoldWithBoundary hQR hpQ hQnhds).mp hpB
    · exact inter_boundaryComplex_space_subset_of_subset K R hK hman hRK hpB

end DifferentialGeometry.Topology.PiecewiseLinear
