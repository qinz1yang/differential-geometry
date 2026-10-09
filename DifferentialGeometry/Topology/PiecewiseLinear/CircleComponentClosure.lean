/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarDiskPair
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ComplementComponents
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity
import DifferentialGeometry.Topology.Connected.ComponentNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
  {J W : Set E} {ρ : E × ℝ → E}

private theorem exists_disk_pair_in_circle_component_closure
    (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W) (hWK : W ⊆ K.space)
    (hW : W ∈ 𝓝ˢ[K.space] J) (hzero : ∀ x ∈ J, ρ (x, 0) = x)
    {a b p : E} (hp : p ∈ J)
    (hdis : Disjoint (connectedComponentIn (K.space \ J) a)
      (connectedComponentIn (K.space \ J) b))
    (hmeet : closure (connectedComponentIn (K.space \ J) a) ∩
      closure (connectedComponentIn (K.space \ J) b) = J) :
    ∃ C D : Set E, IsPLBall 2 C ∧ IsPLBall 2 D ∧
      C ⊆ closure (connectedComponentIn (K.space \ J) a) ∧
      C ∈ 𝓝[closure (connectedComponentIn (K.space \ J) a)] p ∧ D ⊆ K.space ∧
      p ∈ C ∩ D ∧ IsPLBall 1 (C ∩ D) := by
  obtain ⟨O, hO, hJO, hOW⟩ := mem_nhdsSetWithin.mp hW
  have hWpoint : W ∈ 𝓝[K.space] p := mem_nhdsWithin.mpr ⟨O, hO, hJO hp, hOW⟩
  obtain ⟨V, _, hVW, hVnhds, htrace, x, _, y, _, _, hcover, hC, hD, hclcover, hclmeet⟩ :=
    hρ.exists_isPLBall_neighborhood_pair_sdiff_of_bicollar hJ hzero hp hWpoint
  have hVK : V ⊆ K.space := hVW.trans hWK
  have hpV : p ∈ V := mem_of_mem_nhdsWithin (hJK hp) hVnhds
  have hCK : closure (connectedComponentIn (V \ J) x) ⊆ K.space :=
    (subset_union_left.trans hclcover.subset).trans hVK
  have hDK : closure (connectedComponentIn (V \ J) y) ⊆ K.space :=
    (subset_union_right.trans hclcover.subset).trans hVK
  have hpI := hclmeet.symm.subset ⟨hpV, hp⟩
  have hI : IsPLBall 1 (closure (connectedComponentIn (V \ J) x) ∩
      closure (connectedComponentIn (V \ J) y)) := hclmeet.symm ▸ htrace
  rcases Topology.local_component_closure_neighborhood (isPolyhedron_space K).isClosed
    hVK hVnhds hp hdis hmeet hcover hclmeet with ⟨hsub, hnhds⟩ | ⟨hsub, hnhds⟩
  · exact ⟨_, _, hC, hD, hsub, hnhds, hDK, hpI, hI⟩
  · exact ⟨_, _, hD, hC, hsub, hnhds, hCK, ⟨hpI.2, hpI.1⟩, by rwa [inter_comm]⟩

private theorem isCombinatorialManifoldWithBoundary_circle_component_closure
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W) (hWK : W ⊆ K.space)
    (hW : W ∈ 𝓝ˢ[K.space] J) (hzero : ∀ x ∈ J, ρ (x, 0) = x)
    {a b : E} (hdis : Disjoint (connectedComponentIn (K.space \ J) a)
      (connectedComponentIn (K.space \ J) b))
    (hmeet : closure (connectedComponentIn (K.space \ J) a) ∩
      closure (connectedComponentIn (K.space \ J) b) = J)
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : R.space = closure (connectedComponentIn (K.space \ J) a)) :
    IsCombinatorialManifoldWithBoundary 2 R := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  have hRK : R.space ⊆ K.space := by
    rw [hR]
    exact closure_minimal ((connectedComponentIn_subset _ _).trans sdiff_subset)
      (isPolyhedron_space K).isClosed
  apply isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods R
  intro p hp
  by_cases hpJ : p ∈ J
  · obtain ⟨C, _, hC, _, hsub, hnhds, _, _, _⟩ :=
      exists_disk_pair_in_circle_component_closure hJ hJK hρ hWK hW hzero hpJ hdis hmeet
    exact ⟨C, hC, by rwa [hR], by rwa [hR]⟩
  · have hRnhds : R.space ∈ 𝓝[K.space] p := by
      rw [hR]
      exact Topology.closure_connectedComponentIn_sdiff_mem_nhdsWithin
        hJ.isPolyhedron.isClosed (hR.subset hp) (hRK hp) hpJ
    obtain ⟨C, hC, hsub, hnhds⟩ := hK.exists_isPLBall_subset_of_mem_nhdsWithin (hRK hp) hRnhds
    exact ⟨C, hC, hsub.trans inter_subset_right, nhdsWithin_mono p hRK hnhds⟩

open Classical in
private theorem boundaryComplex_space_circle_component_closure
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W) (hWK : W ⊆ K.space)
    (hW : W ∈ 𝓝ˢ[K.space] J) (hzero : ∀ x ∈ J, ρ (x, 0) = x)
    {a b : E} (hdis : Disjoint (connectedComponentIn (K.space \ J) a)
      (connectedComponentIn (K.space \ J) b))
    (hmeet : closure (connectedComponentIn (K.space \ J) a) ∩
      closure (connectedComponentIn (K.space \ J) b) = J)
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : R.space = closure (connectedComponentIn (K.space \ J) a)) :
    (boundaryComplex 2 R).space = J ∪ (R.space ∩ (boundaryComplex 2 K).space) := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  have hman := isCombinatorialManifoldWithBoundary_circle_component_closure
    hK hJ hJK hρ hWK hW hzero hdis hmeet R hR
  have hRK : R.space ⊆ K.space := by
    rw [hR]
    exact closure_minimal ((connectedComponentIn_subset _ _).trans sdiff_subset)
      (isPolyhedron_space K).isClosed
  apply Subset.antisymm
  · intro p hp
    have hpR := boundaryComplex_space_subset 2 R hp
    by_cases hpJ : p ∈ J
    · exact Or.inl hpJ
    · have hRnhds : R.space ∈ 𝓝[K.space] p := by
        rw [hR]
        exact Topology.closure_connectedComponentIn_sdiff_mem_nhdsWithin
          hJ.isPolyhedron.isClosed (hR.subset hpR) (hRK hpR) hpJ
      exact Or.inr ⟨hpR, (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin
        K R hK hman hRK hpR hRnhds).mp hp⟩
  · rintro p (hpJ | hpB)
    · obtain ⟨C, D, hC, hD, hsub, hnhds, hDK, hpI, hI⟩ :=
        exists_disk_pair_in_circle_component_closure hJ hJK hρ hWK hW hzero hpJ hdis hmeet
      obtain ⟨Q, hQfin, hQC⟩ := hC.isPolyhedron.exists_simplicialComplex
      let _ : Finite Q.faces := hQfin.to_subtype
      have hQ : IsPLBall 2 Q.space := hQC.symm ▸ hC
      have hQR : Q.space ⊆ R.space := by rwa [hQC, hR]
      have hQnhds : Q.space ∈ 𝓝[R.space] p := by rwa [hQC, hR]
      have hpQ : p ∈ Q.space := hQC.symm.subset hpI.1
      have hpB : p ∈ (boundaryComplex 2 Q).space :=
        hK.inter_subset_boundaryComplex_of_isPLBall Q hQ (hQR.trans hRK) hD hDK
          (by rwa [hQC]) ⟨hpQ, hpI.2⟩
      exact (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin R Q hman
        hQ.isCombinatorialManifoldWithBoundary hQR hpQ hQnhds).mp hpB
    · exact inter_boundaryComplex_space_subset_of_subset K R hK hman hRK hpB

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_manifold_pair_of_separating_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    (hconn : IsPreconnected K.space) {J : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hBd : Disjoint J (boundaryComplex 2 K).space) (hsep : ¬ IsPreconnected (K.space \ J)) :
    ∃ (A B : Geometry.SimplicialComplex ℝ E) (hAfin : A.faces.Finite) (hBfin : B.faces.Finite),
      letI := hAfin.to_subtype
      letI := hBfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 A ∧ IsCombinatorialManifoldWithBoundary 2 B ∧
      IsOrientable 2 A ∧ IsOrientable 2 B ∧ IsConnected A.space ∧ IsConnected B.space ∧
      A.space ∪ B.space = K.space ∧ A.space ∩ B.space = J ∧
      (boundaryComplex 2 A).space = J ∪ (A.space ∩ (boundaryComplex 2 K).space) ∧
      (boundaryComplex 2 B).space = J ∪ (B.space ∩ (boundaryComplex 2 K).space) ∧
      ∃ a ∈ K.space \ J, ∃ b ∈ K.space \ J,
        A.space = closure (connectedComponentIn (K.space \ J) a) ∧
        B.space = closure (connectedComponentIn (K.space \ J) b) := by
  obtain ⟨W, ρ, _, hWK, _, hW, hρ, hzero⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK hBd (U := univ) Filter.univ_mem
  have hWK' := hWK.trans sdiff_subset
  obtain ⟨a, ha, b, hb, hdis, _, hclcover, hclmeet⟩ :=
    hK.exists_connectedComponentIn_pair_sdiff_of_separating_circle K hor hconn hJ hJK hBd hsep
  obtain ⟨L, hLfin, hLspace⟩ := hJ.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hLK : L.space ⊆ K.space := hLspace.subset.trans hJK
  have hpoly (p : E) : IsPolyhedron (closure (connectedComponentIn (K.space \ J) p)) := by
    rw [← hLspace]
    exact isPolyhedron_closure_connectedComponentIn_sdiff_of_subset K L hLK p
  obtain ⟨A, hAfin, hAspace⟩ := (hpoly a).exists_simplicialComplex
  obtain ⟨B, hBfin, hBspace⟩ := (hpoly b).exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hA := isCombinatorialManifoldWithBoundary_circle_component_closure
    hK hJ hJK hρ hWK' hW hzero hdis hclmeet A hAspace
  have hmeet' : closure (connectedComponentIn (K.space \ J) b) ∩
      closure (connectedComponentIn (K.space \ J) a) = J := by rwa [inter_comm]
  have hB := isCombinatorialManifoldWithBoundary_circle_component_closure
    hK hJ hJK hρ hWK' hW hzero hdis.symm hmeet' B hBspace
  have hcover : A.space ∪ B.space = K.space := by rwa [hAspace, hBspace]
  have hAK : A.space ⊆ K.space := subset_union_left.trans hcover.subset
  have hBK : B.space ⊆ K.space := subset_union_right.trans hcover.subset
  refine ⟨A, B, hAfin, hBfin, hA, hB,
    hor.of_space_subset K A hAK hK hA, hor.of_space_subset K B hBK hK hB, ?_, ?_, hcover, ?_,
    boundaryComplex_space_circle_component_closure hK hJ hJK hρ hWK' hW hzero
      hdis hclmeet A hAspace,
    boundaryComplex_space_circle_component_closure hK hJ hJK hρ hWK' hW hzero
      hdis.symm hmeet' B hBspace, a, ha, b, hb, hAspace, hBspace⟩
  · rw [hAspace]
    exact (isConnected_connectedComponentIn_iff.mpr ha).closure
  · rw [hBspace]
    exact (isConnected_connectedComponentIn_iff.mpr hb).closure
  · rwa [hAspace, hBspace]

open Classical in
theorem IsCombinatorialManifold.exists_manifold_pair_of_separating_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    (hconn : IsPreconnected K.space) {J : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hsep : ¬ IsPreconnected (K.space \ J)) :
    ∃ (A B : Geometry.SimplicialComplex ℝ E) (hAfin : A.faces.Finite) (hBfin : B.faces.Finite),
      letI := hAfin.to_subtype
      letI := hBfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 A ∧ IsCombinatorialManifoldWithBoundary 2 B ∧
      IsOrientable 2 A ∧ IsOrientable 2 B ∧ IsConnected A.space ∧ IsConnected B.space ∧
      A.space ∪ B.space = K.space ∧ A.space ∩ B.space = J ∧
      (boundaryComplex 2 A).space = J ∧ (boundaryComplex 2 B).space = J ∧
      ∃ a ∈ K.space \ J, ∃ b ∈ K.space \ J,
        A.space = closure (connectedComponentIn (K.space \ J) a) ∧
        B.space = closure (connectedComponentIn (K.space \ J) b) := by
  have hBd : (boundaryComplex 2 K).space = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨s, hs, _⟩ := (boundaryComplex 2 K).mem_space_iff.mp hx
    rw [hK.boundaryComplex_faces_eq_empty K] at hs
    exact hs.elim
  obtain ⟨A, B, hAfin, hBfin, hA, hB, hAo, hBo, hAc, hBc, hcover, hmeet, hAbd, hBbd, hcomponents⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_manifold_pair_of_separating_circle K hor hconn
      hJ hJK (by rw [hBd]; exact disjoint_empty J) hsep
  rw [hBd, inter_empty, union_empty] at hAbd hBbd
  exact ⟨A, B, hAfin, hBfin, hA, hB, hAo, hBo, hAc, hBc, hcover, hmeet, hAbd, hBbd, hcomponents⟩

end DifferentialGeometry.Topology.PiecewiseLinear
