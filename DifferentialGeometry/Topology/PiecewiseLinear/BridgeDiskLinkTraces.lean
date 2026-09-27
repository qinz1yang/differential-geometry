/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskLinks

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsBridgeDisk.geometricLink_traces
    {C A B : Set E} {a b x : E} (h : IsBridgeDisk C A B a b)
    (hdim : Module.finrank ℝ E = 3) (hC : IsPLBall 3 C)
    (T K L M R : Geometry.SimplicialComplex ℝ E) [Finite T.faces]
    (hKT : K.faces ⊆ T.faces) (hLT : L.faces ⊆ T.faces)
    (hMT : M.faces ⊆ T.faces) (hRT : R.faces ⊆ T.faces)
    (hKC : K.space = C) (hLB : L.space = B) (hMA : M.space = A)
    (hRβ : R.space = B ∩ frontier C) (hCT : C ⊆ interior T.space)
    (hxT : {x} ∈ T.faces) (hxβ : x ∈ B ∩ frontier C) :
    IsPLSphere 2 (SimplicialComplex.geometricLink T {x}).space ∧
    IsPLBall 2 (SimplicialComplex.geometricLink K {x}).space ∧
    IsPLBall 1 (SimplicialComplex.geometricLink L {x}).space ∧
    (SimplicialComplex.geometricLink L {x}).space ⊆
      (SimplicialComplex.geometricLink K {x}).space ∧
    (SimplicialComplex.geometricLink L {x}).space ∩
      (boundaryComplex 2 (SimplicialComplex.geometricLink K {x})).space =
        (SimplicialComplex.geometricLink R {x}).space ∧
    (boundaryComplex 1 (SimplicialComplex.geometricLink L {x})).space =
      (SimplicialComplex.geometricLink M {x}).space ∪
        (SimplicialComplex.geometricLink R {x}).space ∧
    Disjoint (SimplicialComplex.geometricLink M {x}).space
      (SimplicialComplex.geometricLink R {x}).space ∧
    (x ∈ ({a, b} : Set E) →
      IsPLBall 0 (SimplicialComplex.geometricLink M {x}).space ∧
      IsPLBall 0 (SimplicialComplex.geometricLink R {x}).space) ∧
    (x ∉ ({a, b} : Set E) →
      (SimplicialComplex.geometricLink M {x}).space = ∅ ∧
      (SimplicialComplex.geometricLink R {x}).space =
        (boundaryComplex 1 (SimplicialComplex.geometricLink L {x})).space) := by
  let _ : Finite K.faces := ((Set.toFinite T.faces).subset hKT).to_subtype
  let _ : Finite L.faces := ((Set.toFinite T.faces).subset hLT).to_subtype
  let _ : Finite M.faces := ((Set.toFinite T.faces).subset hMT).to_subtype
  let _ : Finite R.faces := ((Set.toFinite T.faces).subset hRT).to_subtype
  have hcopy := h
  obtain ⟨q, hq, hBC, _, _, _, _⟩ := hcopy
  have hL : IsPLBall 2 L.space := hLB.symm ▸ (show IsPLBall 2 B from ⟨q, hq⟩)
  have hK : IsPLBall 3 K.space := hKC.symm ▸ hC
  have hbdK : (boundaryComplex 3 K).space = frontier C := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K
      hK.isCombinatorialManifoldWithBoundary, hKC]
  have hbdL := h.boundary_eq L hLB
  have hvertex (S : Geometry.SimplicialComplex ℝ E) (hST : S.faces ⊆ T.faces)
      (hxS : x ∈ S.space) : {x} ∈ S.faces := by
    by_contra hnot
    exact notMem_space_of_notMem_faces hST hxT hnot (mem_openSimplex_singleton x) hxS
  have hxK : {x} ∈ K.faces := hvertex K hKT (hKC.symm ▸ hBC hxβ.1)
  have hxL : {x} ∈ L.faces := hvertex L hLT (hLB.symm ▸ hxβ.1)
  have hxR : {x} ∈ R.faces := hvertex R hRT (hRβ.symm ▸ hxβ)
  have hKlink : IsPLBall 2 (SimplicialComplex.geometricLink K {x}).space := by
    apply (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision K K
      hK.isCombinatorialManifoldWithBoundary (IsSubdivision.refl K) hxK).mpr
    exact hbdK.symm ▸ hxβ.2
  have hLlink : IsPLBall 1 (SimplicialComplex.geometricLink L {x}).space := by
    apply (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision L L
      hL.isCombinatorialManifoldWithBoundary (IsSubdivision.refl L) hxL).mpr
    exact hbdL.symm.subset (Or.inr hxβ)
  have hLK : L.faces ⊆ K.faces := by
    intro s hs
    by_contra hnot
    exact notMem_space_of_notMem_faces hKT (hLT hs) hnot
      (centroid_mem_openSimplex (L.nonempty_of_mem_faces hs))
      (hKC.symm.subset (hBC (hLB.subset
        (L.convexHull_subset_space hs (s.centroid_mem_convexHull
          (L.nonempty_of_mem_faces hs))))))
  have hlinksub : (SimplicialComplex.geometricLink L {x}).space ⊆
      (SimplicialComplex.geometricLink K {x}).space :=
    space_mono_of_faces_subset (fun _ hs => ⟨hs.1, hs.2.1, hLK hs.2.2⟩)
  have htrace : (SimplicialComplex.geometricLink L {x}).space ∩
      (boundaryComplex 2 (SimplicialComplex.geometricLink K {x})).space =
        (SimplicialComplex.geometricLink R {x}).space := by
    rw [← geometricLink_boundaryComplex (n := 2)]
    exact (geometricLink_space_inter_of_subcomplex_space_eq T L (boundaryComplex 3 K) R
      hLT ((boundaryComplex_faces_subset 3 K).trans hKT) hRT
      (by rw [hRβ, hLB, hbdK]) x).symm
  have hlinkbd : (boundaryComplex 1 (SimplicialComplex.geometricLink L {x})).space =
      (SimplicialComplex.geometricLink M {x}).space ∪
        (SimplicialComplex.geometricLink R {x}).space := by
    rw [← geometricLink_boundaryComplex (n := 1)]
    exact geometricLink_space_union_of_subcomplex_space_eq T M R (boundaryComplex 2 L)
      hMT hRT ((boundaryComplex_faces_subset 2 L).trans hLT)
      (by rw [hbdL, hMA, hRβ]) x
  have hAB : A ⊆ B := (subset_union_left.trans hbdL.symm.subset).trans
    ((boundaryComplex_space_subset 2 L).trans hLB.subset)
  have hAβ : A ∩ (B ∩ frontier C) = {a, b} := by
    calc
      A ∩ (B ∩ frontier C) = A ∩ frontier C := by
        ext y
        exact ⟨fun hy => ⟨hy.1, hy.2.2⟩, fun hy => ⟨hy.1, hAB hy.1, hy.2⟩⟩
      _ = {a, b} := h.inter_frontier
  have hdis : Disjoint (SimplicialComplex.geometricLink M {x}).space
      (SimplicialComplex.geometricLink R {x}).space := by
    let I := restrict M R.space
    have hI : I.space = M.space ∩ R.space :=
      restrict_space_eq_inter_of_faces_subset T M R hMT hRT
    have hIfin : I.space.Finite := by
      rw [hI, hMA, hRβ, hAβ]
      exact (finite_singleton b).insert a
    rw [disjoint_iff_inter_eq_empty,
      ← geometricLink_space_inter_of_subcomplex_space_eq T M R I hMT hRT
        ((restrict_faces_subset M R.space).trans hMT) hI x]
    exact geometricLink_space_eq_empty_of_finite_space I hIfin x
  refine ⟨isPLSphere_geometricLink_of_mem_nhds hdim T hxT
    (mem_interior_iff_mem_nhds.mp (hCT (hBC hxβ.1))), hKlink, hLlink,
    hlinksub, htrace, hlinkbd, hdis, ?_, ?_⟩
  · intro hxends
    obtain ⟨γ, hγ, hγ0, hγ1⟩ := h.exists_parametrization
    obtain ⟨δ, hδ, hδ0, hδ1⟩ := h.exists_frontier_parametrization
    have hM : IsPLBall 1 M.space := hMA.symm ▸
      (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ
    have hR : IsPLBall 1 R.space := hRβ.symm ▸ h.isPLBall_inter_frontier
    have hMbd : (boundaryComplex 1 M).space = {a, b} := by
      rw [boundaryComplex_space_of_parametrized_Icc M zero_lt_one (hMA.symm ▸ hγ), hγ0, hγ1]
    have hRbd : (boundaryComplex 1 R).space = {a, b} := by
      rw [boundaryComplex_space_of_parametrized_Icc R zero_lt_one (hRβ.symm ▸ hδ), hδ0, hδ1]
    have hxM : {x} ∈ M.faces := hvertex M hMT (boundaryComplex_space_subset 1 M
      (hMbd.symm ▸ hxends))
    exact ⟨(isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision M M
      hM.isCombinatorialManifoldWithBoundary (IsSubdivision.refl M) hxM).mpr
        (hMbd.symm ▸ hxends),
      (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision R R
        hR.isCombinatorialManifoldWithBoundary (IsSubdivision.refl R) hxR).mpr
        (hRbd.symm ▸ hxends)⟩
  · intro hxends
    have hxM : x ∉ M.space := by
      intro hx
      exact hxends (h.inter_frontier.subset ⟨hMA.subset hx, hxβ.2⟩)
    have hempty := geometricLink_space_eq_empty_of_notMem_space M hxM
    exact ⟨hempty, by simpa only [hempty, empty_union] using hlinkbd.symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear
