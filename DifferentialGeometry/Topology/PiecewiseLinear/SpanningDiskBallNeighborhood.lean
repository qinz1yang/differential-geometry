/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCutting
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingSurface

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_neighborhood_of_proper_disk
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hdim : Module.finrank ℝ E = 3)
    {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (hproper : D ∩ (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2)
    (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (B : Geometry.SimplicialComplex ℝ E) (hBfin : B.faces.Finite),
      letI := hBfin.to_subtype
      IsPLBall 3 B.space ∧ B.space ⊆ K.space ∧ B.space ⊆ U ∧ D ⊆ B.space ∧
      (∀ x ∈ D, B.space ∈ 𝓝[K.space] x) ∧
      D ∩ frontier B.space = r '' stdSimplexBoundary 2 ∧
      (boundaryComplex 3 K).space ∈ 𝓝ˢ[frontier B.space] (r '' stdSimplexBoundary 2) := by
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  obtain ⟨K', M, hK', hK'fin, hMK', hM, hMU, hMnhds⟩ :=
    hK.exists_isSubdivision_neighborhood hD.isPolyhedron.isCompact hDK hU hDU
  let _ : Finite M.faces := (hK'fin.subset hMK').to_subtype
  have hMK : M.space ⊆ K.space := (space_mono_of_faces_subset hMK').trans hK'.space_eq.subset
  have hDM : D ⊆ M.space := fun x hx => mem_of_mem_nhdsWithin (hDK hx) (hMnhds x hx)
  obtain ⟨R, A, hR, hRfin, hAR, hAfin, hAD, hB, hDB, hBM, hBnhds⟩ :=
    hM.exists_isPLBall_derivedNeighborhood_disk hD hDM
  let _ : Finite R.faces := hRfin.to_subtype
  let B := PiecewiseLinear.derivedNeighborhood R A
  have hBfin : B.faces.Finite := derivedNeighborhood_faces_finite R A
  let _ : Finite B.faces := hBfin.to_subtype
  have hBK : B.space ⊆ K.space := hBM.trans hMK
  have hnhds (x : E) (hx : x ∈ D) : B.space ∈ 𝓝[K.space] x := by
    have hle : 𝓝[K.space] x ≤ 𝓝[M.space] x :=
      le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr (hMnhds x hx))
    exact hle (hBnhds x hx)
  have hfrontK := frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK
  have htrace : D ∩ frontier B.space = r '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro x ⟨hxD, hxF⟩
      apply hproper.subset
      refine ⟨hxD, ?_⟩
      by_contra hxB
      have hxint : x ∈ interior K.space := by
        rw [← self_sdiff_frontier K.space, hfrontK]
        exact ⟨hDK hxD, hxB⟩
      have hxN := hnhds x hxD
      rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hxint)] at hxN
      exact hxF.2 (mem_interior_iff_mem_nhds.mpr hxN)
    · intro x hx
      obtain ⟨hxD, hxK⟩ := hproper.symm.subset hx
      refine ⟨hxD, subset_closure (hDB hxD), ?_⟩
      intro hxint
      exact (hfrontK.symm.subset hxK).2 (interior_mono hBK hxint)
  have hpoint (x : E) (hx : x ∈ r '' stdSimplexBoundary 2) :
      (boundaryComplex 3 K).space ∈ 𝓝[frontier B.space] x := by
    obtain ⟨O, hO, hxO, hOB⟩ := mem_nhdsWithin.mp (hnhds x (hproper.symm.subset hx).1)
    refine mem_nhdsWithin.mpr ⟨O, hO, hxO, ?_⟩
    rintro y ⟨hyO, hyF⟩
    have hyK : y ∈ K.space := hBK (hB.isPolyhedron.isClosed.frontier_subset hyF)
    by_contra hybd
    have hyint : y ∈ interior K.space := by
      rw [← self_sdiff_frontier K.space, hfrontK]
      exact ⟨hyK, hybd⟩
    have hyN : B.space ∈ 𝓝 y := Filter.mem_of_superset
      (Filter.inter_mem (hO.mem_nhds hyO) (mem_interior_iff_mem_nhds.mp hyint)) hOB
    exact hyF.2 (mem_interior_iff_mem_nhds.mpr hyN)
  have hboundary : (boundaryComplex 3 K).space ∈
      𝓝ˢ[frontier B.space] (r '' stdSimplexBoundary 2) := by
    choose O hO hxO hOB using fun x : r '' stdSimplexBoundary 2 =>
      mem_nhdsWithin.mp (hpoint x x.property)
    refine mem_nhdsSetWithin.mpr ⟨⋃ x : r '' stdSimplexBoundary 2, O x,
      isOpen_iUnion hO, ?_, ?_⟩
    · exact fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩
    · rintro x ⟨hxO', hxF⟩
      obtain ⟨y, hxy⟩ := mem_iUnion.mp hxO'
      exact hOB y ⟨hxy, hxF⟩
  exact ⟨B, hBfin, hB, hBK, hBM.trans hMU, hDB, hnhds, htrace, hboundary⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_neighborhood_of_spanning_disk
    {K S : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite S.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hS : IsCombinatorialManifold 2 S)
    (hdim : Module.finrank ℝ E = 3)
    (hSK : S.space ⊆ K.space \ (boundaryComplex 3 K).space)
    (hKc : IsPreconnected K.space) (hSc : IsConnected S.space)
    {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2)
    (hDK : D ⊆ interior K.space) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (B : Geometry.SimplicialComplex ℝ E) (hBfin : B.faces.Finite),
      letI := hBfin.to_subtype
      IsPLBall 3 B.space ∧ B.space ⊆ interior K.space ∧ B.space ⊆ U ∧ D ⊆ B.space ∧
      D \ S.space ⊆ interior B.space ∧
      D ∩ frontier B.space = r '' stdSimplexBoundary 2 ∧
      S.space ∩ B.space ⊆ frontier B.space ∧
      S.space ∈ 𝓝ˢ[frontier B.space] (r '' stdSimplexBoundary 2) := by
  obtain ⟨A₀, A₁, hA₀fin, hA₁fin, hA₀, hA₁, _, _, _, _, hcover, hpair,
    hbd₀, hbd₁, _, _⟩ := hK.exists_manifold_pair_of_surface_interior hS hdim hSK hKc hSc
  let _ : Finite A₀.faces := hA₀fin.to_subtype
  let _ : Finite A₁.faces := hA₁fin.to_subtype
  let J := r '' stdSimplexBoundary 2
  have hcoverD : D \ J ⊆ A₀.space ∪ A₁.space :=
    sdiff_subset.trans (hDK.trans (interior_subset.trans hcover.symm.subset))
  have hside : D \ J ⊆ A₀.space ∨ D \ J ⊆ A₁.space := by
    by_cases hleft : D \ J ⊆ A₀.space
    · exact Or.inl hleft
    right
    intro y hy
    by_contra hyA₁
    obtain ⟨x, hx, hxA₀⟩ := not_subset.mp hleft
    obtain ⟨z, hz, hz₀, hz₁⟩ :=
      isPreconnected_closed_iff.mp hr.isConnected_sdiff_image_stdSimplexBoundary.isPreconnected
        A₀.space A₁.space (isPolyhedron_space A₀).isClosed (isPolyhedron_space A₁).isClosed
        hcoverD ⟨y, hy, (hcoverD hy).resolve_right hyA₁⟩
        ⟨x, hx, (hcoverD hx).resolve_left hxA₀⟩
    exact hz.2 (hmeet.subset ⟨hz.1, hpair.subset ⟨hz₀, hz₁⟩⟩)
  have hfrontK := frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK
  have hsideBall (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
      (hR : IsCombinatorialManifoldWithBoundary 3 R)
      (hRbd : (boundaryComplex 3 R).space =
        S.space ∪ (R.space ∩ (boundaryComplex 3 K).space))
      (hDR : D ⊆ R.space) :
      ∃ (B : Geometry.SimplicialComplex ℝ E) (hBfin : B.faces.Finite),
        letI := hBfin.to_subtype
        IsPLBall 3 B.space ∧ B.space ⊆ interior K.space ∧ B.space ⊆ U ∧ D ⊆ B.space ∧
        D \ S.space ⊆ interior B.space ∧ D ∩ frontier B.space = J ∧
        S.space ∩ B.space ⊆ frontier B.space ∧ S.space ∈ 𝓝ˢ[frontier B.space] J := by
    have hproper : D ∩ (boundaryComplex 3 R).space = J := by
      apply Subset.antisymm
      · rintro x ⟨hxD, hxR⟩
        rcases hRbd.subset hxR with hxS | hxK
        · exact hmeet.subset ⟨hxD, hxS⟩
        · exact ((hfrontK.symm.subset hxK.2).2 (hDK hxD)).elim
      · exact fun x hx => ⟨(hmeet.symm.subset hx).1,
          hRbd.symm.subset (Or.inl (hmeet.symm.subset hx).2)⟩
    obtain ⟨B, hBfin, hB, hBR, hBU, hDB, _, htrace, hboundary⟩ :=
      hR.exists_isPLBall_neighborhood_of_proper_disk hdim hr hDR hproper
        (hU.inter isOpen_interior) (fun x hx => ⟨hDU hx, hDK hx⟩)
    let _ : Finite B.faces := hBfin.to_subtype
    have hBS (x : E) (hxB : x ∈ B.space) (hxR : x ∈ (boundaryComplex 3 R).space) :
        x ∈ S.space := by
      rcases hRbd.subset hxR with hxS | hxK
      · exact hxS
      · exact ((hfrontK.symm.subset hxK.2).2 (hBU hxB).2).elim
    have htraceS : S.space ∩ B.space ⊆ frontier B.space := by
      rintro x ⟨hxS, hxB⟩
      refine ⟨subset_closure hxB, ?_⟩
      intro hxint
      have hxR : x ∈ frontier R.space := by
        rw [frontier_space_eq_boundaryComplex_space_of_finrank hdim R hR, hRbd]
        exact Or.inl hxS
      exact hxR.2 (interior_mono hBR hxint)
    have hSnhds : S.space ∈ 𝓝ˢ[frontier B.space] J := by
      obtain ⟨O, hO, hJO, hOR⟩ := mem_nhdsSetWithin.mp hboundary
      exact mem_nhdsSetWithin.mpr ⟨O, hO, hJO, fun x hx =>
        hBS x (hB.isPolyhedron.isClosed.frontier_subset hx.2) (hOR hx)⟩
    refine ⟨B, hBfin, hB, fun _ hx => (hBU hx).2, fun _ hx => (hBU hx).1,
      hDB, ?_, htrace, htraceS, hSnhds⟩
    rintro x ⟨hxD, hxS⟩
    rw [← self_sdiff_frontier B.space]
    exact ⟨hDB hxD, fun hxF => hxS (hmeet.symm.subset (htrace.subset ⟨hxD, hxF⟩)).2⟩
  rcases hside with hleft | hright
  · apply hsideBall A₀ hA₀ hbd₀
    rw [← hr.closure_sdiff_image_stdSimplexBoundary]
    exact closure_minimal hleft (isPolyhedron_space A₀).isClosed
  · apply hsideBall A₁ hA₁ hbd₁
    rw [← hr.closure_sdiff_image_stdSimplexBoundary]
    exact closure_minimal hright (isPolyhedron_space A₁).isClosed

end DifferentialGeometry.Topology.PiecewiseLinear
