/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopCutPL

set_option autoImplicit false

open Set Topology DifferentialGeometry.Topology DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem exists_connectedComponentComplex_space_eq_of_closed_partition_LTP3
    (K : Geometry.SimplicialComplex ℝ E) {S T : Set E}
    (hS : IsClosed S) (hT : IsClosed T) (hconn : IsConnected S)
    (hdis : Disjoint S T) (hcover : K.space = S ∪ T) :
    ∃ c : ConnectedComponents K.space, (connectedComponentComplex K c).space = S := by
  obtain ⟨x, hx⟩ := hconn.nonempty
  have hxK : x ∈ K.space := hcover.symm.subset (Or.inl hx)
  refine ⟨ConnectedComponents.mk (⟨x, hxK⟩ : K.space), ?_⟩
  rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space]
  change connectedComponentIn K.space x = S
  rw [hcover]
  have hsdiff : S \ T = S := sdiff_eq_left.mpr hdis
  have h := connectedComponentIn_sdiff_inter_eq_sdiff hS hT
    (hsdiff.symm ▸ hconn.isPreconnected) ⟨hx, disjoint_left.mp hdis hx⟩
  simpa only [hdis.inter_eq, sdiff_empty, hsdiff] using h

/-- A connected component of a finite polyhedron is closed and has closed complement in it. -/
theorem isClosed_component_and_rest_LTP3 (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (x : E) :
    IsClosed (connectedComponentIn L.space x) ∧
      IsClosed (L.space \ connectedComponentIn L.space x) := by
  have hLc : IsClosed L.space := (isPolyhedron_space L).isClosed
  constructor
  · by_cases hx : x ∈ L.space
    · have hc : IsPreconnected (closure (connectedComponentIn L.space x)) :=
        isPreconnected_connectedComponentIn.closure
      have := hc.subset_connectedComponentIn (subset_closure (mem_connectedComponentIn hx))
        (closure_minimal (connectedComponentIn_subset _ _) hLc)
      exact closure_subset_iff_isClosed.mp (by
        rw [← connectedComponentIn_eq (this (subset_closure (mem_connectedComponentIn hx)))] at this
        exact this |>.trans (by rw [connectedComponentIn_eq (mem_connectedComponentIn hx)]))
    · rw [connectedComponentIn_eq_empty hx]; exact isClosed_empty
  · letI := locallyConnectedSpace_space L
    have hopen := isOpen_preimage_connectedComponentIn_sdiff (N := L.space) (S := ∅)
      isClosed_empty x
    simp only [sdiff_empty] at hopen
    have hcl : IsClosed (((↑) : L.space → E) '' (((↑) : L.space → E) ⁻¹'
        connectedComponentIn L.space x)ᶜ) :=
      hLc.isClosedEmbedding_subtypeVal.isClosedMap _ hopen.isClosed_compl
    convert hcl using 1
    ext y
    simp only [mem_diff, mem_image, mem_compl_iff, mem_preimage, Subtype.exists, exists_and_right,
      exists_eq_right]
    constructor
    · rintro ⟨hy, hyc⟩; exact ⟨hy, hyc⟩
    · rintro ⟨hy, hyc⟩; exact ⟨hy, hyc⟩

open Classical in
/-- **P3, boundary components.**  Under the one-sidedness hypotheses, every connected component
`T` of `L` meeting `R` lies in `R` and is a connected component of `∂R`
(a torus component of `L` is therefore a boundary torus of `R`). -/
theorem exists_boundary_component_of_oneSided_LTP3
    {K L R : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    (hRK : R.space ⊆ K.space)
    (hopen : ∀ x ∈ R.space \ L.space, R.space ∈ 𝓝[K.space] x)
    (hdense : ∀ p ∈ L.space ∩ R.space, p ∈ closure (R.space \ L.space))
    (hone : ∀ p ∈ L.space ∩ R.space, p ∈ closure (K.space \ R.space))
    {x : E} (hxL : x ∈ L.space) (hxR : x ∈ R.space) :
    connectedComponentIn L.space x ⊆ R.space ∧
    ∃ c : ConnectedComponents (boundaryComplex 3 R).space,
      (connectedComponentComplex (boundaryComplex 3 R) c).space = connectedComponentIn L.space x := by
  have hRc : IsClosed R.space := (isPolyhedron_space R).isClosed
  have hLc : IsClosed L.space := (isPolyhedron_space L).isClosed
  obtain ⟨-, hbd⟩ := isCombinatorialManifoldWithBoundary_of_oneSided_LTP3 hK hL hLK hB hRK
    hopen hdense hone
  set T := connectedComponentIn L.space x with hTdef
  obtain ⟨hTc, hrestc⟩ := isClosed_component_and_rest_LTP3 L x
  have hTL : T ⊆ L.space := connectedComponentIn_subset _ _
  have hTconn : IsConnected T := isConnected_connectedComponentIn_iff.mpr hxL
  -- `L ∩ R` is open in `L`
  have hLRopen : ∀ p ∈ L.space ∩ R.space, L.space ∩ R.space ∈ 𝓝[L.space] p := by
    intro p hp
    obtain ⟨C, D, -, -, hsub, -, -, -, -, N, hN, hNC⟩ :=
      exists_side_ball_pair_LTP3 hK hL hLK hB hRK hopen hdense hone hp
    have hN' : N ∈ 𝓝[L.space] p := nhdsWithin_mono p hLK hN
    refine Filter.mem_of_superset (Filter.inter_mem hN' self_mem_nhdsWithin) ?_
    rintro z ⟨hzN, hzL⟩
    exact ⟨hzL, hsub (hNC ⟨hzL, hzN⟩)⟩
  have hTR : T ⊆ R.space := by
    have h := subset_or_disjoint_LTP3 (K := L.space) (L := ∅) (R := L.space ∩ R.space)
      (hLc.inter hRc) (fun y hy => hLRopen y hy.1) hTconn.isPreconnected hTL
      (disjoint_empty _)
    rcases h with h | h
    · exact fun y hy => (h hy).2
    · exact (disjoint_left.mp h (mem_connectedComponentIn hxL) ⟨hxL, hxR⟩).elim
  refine ⟨hTR, ?_⟩
  refine exists_connectedComponentComplex_space_eq_of_closed_partition_LTP3 (boundaryComplex 3 R)
    hTc (T := ((L.space \ T) ∩ R.space) ∪ (R.space ∩ (boundaryComplex 3 K).space))
    ((hrestc.inter hRc).union (hRc.inter (isPolyhedron_space (boundaryComplex 3 K)).isClosed))
    hTconn ?_ ?_
  · refine disjoint_union_right.mpr ⟨?_, ?_⟩
    · exact disjoint_left.mpr fun y hy hy' => hy'.1.2 hy
    · exact disjoint_left.mpr fun y hy hy' => disjoint_left.mp hB (hTL hy) hy'.2
  · rw [hbd]
    ext y
    constructor
    · rintro (⟨hyL, hyR⟩ | h)
      · by_cases hyT : y ∈ T
        · exact Or.inl hyT
        · exact Or.inr (Or.inl ⟨⟨hyL, hyT⟩, hyR⟩)
      · exact Or.inr (Or.inr h)
    · rintro (hyT | ⟨⟨hyL, -⟩, hyR⟩ | h)
      · exact Or.inl ⟨hTL hyT, hTR hyT⟩
      · exact Or.inl ⟨hyL, hyR⟩
      · exact Or.inr h

end GC.LongTime.CuspP1
