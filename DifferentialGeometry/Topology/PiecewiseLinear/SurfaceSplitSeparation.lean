/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Connected.Separation
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitLocalTrace

/-! Separation preserved by splitting a polyhedral surface along a disk. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_surface_split_preserving_separation
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) {H Q : Set K.space} {C Δ D₁ D₂ : Set E}
    (hHclosed : IsClosed H) (hQclosed : IsClosed Q)
    (hCclosed : IsClosed (((↑) : K.space → E) ⁻¹' C))
    (hsep : Separates (((↑) : K.space → E) ⁻¹' C) H Q) (hΔ : IsPLBall 2 Δ)
    {r₁ r₂ : (Fin 3 → ℝ) → E}
    (hr₁ : IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁)
    (hr₂ : IsPLHomeomorphOn r₂ (stdSimplex ℝ (Fin 3)) D₂)
    (hΔintD₁ : Δ ⊆ r₁ '' openSimplex (stdVertices 1))
    (hΔintD₂ : Δ ⊆ r₂ '' openSimplex (stdVertices 1))
    (hΔD₁ : Δ ⊆ D₁) (hΔD₂ : Δ ⊆ D₂) (hD₁D₂ : D₁ ∩ D₂ = Δ)
    (hD₁K : D₁ ⊆ K.space) (hD₂K : D₂ ⊆ K.space)
    (hD₁C : D₁ ⊆ C) (hD₂C : D₂ ⊆ C)
    (hlocal : D₁ ∪ D₂ ∈ 𝓝ˢ[C] Δ) :
    ∃ (N : Set E) (B : Geometry.SimplicialComplex ℝ E)
      (g : (Fin 3 → ℝ) → E) (A₁ Δ₁ C' : Set E),
      B.faces.Finite ∧ IsPLBall 3 N ∧ IsPLBall 3 B.space ∧
      Δ ⊆ N ∧ N ⊆ K.space ∧
      N ⊆ (((↑) : K.space → E) '' H ∪ ((↑) : K.space → E) '' Q)ᶜ ∧
      (∀ x ∈ Δ, N ∈ 𝓝[K.space] x) ∧ B.space ⊆ N ∧
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) (D₂ ∩ N) ∧
      D₂ ∩ N ⊆ (boundaryComplex 3 B).space ∧
      A₁ = N ∩ closure (D₁ \ Δ) ∧ A₁ ⊆ B.space ∧
      IsPLBall 2 Δ₁ ∧ Δ₁ ⊆ (boundaryComplex 3 B).space ∧
      (boundaryComplex 3 B).space = (D₂ ∩ N) ∪ Δ₁ ∧
      (D₂ ∩ N) ∩ Δ₁ = g '' stdSimplexBoundary 2 ∧
      C' = (C \ (A₁ \ ((D₂ ∩ N) ∪ Δ₁))) ∪ Δ₁ ∧
      C ∩ B.space = (D₂ ∩ N) ∪ A₁ ∧
      C' ∩ B.space = (D₂ ∩ N) ∪ Δ₁ ∧
      C' \ B.space = C \ B.space ∧
      frontier (((↑) : K.space → E) ⁻¹' B.space) =
        ((↑) : K.space → E) ⁻¹' ((D₂ ∩ N) ∪ Δ₁) ∧
      IsClosed (((↑) : K.space → E) ⁻¹' C') ∧
      Separates (((↑) : K.space → E) ⁻¹' C') H Q := by
  classical
  let _ : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (isPolyhedron_space K).isCompact
  let H' : Set E := ((↑) : K.space → E) '' H
  let Q' : Set E := ((↑) : K.space → E) '' Q
  let U := (H' ∪ Q')ᶜ
  have hH'closed : IsClosed H' :=
    (hHclosed.isCompact.image continuous_subtype_val).isClosed
  have hQ'closed : IsClosed Q' :=
    (hQclosed.isCompact.image continuous_subtype_val).isClosed
  have hΔC : Δ ⊆ C := hΔD₁.trans hD₁C
  have hΔU : Δ ⊆ U := by
    intro x hxΔ hx
    rcases hx with ⟨y, hyH, rfl⟩ | ⟨y, hyQ, rfl⟩
    · exact hsep.left_subset_compl hyH (hΔC hxΔ)
    · exact hsep.right_subset_compl hyQ (hΔC hxΔ)
  have hUopen : IsOpen U := (hH'closed.union hQ'closed).isOpen_compl
  have hU : U ∈ 𝓝ˢ[K.space] Δ :=
    Filter.mem_inf_of_left (mem_nhdsSet_iff_forall.mpr fun x hx => hUopen.mem_nhds (hΔU hx))
  obtain ⟨N, B, g, A₁, Δ₁, C', hBfin, hN, hB, hΔN, hNK, hNU,
      hnhds, hBN, hg, hmiddleB, hA₁, hA₁B, hΔ₁, hΔ₁B, hboundary,
      hmiddleMeet, hC', hCtrace, hC'trace, houtside⟩ :=
    hK.exists_surface_split_local_traces hΔ hr₁ hr₂ hΔintD₁ hΔintD₂ hΔD₁ hΔD₂
      hD₁D₂ hD₁K hD₂K hD₁C hD₂C hlocal hU
  let _ : Finite B.faces := hBfin.to_subtype
  have hKB : (boundaryComplex 3 K).space = ∅ := by
    change (⋃ t ∈ (boundaryComplex 3 K).faces, convexHull ℝ (t : Set E)) = ∅
    rw [hK.boundaryComplex_faces_eq_empty]
    simp
  have hBdis : Disjoint B.space (boundaryComplex 3 K).space := by
    rw [hKB]
    exact disjoint_empty B.space
  have hBK : B.space ⊆ K.space := hBN.trans hNK
  have hfrontier :
      frontier (((↑) : K.space → E) ⁻¹' B.space) =
        ((↑) : K.space → E) ⁻¹' (boundaryComplex 3 B).space :=
    frontier_preimage_space_eq_preimage_boundaryComplex K B
      hK.isCombinatorialManifoldWithBoundary hB.isCombinatorialManifoldWithBoundary hBK hBdis
  have hfrontierSplit :
      frontier (((↑) : K.space → E) ⁻¹' B.space) =
        ((↑) : K.space → E) ⁻¹' ((D₂ ∩ N) ∪ Δ₁) := by
    rw [hfrontier, hboundary]
  have hfrontierC' :
      frontier (((↑) : K.space → E) ⁻¹' B.space) ⊆
        ((↑) : K.space → E) ⁻¹' C' := by
    intro x hx
    exact (hC'trace.symm.subset (hfrontierSplit.subset hx)).1
  have hmiddleClosed : IsClosed (D₂ ∩ N) :=
    (show IsPLBall 2 (D₂ ∩ N) from ⟨g, hg⟩).isPolyhedron.isClosed
  have hC'interClosed : IsClosed
      ((((↑) : K.space → E) ⁻¹' C') ∩ ((↑) : K.space → E) ⁻¹' B.space) := by
    rw [← preimage_inter, hC'trace]
    exact (hmiddleClosed.union hΔ₁.isPolyhedron.isClosed).preimage continuous_subtype_val
  have hBclosed : IsClosed (((↑) : K.space → E) ⁻¹' B.space) :=
    hB.isPolyhedron.isClosed.preimage continuous_subtype_val
  have houtside' :
      (((↑) : K.space → E) ⁻¹' C') \ ((↑) : K.space → E) ⁻¹' B.space =
        (((↑) : K.space → E) ⁻¹' C) \ ((↑) : K.space → E) ⁻¹' B.space := by
    simpa only [preimage_sdiff] using congrArg (preimage ((↑) : K.space → E)) houtside
  have hC'eq :
      ((↑) : K.space → E) ⁻¹' C' =
        ((((↑) : K.space → E) ⁻¹' C) \
          interior (((↑) : K.space → E) ⁻¹' B.space)) ∪
        ((((↑) : K.space → E) ⁻¹' C') ∩ ((↑) : K.space → E) ⁻¹' B.space) := by
    apply Subset.antisymm
    · intro x hxC'
      by_cases hxB : x ∈ ((↑) : K.space → E) ⁻¹' B.space
      · exact Or.inr ⟨hxC', hxB⟩
      · have hxout : x ∈
            (((↑) : K.space → E) ⁻¹' C') \ ((↑) : K.space → E) ⁻¹' B.space :=
          ⟨hxC', hxB⟩
        rw [houtside'] at hxout
        exact Or.inl ⟨hxout.1, fun hx => hxB (interior_subset hx)⟩
    · rintro x (hx | hx)
      · by_cases hxB : x ∈ ((↑) : K.space → E) ⁻¹' B.space
        · apply hfrontierC'
          rw [hBclosed.frontier_eq]
          exact ⟨hxB, hx.2⟩
        · have hxout : x ∈
              (((↑) : K.space → E) ⁻¹' C) \ ((↑) : K.space → E) ⁻¹' B.space :=
            ⟨hx.1, hxB⟩
          rw [← houtside'] at hxout
          exact hxout.1
      · exact hx.1
  have hC'closed : IsClosed (((↑) : K.space → E) ⁻¹' C') := by
    rw [hC'eq]
    exact (hCclosed.sdiff isOpen_interior).union hC'interClosed
  have hNtargets : N ⊆ (H' ∪ Q')ᶜ := by
    simpa only [U] using hNU
  have hBtargets : B.space ⊆ (H' ∪ Q')ᶜ := hBN.trans hNtargets
  have hHB : H ⊆ (((↑) : K.space → E) ⁻¹' B.space)ᶜ := by
    intro x hxH hxB
    exact hBtargets hxB (Or.inl ⟨x, hxH, rfl⟩)
  have hQB : Q ⊆ (((↑) : K.space → E) ⁻¹' B.space)ᶜ := by
    intro x hxQ hxB
    exact hBtargets hxB (Or.inr ⟨x, hxQ, rfl⟩)
  have hsep' : Separates (((↑) : K.space → E) ⁻¹' C') H Q :=
    hsep.of_frontier_subset_replacement hC'closed hBclosed houtside'.symm
      hfrontierC' hHB hQB
  exact ⟨N, B, g, A₁, Δ₁, C', hBfin, hN, hB, hΔN, hNK, hNtargets,
    hnhds, hBN, hg, hmiddleB, hA₁, hA₁B, hΔ₁, hΔ₁B, hboundary, hmiddleMeet,
    hC', hCtrace, hC'trace, houtside, hfrontierSplit, hC'closed, hsep'⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_surface_split_preserving_separation
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hdim : Module.finrank ℝ E = 3)
    {H Q C Δ D₁ D₂ : Set E}
    (hHclosed : IsClosed H) (hQclosed : IsClosed Q) (hCclosed : IsClosed C)
    (hsep : Separates C H Q) (hΔ : IsPLBall 2 Δ)
    {r₁ r₂ : (Fin 3 → ℝ) → E}
    (hr₁ : IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁)
    (hr₂ : IsPLHomeomorphOn r₂ (stdSimplex ℝ (Fin 3)) D₂)
    (hΔintD₁ : Δ ⊆ r₁ '' openSimplex (stdVertices 1))
    (hΔintD₂ : Δ ⊆ r₂ '' openSimplex (stdVertices 1))
    (hΔD₁ : Δ ⊆ D₁) (hΔD₂ : Δ ⊆ D₂) (hD₁D₂ : D₁ ∩ D₂ = Δ)
    (hD₁K : D₁ ⊆ K.space) (hD₂K : D₂ ⊆ K.space)
    (hD₁C : D₁ ⊆ C) (hD₂C : D₂ ⊆ C)
    (hlocal : D₁ ∪ D₂ ∈ 𝓝ˢ[C] Δ)
    (hΔboundary : Disjoint Δ (boundaryComplex 3 K).space) :
    ∃ (N : Set E) (B : Geometry.SimplicialComplex ℝ E)
      (g : (Fin 3 → ℝ) → E) (A₁ Δ₁ C' : Set E),
      B.faces.Finite ∧ IsPLBall 3 N ∧ IsPLBall 3 B.space ∧
      Δ ⊆ N ∧ N ⊆ K.space ∧ Disjoint N (boundaryComplex 3 K).space ∧
      N ⊆ (H ∪ Q)ᶜ ∧
      (∀ x ∈ Δ, N ∈ 𝓝[K.space] x) ∧ B.space ⊆ N ∧
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) (D₂ ∩ N) ∧
      D₂ ∩ N ⊆ (boundaryComplex 3 B).space ∧
      A₁ = N ∩ closure (D₁ \ Δ) ∧ A₁ ⊆ B.space ∧
      IsPLBall 2 Δ₁ ∧ Δ₁ ⊆ (boundaryComplex 3 B).space ∧
      (boundaryComplex 3 B).space = (D₂ ∩ N) ∪ Δ₁ ∧
      (D₂ ∩ N) ∩ Δ₁ = g '' stdSimplexBoundary 2 ∧
      C' = (C \ (A₁ \ ((D₂ ∩ N) ∪ Δ₁))) ∪ Δ₁ ∧
      C ∩ B.space = (D₂ ∩ N) ∪ A₁ ∧
      C' ∩ B.space = (D₂ ∩ N) ∪ Δ₁ ∧
      C' \ B.space = C \ B.space ∧
      frontier B.space = (D₂ ∩ N) ∪ Δ₁ ∧ IsClosed C' ∧ Separates C' H Q := by
  classical
  let J := (boundaryComplex 3 K).space
  let U := (H ∪ Q ∪ J)ᶜ
  let _ : Finite (boundaryComplex 3 K).faces :=
    (boundaryComplex_faces_finite 3 K).to_subtype
  have hJclosed : IsClosed J := isPolyhedron_space (boundaryComplex 3 K) |>.isClosed
  have hUopen : IsOpen U := ((hHclosed.union hQclosed).union hJclosed).isOpen_compl
  have hΔC : Δ ⊆ C := hΔD₁.trans hD₁C
  have hΔU : Δ ⊆ U := by
    intro x hxΔ
    change x ∉ H ∪ Q ∪ J
    rintro ((hxH | hxQ) | hxJ)
    · exact hsep.left_subset_compl hxH (hΔC hxΔ)
    · exact hsep.right_subset_compl hxQ (hΔC hxΔ)
    · exact disjoint_left.mp hΔboundary hxΔ hxJ
  have hU : U ∈ 𝓝ˢ[K.space] Δ :=
    Filter.mem_inf_of_left (mem_nhdsSet_iff_forall.mpr fun x hx => hUopen.mem_nhds (hΔU hx))
  have hUdis : Disjoint U (boundaryComplex 3 K).space := by
    rw [disjoint_left]
    intro x hxU hxJ
    change x ∉ H ∪ Q ∪ J at hxU
    exact hxU (Or.inr hxJ)
  obtain ⟨N, B, g, A₁, Δ₁, C', hBfin, hN, hB, hΔN, hNK, hNU,
      hnhds, hBN, hg, hmiddleB, hA₁, hA₁B, hΔ₁, hΔ₁B, hboundary,
      hmiddleMeet, hC', hCtrace, hC'trace, houtside⟩ :=
    hK.exists_surface_split_local_traces hΔ hr₁ hr₂ hΔintD₁ hΔintD₂ hΔD₁ hΔD₂
      hD₁D₂ hD₁K hD₂K hD₁C hD₂C hlocal hU hUdis
  let _ : Finite B.faces := hBfin.to_subtype
  have hNboundary : Disjoint N (boundaryComplex 3 K).space := hUdis.mono_left hNU
  have hNtargets : N ⊆ (H ∪ Q)ᶜ := by
    intro x hxN hx
    have hxU := hNU hxN
    change x ∉ H ∪ Q ∪ J at hxU
    exact hxU (Or.inl hx)
  have hfrontier : frontier B.space = (boundaryComplex 3 B).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank (n := 2) (by simpa using hdim) B
      hB.isCombinatorialManifoldWithBoundary
  have hfrontierSplit : frontier B.space = (D₂ ∩ N) ∪ Δ₁ := by
    rw [hfrontier, hboundary]
  have hfrontierC' : frontier B.space ⊆ C' := by
    intro x hx
    exact (hC'trace.symm.subset (hfrontierSplit.subset hx)).1
  have hmiddleClosed : IsClosed (D₂ ∩ N) :=
    (show IsPLBall 2 (D₂ ∩ N) from ⟨g, hg⟩).isPolyhedron.isClosed
  have hC'interClosed : IsClosed (C' ∩ B.space) := by
    rw [hC'trace]
    exact hmiddleClosed.union hΔ₁.isPolyhedron.isClosed
  have hBclosed : IsClosed B.space := hB.isPolyhedron.isClosed
  have hC'eq : C' = (C \ interior B.space) ∪ (C' ∩ B.space) := by
    apply Subset.antisymm
    · intro x hxC'
      by_cases hxB : x ∈ B.space
      · exact Or.inr ⟨hxC', hxB⟩
      · have hxout : x ∈ C' \ B.space := ⟨hxC', hxB⟩
        rw [houtside] at hxout
        exact Or.inl ⟨hxout.1, fun hx => hxB (interior_subset hx)⟩
    · rintro x (hx | hx)
      · by_cases hxB : x ∈ B.space
        · apply hfrontierC'
          rw [hBclosed.frontier_eq]
          exact ⟨hxB, hx.2⟩
        · have hxout : x ∈ C \ B.space := ⟨hx.1, hxB⟩
          rw [← houtside] at hxout
          exact hxout.1
      · exact hx.1
  have hC'closed : IsClosed C' := by
    rw [hC'eq]
    exact (hCclosed.sdiff isOpen_interior).union hC'interClosed
  have hBtargets : B.space ⊆ (H ∪ Q)ᶜ := hBN.trans hNtargets
  have hHB : H ⊆ B.spaceᶜ := by
    intro x hxH hxB
    exact hBtargets hxB (Or.inl hxH)
  have hQB : Q ⊆ B.spaceᶜ := by
    intro x hxQ hxB
    exact hBtargets hxB (Or.inr hxQ)
  have hsep' : Separates C' H Q :=
    hsep.of_frontier_subset_replacement hC'closed hBclosed houtside.symm hfrontierC' hHB hQB
  exact ⟨N, B, g, A₁, Δ₁, C', hBfin, hN, hB, hΔN, hNK, hNboundary, hNtargets,
    hnhds, hBN, hg, hmiddleB, hA₁, hA₁B, hΔ₁, hΔ₁B, hboundary, hmiddleMeet,
    hC', hCtrace, hC'trace, houtside, hfrontierSplit, hC'closed, hsep'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
