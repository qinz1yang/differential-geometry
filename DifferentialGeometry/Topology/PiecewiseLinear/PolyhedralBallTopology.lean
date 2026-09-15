import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialPiece
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import Mathlib.Analysis.Convex.PathConnected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) X] [T2Space X]

omit [FiniteDimensional ℝ E] in
private theorem convex_openSimplex' (s : Finset E) : Convex ℝ (openSimplex s) := by
  rintro x ⟨a, ha, ha₁, hax⟩ y ⟨b, hb, hb₁, hby⟩ u v hu hv huv
  refine ⟨fun z => u * a z + v * b z, ?_, ?_, ?_⟩
  · intro z hz
    rcases hu.eq_or_lt with rfl | hu'
    · have hv' : v = 1 := by simpa using huv
      simpa [hv'] using hb z hz
    · exact add_pos_of_pos_of_nonneg (mul_pos hu' (ha z hz)) (mul_nonneg hv (hb z hz).le)
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ha₁, hb₁]
    simpa using huv
  · simp_rw [add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hax, hby]

open Classical in
theorem PLPieceIn.interior_eq_image_openSimplex
    {P : Set X} (T : PLPieceIn E (n + 1) X P)
    (hT : IsPLBall (n + 1) T.complex.space)
    {f : (Fin (n + 2) → ℝ) → E}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) T.complex.space) :
    interior P = (T.map ∘ f) '' openSimplex (stdVertices n) := by
  classical
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  have hman : IsCombinatorialManifoldWithBoundary (n + 1) T.complex :=
    hT.isCombinatorialManifoldWithBoundary
  have hboundary := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex T.complex hf
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := T.bijOn.surjOn (interior_subset hy)
    have hznot := (T.mem_interior_iff_not_mem_boundaryComplex_space hman hz).mp hy
    obtain ⟨x, hx, hfx⟩ := hf.bijOn.surjOn hz
    refine ⟨x, ?_, ?_⟩
    · rw [openSimplex_eq_sdiff_simplexBoundary (stdVertices n)
        (stdVertices_affineIndependent n), convexHull_stdVertices]
      refine ⟨hx, ?_⟩
      intro hxB
      apply hznot
      rw [hboundary]
      exact ⟨x, hxB, hfx⟩
    · change T.map (f x) = T.map z
      rw [hfx]
  · rintro ⟨x, hx, rfl⟩
    rw [openSimplex_eq_sdiff_simplexBoundary (stdVertices n)
      (stdVertices_affineIndependent n), convexHull_stdVertices] at hx
    have hfx : f x ∈ T.complex.space := hf.bijOn.mapsTo hx.1
    apply (T.mem_interior_iff_not_mem_boundaryComplex_space hman hfx).mpr
    rw [hboundary]
    rintro ⟨z, hzB, hzx⟩
    have hz : z ∈ stdSimplex ℝ (Fin (n + 2)) :=
      simplexBoundary_stdVertices_space_subset n hzB
    have heq : z = x := hf.bijOn.injOn hz hx.1 hzx
    exact hx.2 (heq ▸ hzB)

open Classical in
theorem IsPolyhedralBall.isPreconnected_interior {P : Set X}
    (hP : IsPolyhedralBall (n := n + 1) (n + 1) P) : IsPreconnected (interior P) := by
  obtain ⟨T, hT⟩ := hP
  obtain ⟨f, hf⟩ := hT
  rw [T.piece.interior_eq_image_openSimplex (⟨f, hf⟩ : IsPLBall (n + 1)
    T.piece.complex.space) hf]
  exact (convex_openSimplex' (stdVertices n)).isPreconnected.image (T.piece.map ∘ f)
    (T.piece.continuousOn.comp
      (hf.isPiecewiseAffineOn.continuousOn.mono openSimplex_stdVertices_subset_stdSimplex)
      fun x hx => hf.bijOn.mapsTo (openSimplex_stdVertices_subset_stdSimplex hx))

theorem IsPolyhedralBall.eq_of_frontier_eq_of_interior_inter_nonempty
    {P Q : Set X} (hP : IsPolyhedralBall (n := n + 1) (n + 1) P)
    (hQ : IsPolyhedralBall (n := n + 1) (n + 1) Q)
    (hfront : frontier P = frontier Q)
    (hinter : (interior P ∩ interior Q).Nonempty) : P = Q := by
  have hPclosed : IsClosed P := hP.isPolyhedralManifoldWithBoundary.isCompact.isClosed
  have hQclosed : IsClosed Q := hQ.isPolyhedralManifoldWithBoundary.isCompact.isClosed
  have hPsub : interior P ⊆ interior Q ∪ Qᶜ := by
    intro x hxP
    by_cases hxQ : x ∈ Q
    · left
      by_contra hxQi
      have hxF : x ∈ frontier Q := by
        rw [hQclosed.frontier_eq]
        exact ⟨hxQ, hxQi⟩
      rw [← hfront, hPclosed.frontier_eq] at hxF
      exact hxF.2 hxP
    · exact Or.inr hxQ
  have hPQ : interior P ⊆ interior Q :=
    hP.isPreconnected_interior.subset_left_of_subset_union isOpen_interior
      hQclosed.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hPsub hinter
  have hQsub : interior Q ⊆ interior P ∪ Pᶜ := by
    intro x hxQ
    by_cases hxP : x ∈ P
    · left
      by_contra hxPi
      have hxF : x ∈ frontier P := by
        rw [hPclosed.frontier_eq]
        exact ⟨hxP, hxPi⟩
      rw [hfront, hQclosed.frontier_eq] at hxF
      exact hxF.2 hxQ
    · exact Or.inr hxP
  have hQP : interior Q ⊆ interior P :=
    hQ.isPreconnected_interior.subset_left_of_subset_union isOpen_interior
      hPclosed.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hQsub
        (by obtain ⟨x, hxP, hxQ⟩ := hinter; exact ⟨x, hxQ, hxP⟩)
  have hintereq : interior P = interior Q := Subset.antisymm hPQ hQP
  ext x
  constructor
  · intro hxP
    by_cases hxi : x ∈ interior P
    · exact interior_subset (hintereq ▸ hxi)
    · have hxF : x ∈ frontier P := by
        rw [hPclosed.frontier_eq]
        exact ⟨hxP, hxi⟩
      have hxFQ : x ∈ frontier Q := hfront ▸ hxF
      have hxcl := frontier_subset_closure hxFQ
      rwa [hQclosed.closure_eq] at hxcl
  · intro hxQ
    by_cases hxi : x ∈ interior Q
    · exact interior_subset (hintereq.symm ▸ hxi)
    · have hxF : x ∈ frontier Q := by
        rw [hQclosed.frontier_eq]
        exact ⟨hxQ, hxi⟩
      have hxFP : x ∈ frontier P := hfront.symm ▸ hxF
      have hxcl := frontier_subset_closure hxFP
      rwa [hPclosed.closure_eq] at hxcl

end DifferentialGeometry.Topology.PiecewiseLinear
