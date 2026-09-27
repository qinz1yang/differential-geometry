/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PrismFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.Connected.SeparatorLocation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsCylindricalDiagram.frontier_image_right_strip
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {f : E × ℝ → F} {S : Set F} (hf : IsCylindricalDiagram f D.space S)
    (hdim : Module.finrank ℝ F = 3) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    frontier (f '' (D.space ×ˢ Icc a 1)) =
      f '' ((boundaryComplex 2 D).space ×ˢ Icc a 1) ∪
        f '' (D.space ×ˢ {0}) ∪ f '' (D.space ×ˢ {a}) := by
  have hstrip := hf.isPLHomeomorphOn_strip hD.isPolyhedron ha.1.le le_rfl (Or.inl ha.1)
  rw [hstrip.frontier_prism_image D hD ha.2 hdim, image_union,
    show D.space ×ˢ {a, (1 : ℝ)} = D.space ×ˢ {a} ∪ D.space ×ˢ {1} by
      rw [← prod_union, singleton_union], image_union, hf.image_top_eq_bottom]
  ext x
  simp only [mem_union]
  tauto

open Classical in
theorem IsCylindricalDiagram.separates_side_and_capped_side
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hdim : Module.finrank ℝ F = 3) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    {H K : Set F} (hH : H ⊆ interior (f '' (D.space ×ˢ Icc a 1)))
    (hK : K ⊆ M.spaceᶜ) :
    Separates (f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)) H K ∧
      Separates (f '' ((boundaryComplex 2 D).space ×ˢ Icc a 1) ∪
        f '' (D.space ×ˢ {0}) ∪ f '' (D.space ×ˢ {a})) H K := by
  have hsub : f '' (D.space ×ˢ Icc a 1) ⊆ M.space := by
    rw [← hf.image_eq]
    exact image_mono (fun _ hx => ⟨hx.1, ha.1.le.trans hx.2.1, hx.2.2⟩)
  have hMclosed := (isPolyhedron_space M).isClosed
  have hball : IsPLBall 3 (f '' (D.space ×ˢ Icc a 1)) :=
    (isPLBall_three_prod hD (isPLBall_Icc ha.2)).of_isPLHomeomorphOn
      (hf.isPLHomeomorphOn_strip hD.isPolyhedron ha.1.le le_rfl (Or.inl ha.1))
  constructor
  · rw [← hf.frontier_eq_image_side D M hD hM hdim]
    apply separates_frontier (hH.trans (interior_mono hsub))
    rwa [hMclosed.isOpen_compl.interior_eq]
  · rw [← hf.frontier_image_right_strip D hD hdim ha]
    apply separates_frontier hH
    rw [hball.isPolyhedron.isClosed.isOpen_compl.interior_eq]
    exact hK.trans (compl_subset_compl.mpr hsub)

open Classical in
theorem IsCylindricalDiagram.exists_separating_ball_pair
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hdim : Module.finrank ℝ F = 3) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ H K : Set F, IsPLBall 3 H ∧ IsPLBall 3 K ∧
      (interior H).Nonempty ∧ (interior K).Nonempty ∧
      H ⊆ interior (f '' (D.space ×ˢ Icc a 1)) ∧ K ⊆ M.spaceᶜ ∧ Disjoint H K ∧
      Separates (f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)) H K ∧
      Separates (f '' ((boundaryComplex 2 D).space ×ˢ Icc a 1) ∪
        f '' (D.space ×ˢ {0}) ∪ f '' (D.space ×ˢ {a})) H K := by
  let _ : Nontrivial F := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ F)
  have hball : IsPLBall 3 (f '' (D.space ×ˢ Icc a 1)) :=
    (isPLBall_three_prod hD (isPLBall_Icc ha.2)).of_isPLHomeomorphOn
      (hf.isPLHomeomorphOn_strip hD.isPolyhedron ha.1.le le_rfl (Or.inl ha.1))
  obtain ⟨B, hBfin, hBsp⟩ := hball.isPolyhedron.exists_simplicialComplex
  let _ : Finite B.faces := hBfin.to_subtype
  have hB : IsPLBall 3 B.space := hBsp.symm ▸ hball
  have hBman := hB.isCombinatorialManifoldWithBoundary
  obtain ⟨p, hp⟩ := hB
  obtain ⟨q, hq, hqbd⟩ := hp.isConnected_sdiff_image_stdSimplexBoundary.nonempty
  have hqint : q ∈ interior B.space := by
    by_contra hnot
    apply hqbd
    rw [← simplexBoundary_stdVertices_space,
      ← boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex B hp,
      ← frontier_space_eq_boundaryComplex_space_of_finrank hdim B hBman]
    exact ⟨subset_closure hq, hnot⟩
  obtain ⟨z, hz⟩ := nonempty_compl.mpr (isPolyhedron_space M).isCompact.ne_univ
  obtain ⟨T₀, hT₀, hcard₀, -, hsub₀, hnhds₀⟩ := exists_affineIndependent_openSimplex_subset
    (n := 2) hdim q (isOpen_interior.mem_nhds (hBsp ▸ hqint))
  obtain ⟨T₁, hT₁, hcard₁, -, hsub₁, hnhds₁⟩ := exists_affineIndependent_openSimplex_subset
    (n := 2) hdim z ((isPolyhedron_space M).isClosed.isOpen_compl.mem_nhds hz)
  have hBsub : f '' (D.space ×ˢ Icc a 1) ⊆ M.space := by
    rw [← hf.image_eq]
    exact image_mono (fun _ hx => ⟨hx.1, ha.1.le.trans hx.2.1, hx.2.2⟩)
  have hdis : Disjoint (convexHull ℝ (T₀ : Set F)) (convexHull ℝ (T₁ : Set F)) :=
    disjoint_compl_right.mono (hsub₀.trans (interior_subset.trans hBsub)) hsub₁
  exact ⟨_, _, isPLBall_convexHull_of_affineIndependent T₀ hT₀ hcard₀,
    isPLBall_convexHull_of_affineIndependent T₁ hT₁ hcard₁,
    ⟨q, mem_interior_iff_mem_nhds.mpr hnhds₀⟩,
    ⟨z, mem_interior_iff_mem_nhds.mpr hnhds₁⟩, hsub₀, hsub₁, hdis,
    hf.separates_side_and_capped_side D M hD hM hdim ha hsub₀ hsub₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
