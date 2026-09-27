import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorusOfCylindricalDiagram
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsCylindricalDiagram.exists_manifold_complex_of_disk
    {f : E × ℝ → F} {P : Set E} {S : Set F}
    (h : IsCylindricalDiagram f P S) (hP : IsPLBall 2 P) :
    ∃ M : Geometry.SimplicialComplex ℝ F, M.faces.Finite ∧ M.space = S ∧
      IsCombinatorialManifoldWithBoundary 3 M := by
  classical
  have hPc : IsCompact P := hP.isPolyhedron.isCompact
  obtain ⟨C₀, hC₀fin, hC₀sp, hC₀, hC₀lo, -⟩ := h.exists_simplicialComplex_slab hP le_rfl
    (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num) (Or.inr (by norm_num))
  obtain ⟨C₁, hC₁fin, hC₁sp, -, -, -⟩ := h.exists_simplicialComplex_slab hP
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) < 2 / 3) (by norm_num)
    (Or.inl (by norm_num))
  obtain ⟨C₂, hC₂fin, hC₂sp, hC₂, -, hC₂hi⟩ := h.exists_simplicialComplex_slab hP
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1) le_rfl
    (Or.inl (by norm_num))
  let _ : Finite C₀.faces := hC₀fin.to_subtype
  let _ : Finite C₁.faces := hC₁fin.to_subtype
  let _ : Finite C₂.faces := hC₂fin.to_subtype
  have h02 : C₀.space ∩ C₂.space = f '' (P ×ˢ {0}) := by
    rw [hC₀sp, hC₂sp]
    exact h.image_strip_inter_ends (by norm_num) (by norm_num) (by norm_num)
  have hD₀ : IsPLBall 2 (f '' (P ×ˢ {0})) :=
    hP.of_isPLHomeomorphOn (h.isPLHomeomorphOn_slice hP.isPolyhedron (by norm_num))
  have hC₂top : f '' (P ×ˢ {0}) ⊆ (boundaryComplex 3 C₂).space := by
    rw [← h.image_top_eq_bottom]
    exact hC₂hi
  have hunion : C₀.space ∪ C₁.space ∪ C₂.space = S := by
    rw [hC₀sp, hC₁sp, hC₂sp, ← image_union, ← image_union, ← prod_union, ← prod_union,
      Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 2 / 3),
      Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) ≤ 1),
      h.image_eq]
  have hSpoly : IsPolyhedron S := by
    rw [← hunion]
    exact ((isPolyhedron_space C₀).union (isPolyhedron_space C₁)).union (isPolyhedron_space C₂)
  obtain ⟨M, hMfin, hMsp⟩ := hSpoly.exists_simplicialComplex
  let _ : Finite M.faces := hMfin.to_subtype
  have hseam : IsPLBall 3 (C₀.space ∪ C₂.space) :=
    isPLBall_union_of_boundary_disk C₀ C₂ hC₀ hC₂ (h02 ▸ hD₀) (h02 ▸ hC₀lo) (h02 ▸ hC₂top)
  have hprod := isPLBall_three_prod hP (isPLBall_Icc (by norm_num : (1 / 4 : ℝ) < 3 / 4))
  have hmid : IsPLBall 3 (f '' (P ×ˢ Icc (1 / 4) (3 / 4))) :=
    hprod.of_isPLHomeomorphOn (h.isPLHomeomorphOn_strip hP.isPolyhedron (by norm_num)
      (by norm_num) (Or.inl (by norm_num)))
  have hM : IsCombinatorialManifoldWithBoundary 3 M := by
    refine isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods (n := 2) M ?_
    intro p hp
    rw [hMsp] at hp ⊢
    rw [← h.image_eq] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    by_cases hxm : 1 / 4 < x.2 ∧ x.2 < 3 / 4
    · refine ⟨f '' (P ×ˢ Icc (1 / 4) (3 / 4)), hmid, ?_, ?_⟩
      · rw [← h.image_eq]
        exact image_mono (prod_mono subset_rfl (Icc_subset_Icc (by norm_num) (by norm_num)))
      · refine mem_nhdsWithin.mpr ⟨(f '' (P ×ˢ Icc 0 (1 / 4)) ∪ f '' (P ×ˢ Icc (3 / 4) 1))ᶜ,
          ((h.isClosed_image_strip hPc le_rfl (by norm_num)).union
            (h.isClosed_image_strip hPc (by norm_num) le_rfl)).isOpen_compl, ?_, ?_⟩
        · rw [mem_compl_iff, mem_union, not_or]
          exact ⟨h.apply_notMem_image_strip hx le_rfl (by norm_num)
              (fun hmem => by linarith [hmem.2, hxm.1])
              (fun _ => ⟨by linarith [hxm.1], by linarith [hxm.2]⟩),
            h.apply_notMem_image_strip hx (by norm_num) le_rfl
              (fun hmem => by linarith [hmem.1, hxm.2])
              (fun _ => ⟨by linarith [hxm.1], by linarith [hxm.2]⟩)⟩
        · rintro y ⟨hyK, hyS⟩
          rw [mem_compl_iff, mem_union, not_or] at hyK
          rw [← h.image_eq] at hyS
          obtain ⟨z, hz, rfl⟩ := hyS
          by_cases hz1 : z.2 ≤ 1 / 4
          · exact (hyK.1 ⟨z, ⟨hz.1, hz.2.1, hz1⟩, rfl⟩).elim
          · by_cases hz2 : 3 / 4 ≤ z.2
            · exact (hyK.2 ⟨z, ⟨hz.1, hz2, hz.2.2⟩, rfl⟩).elim
            · exact ⟨z, ⟨hz.1, (not_le.mp hz1).le, (not_le.mp hz2).le⟩, rfl⟩
    · have hx' : x.2 ∉ Icc (1 / 3 : ℝ) (2 / 3) := fun hmem =>
        hxm ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      refine ⟨C₀.space ∪ C₂.space, hseam, ?_, ?_⟩
      · rw [← hunion]
        exact union_subset (subset_union_left.trans subset_union_left) subset_union_right
      · refine mem_nhdsWithin.mpr
          ⟨C₁.spaceᶜ, (isPolyhedron_space C₁).isClosed.isOpen_compl, ?_, ?_⟩
        · rw [mem_compl_iff, hC₁sp]
          exact h.apply_notMem_image_strip hx (by norm_num) (by norm_num) hx'
            (fun hend => by norm_num at hend)
        · rintro y ⟨hyC, hyS⟩
          rw [← hunion] at hyS
          rcases hyS with (hy | hy) | hy
          · exact Or.inl hy
          · exact (hyC hy).elim
          · exact Or.inr hy
  exact ⟨M, hMfin, hMsp, hM⟩

theorem IsCylindricalDiagram.frontier_eq_image_base_frontier
    {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPLBall 2 P)
    (hdimE : Module.finrank ℝ E = 2) (hdimF : Module.finrank ℝ F = 3) :
    frontier S = f '' (frontier P ×ˢ Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨D, hDfin, hDsp⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨M, hMfin, hMsp, hM⟩ := hf.exists_manifold_complex_of_disk hP
  let _ : Finite D.faces := hDfin.to_subtype
  let _ : Finite M.faces := hMfin.to_subtype
  have hD : IsPLBall 2 D.space := hDsp.symm ▸ hP
  have hfrontD := frontier_space_eq_boundaryComplex_space_of_finrank hdimE D
    hD.isCombinatorialManifoldWithBoundary
  have hfD : IsCylindricalDiagram f D.space M.space := by
    rw [hDsp, hMsp]
    exact hf
  have hfront := hfD.frontier_eq_image_side D M hD hM hdimF
  rwa [← hfrontD, hDsp, hMsp] at hfront

end DifferentialGeometry.Topology.PiecewiseLinear
