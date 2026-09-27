import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalAnnuli
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCylindricalDiagram.exists_base_arc_annulus_complex
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P A : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    {δ : ℝ → E} (hδ : IsPLHomeomorphOn δ (Icc 0 1) A) (hAP : A ⊆ P) :
    ∃ H : Geometry.SimplicialComplex ℝ F, H.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 H ∧ IsConnected H.space ∧
      H.space = f '' (A ×ˢ Icc (0 : ℝ) 1) ∧
      (boundaryComplex 2 H).space = f '' ({δ 0} ×ˢ Icc (0 : ℝ) 1) ∪
        f '' ({δ 1} ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨ρ, hρ, hzero, hone⟩ := hf.exists_annulus_chart_of_base_arc hends hδ hAP
  have hcircle : IsPLSphere 1 (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPLSphere_simplexBoundary_std 1
  obtain ⟨H, hHfin, hH, hconn, hspace, hboundary⟩ :=
    hρ.exists_annulus_complex hcircle (by norm_num)
  refine ⟨H, hHfin, hH, hconn, hspace, ?_⟩
  rw [hboundary, ← singleton_union, prod_union, image_union, hzero, hone]

open Classical in
theorem IsCylindricalDiagram.exists_filling_face_annuli
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hdim : Module.finrank ℝ E = 3)
    {f : (ℝ × ℝ) × ℝ → E}
    (hf : IsCylindricalDiagram f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R.space)
    (hends : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f (x, 0) = f (x, 1))
    {A : Fin 2 → Set (ℝ × ℝ)} {δ : Fin 2 → ℝ → ℝ × ℝ} {p : Fin 2 → ℝ × ℝ}
    (hδ : ∀ k, IsPLHomeomorphOn (δ k) (Icc 0 1) (A k))
    (hzero : ∀ k, δ k 0 = p 0) (hone : ∀ k, δ k 1 = p 1)
    (hcover : A 0 ∪ A 1 = frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hinter : A 0 ∩ A 1 = {p 0, p 1}) :
    ∃ H : Fin 2 → Geometry.SimplicialComplex ℝ E,
      (∀ k, (H k).faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 (H k) ∧
        IsConnected (H k).space ∧ (H k).space = f '' (A k ×ˢ Icc (0 : ℝ) 1) ∧
        (boundaryComplex 2 (H k)).space = f '' ({p 0} ×ˢ Icc (0 : ℝ) 1) ∪
          f '' ({p 1} ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ k, (H k).space ⊆ (boundaryComplex 3 R).space) ∧
      (H 0).space ∪ (H 1).space = (boundaryComplex 3 R).space ∧
      (H 0).space ∩ (H 1).space = f '' ({p 0} ×ˢ Icc (0 : ℝ) 1) ∪
        f '' ({p 1} ×ˢ Icc (0 : ℝ) 1) := by
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  have hAfront (k : Fin 2) : A k ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hcover]
    fin_cases k
    · exact subset_union_left
    · exact subset_union_right
  have hAP (k : Fin 2) : A k ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    (hAfront k).trans isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
  choose H hHfin hH hconn hspace hboundary using
    fun k => hf.exists_base_arc_annulus_complex hends (hδ k) (hAP k)
  obtain ⟨B, hBfin, hBspace⟩ := isPLBall_unit_square.isPolyhedron.exists_simplicialComplex
  let _ : Finite B.faces := hBfin.to_subtype
  have hB : IsPLBall 2 B.space := hBspace.symm ▸ isPLBall_unit_square
  have hfB : IsCylindricalDiagram f B.space R.space := hBspace.symm ▸ hf
  have hside := hfB.frontier_eq_image_side B R hB hR hdim
  have hBfront := frontier_space_eq_boundaryComplex_space_of_finrank
    (by simp : Module.finrank ℝ (ℝ × ℝ) = 2) B hB.isCombinatorialManifoldWithBoundary
  rw [← hBfront, hBspace, frontier_space_eq_boundaryComplex_space_of_finrank hdim R hR] at hside
  have hfull : (H 0).space ∪ (H 1).space = (boundaryComplex 3 R).space := by
    rw [hspace 0, hspace 1, ← image_union, ← union_prod, hcover, ← hside]
  refine ⟨H, ?_, ?_, hfull, ?_⟩
  · intro k
    exact ⟨hHfin k, hH k, hconn k, hspace k, by simpa only [hzero, hone] using hboundary k⟩
  · intro k
    rw [← hfull]
    fin_cases k
    · exact subset_union_left
    · exact subset_union_right
  · rw [hspace 0, hspace 1, hf.inter_images_base_regions hends (hAP 0) (hAP 1),
      hinter, ← singleton_union, union_prod, image_union]

open Classical in
theorem boundary_rim_tube_interiors_mem_nhdsSetWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Geometry.SimplicialComplex ℝ E) {J C : Fin 2 → Set E}
    (hboundary : (boundaryComplex 2 H).space = J 0 ∪ J 1)
    (hJC : ∀ k, J k ⊆ interior (C k)) :
    H.space ∩ (interior (C 0) ∪ interior (C 1)) ∈
      𝓝ˢ[H.space] (boundaryComplex 2 H).space := by
  refine mem_nhdsSetWithin.mpr ⟨interior (C 0) ∪ interior (C 1),
    isOpen_interior.union isOpen_interior, ?_, fun _ hx => ⟨hx.2, hx.1⟩⟩
  rw [hboundary]
  exact union_subset_union (hJC 0) (hJC 1)

end DifferentialGeometry.Topology.PiecewiseLinear
