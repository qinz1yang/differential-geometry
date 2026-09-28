/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RectangleArcPair
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_cylindricalDiagram_of_disk_pair {a b : ℝ} (hab : a < b)
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall 2 K.space) (hL : IsPLBall 2 L.space)
    {D₀ D₁ : Set E} (hD₁ : IsPLBall 1 D₁) (hdis : Disjoint D₀ D₁)
    (hD₀K : D₀ ⊆ (boundaryComplex 2 K).space) (hD₁K : D₁ ⊆ (boundaryComplex 2 K).space)
    (hD₀L : D₀ ⊆ (boundaryComplex 2 L).space) (hD₁L : D₁ ⊆ (boundaryComplex 2 L).space)
    (hinter : K.space ∩ L.space = D₀ ∪ D₁)
    {g₀ : ℝ → E} (hg₀ : IsPLHomeomorphOn g₀ (Icc a b) D₀) :
    ∃ φ : ℝ × ℝ → E, IsCylindricalDiagram φ (Icc a b) (K.space ∪ L.space) ∧
      ∀ x ∈ Icc a b, φ (x, 0) = g₀ x := by
  let _ : DecidableEq E := Classical.decEq _
  have hP := isPLBall_Icc hab
  obtain ⟨f, hf, hf₀, hfm⟩ := exists_isPLHomeomorphOn_rectangle_map_ends hab
    (by norm_num : (0 : ℝ) < 1 / 2) K hK hD₀K hD₁ hD₁K hdis hg₀
  have hmidpoly : IsPolyhedron (Icc a b ×ˢ {(1 / 2 : ℝ)}) :=
    (hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const (1 / 2))).isPolyhedron
  have hfmid : IsPLHomeomorphOn f (Icc a b ×ˢ {1 / 2}) D₁ := by
    have h := hf.restrict hmidpoly (fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨by norm_num, le_rfl⟩⟩)
    rwa [hfm] at h
  let g₁ : ℝ → E := fun x => f (x, 1 / 2)
  have hg₁ : IsPLHomeomorphOn g₁ (Icc a b) D₁ :=
    (hP.isPolyhedron.isPLHomeomorphOn_prod_const (1 / 2)).trans hfmid
  obtain ⟨g, hg, hgm, hg₁⟩ := exists_isPLHomeomorphOn_rectangle_map_ends hab
    (by norm_num : (1 / 2 : ℝ) < 1) L hL hD₁L (hP.of_isPLHomeomorphOn hg₀) hD₀L hdis.symm hg₁
  have hfzero : f '' (Icc a b ×ˢ {0}) = D₀ := by
    have heq : EqOn (f ∘ fun x : ℝ => (x, (0 : ℝ))) g₀ (Icc a b) := hf₀
    rw [← (hP.isPolyhedron.isPLHomeomorphOn_prod_const 0).image_eq, image_image]
    exact heq.image_eq.trans hg₀.image_eq
  have hfg : EqOn f g (Icc a b ×ˢ {1 / 2}) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    change t = 1 / 2 at ht
    subst t
    exact (hgm x hx).symm
  refine ⟨_,
    isCylindricalDiagram_piecewise hP.isPolyhedron hf hg hfzero hg₁ hfm hfg hinter, ?_⟩
  intro x hx
  simp only [Set.piecewise,
    ite_eq_left (show (x, (0 : ℝ)) ∈ Icc a b ×ˢ Icc 0 (1 / 2) from ⟨hx, by norm_num⟩)]
  exact hf₀ x hx

end DifferentialGeometry.Topology.PiecewiseLinear
