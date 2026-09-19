/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension

/-! Centered prism coordinates for PL three-ball pairs in surface splitting. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem exists_isPLHomeomorphOn_centered_prism_of_boundary_disk_pair
    {P : Set E} (hP : IsPLBall 2 P)
    (K₀ K₁ : Geometry.SimplicialComplex ℝ F) [Finite K₀.faces] [Finite K₁.faces]
    (hK₀ : IsPLBall 3 K₀.space) (hK₁ : IsPLBall 3 K₁.space) {D : Set F}
    (hD₀ : D ⊆ (boundaryComplex 3 K₀).space)
    (hD₁ : D ⊆ (boundaryComplex 3 K₁).space) (hinter : K₀.space ∩ K₁.space = D)
    {g : E → F} (hg : IsPLHomeomorphOn g P D) :
    ∃ ρ : E × ℝ → F,
      IsPLHomeomorphOn ρ (P ×ˢ Icc (-1 : ℝ) 1) (K₀.space ∪ K₁.space) ∧
      (∀ x ∈ P, ρ (x, 0) = g x) ∧
      ρ '' (P ×ˢ Icc (-1 : ℝ) 0) = K₀.space ∧
      ρ '' (P ×ˢ Icc (0 : ℝ) 1) = K₁.space := by
  let _ : DecidableEq F := Classical.decEq _
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  obtain ⟨L, hLfin, hLspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall 2 L.space := hLspace.symm ▸ hP
  have hminus : IsPLBall 3 (P ×ˢ Icc (-1 : ℝ) 0) :=
    isPLBall_three_prod hP (isPLBall_Icc (by norm_num))
  have hplus : IsPLBall 3 (P ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_three_prod hP (isPLBall_Icc (by norm_num))
  obtain ⟨R₀, hR₀fin, hR₀space⟩ := hminus.isPolyhedron.exists_simplicialComplex
  obtain ⟨R₁, hR₁fin, hR₁space⟩ := hplus.isPolyhedron.exists_simplicialComplex
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  let _ : Finite R₁.faces := hR₁fin.to_subtype
  have hR₀ : IsPLBall 3 R₀.space := hR₀space.symm ▸ hminus
  have hR₁ : IsPLBall 3 R₁.space := hR₁space.symm ▸ hplus
  have hboundary₀ := boundaryComplex_space_prism L hL (by norm_num : (-1 : ℝ) < 0)
    R₀ (hLspace.symm ▸ hR₀space)
  have hboundary₁ := boundaryComplex_space_prism L hL (by norm_num : (0 : ℝ) < 1)
    R₁ (hLspace.symm ▸ hR₁space)
  have hmid₀ : P ×ˢ {(0 : ℝ)} ⊆ (boundaryComplex 3 R₀).space := by
    rw [hboundary₀, hLspace]
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact Or.inl ⟨hx, Or.inr ht⟩
  have hmid₁ : P ×ˢ {(0 : ℝ)} ⊆ (boundaryComplex 3 R₁).space := by
    rw [hboundary₁, hLspace]
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact Or.inl ⟨hx, Or.inl ht⟩
  have hmid : IsPLBall 2 (P ×ˢ {(0 : ℝ)}) :=
    hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  have hgmid : IsPLHomeomorphOn (g ∘ Prod.fst) (P ×ˢ {(0 : ℝ)}) D :=
    hP.isPolyhedron.isPLHomeomorphOn_fst_prod_const 0 |>.trans hg
  obtain ⟨f₀, hf₀, hf₀g⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex R₀ K₀ hR₀ hK₀
      hmid hmid₀ hgmid hD₀
  obtain ⟨f₁, hf₁, hf₁g⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex R₁ K₁ hR₁ hK₁
      hmid hmid₁ hgmid hD₁
  rw [hR₀space] at hf₀
  rw [hR₁space] at hf₁
  have hsource :
      (P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1) = P ×ˢ {(0 : ℝ)} := by
    ext ⟨x, t⟩
    constructor
    · rintro ⟨⟨hx, -, htle⟩, ⟨-, htge, -⟩⟩
      exact ⟨hx, le_antisymm htle htge⟩
    · rintro ⟨hx, ht⟩
      change t = 0 at ht
      subst t
      exact ⟨⟨hx, by norm_num, by norm_num⟩, ⟨hx, by norm_num, by norm_num⟩⟩
  have hagree : EqOn f₀ f₁
      ((P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1)) := by
    intro z hz
    have hzmid : z ∈ P ×ˢ {(0 : ℝ)} := hsource.subset hz
    exact (hf₀g hzmid).trans (hf₁g hzmid).symm
  have hsurj : SurjOn f₀
      ((P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1))
      (K₀.space ∩ K₁.space) := by
    intro y hy
    have hyD : y ∈ D := hinter.subset hy
    obtain ⟨x, hx, hxy⟩ := hg.bijOn.surjOn hyD
    have hxmid : (x, (0 : ℝ)) ∈ P ×ˢ {(0 : ℝ)} := ⟨hx, rfl⟩
    refine ⟨(x, 0), hsource.symm.subset hxmid, ?_⟩
    exact (hf₀g hxmid).trans hxy
  obtain ⟨ρ, hρ, hρminus, hρplus⟩ := exists_isPLHomeomorphOn_union
    hminus.isPolyhedron hplus.isPolyhedron hf₀ hf₁ hagree hsurj
  have hunion :
      (P ×ˢ Icc (-1 : ℝ) 0) ∪ (P ×ˢ Icc (0 : ℝ) 1) =
        P ×ˢ Icc (-1 : ℝ) 1 := by
    ext z
    constructor
    · rintro (⟨hz, hzl, hzr⟩ | ⟨hz, hzl, hzr⟩)
      · exact ⟨hz, hzl, hzr.trans (by norm_num)⟩
      · exact ⟨hz, (by norm_num : (-1 : ℝ) ≤ 0).trans hzl, hzr⟩
    · rintro ⟨hz, hzl, hzr⟩
      by_cases ht : z.2 ≤ 0
      · exact Or.inl ⟨hz, hzl, ht⟩
      · exact Or.inr ⟨hz, (lt_of_not_ge ht).le, hzr⟩
  rw [hunion] at hρ
  refine ⟨ρ, hρ, ?_, ?_, ?_⟩
  · intro x hx
    have hxminus : (x, (0 : ℝ)) ∈ P ×ˢ Icc (-1 : ℝ) 0 := ⟨hx, by norm_num⟩
    have hxmid : (x, (0 : ℝ)) ∈ P ×ˢ {(0 : ℝ)} := ⟨hx, rfl⟩
    exact (hρminus hxminus).trans (hf₀g hxmid)
  · exact hρminus.image_eq.trans hf₀.image_eq
  · exact hρplus.image_eq.trans hf₁.image_eq

end DifferentialGeometry.Topology.PiecewiseLinear
