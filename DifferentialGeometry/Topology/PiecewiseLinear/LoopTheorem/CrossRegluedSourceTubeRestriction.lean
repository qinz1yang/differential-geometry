/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell
import DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem CrossSeamTubeCore.precomp
    {M : Type u} [TopologicalSpace M] {chart : (ℝ × ℝ) × ℝ → M}
    {D S Γ U : Set M} (T : CrossSeamTubeCore chart D S Γ U)
    {f : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ}
    (hf : ContinuousOn f spliceCylinder) (hinj : InjOn f spliceCylinder)
    (hcyl : MapsTo f spliceCylinder spliceCylinder)
    (hcore : f '' spliceCore = spliceCore)
    (hfig : f '' crossingFigure = crossingFigure ∩ f '' spliceCylinder) :
    CrossSeamTubeCore (chart ∘ f) D S Γ U := by
  have hsub : (chart ∘ f) '' spliceCylinder ⊆ chart '' spliceCylinder := by
    rw [image_comp]
    exact image_mono hcyl.image_subset
  refine ⟨T.isOpen_tube, T.continuousOn_chart.comp hf hcyl, T.injOn_chart.comp hinj hcyl,
    hsub.trans T.image_subset_tube, ?_, ?_, T.double_inter_tube⟩
  · rw [image_comp, hcore, T.image_spliceCore]
  · rw [image_comp, hfig]
    have hcross : crossingFigure ⊆ spliceCylinder := by
      intro p hp
      exact ⟨hp.1.elim And.left And.left, hp.2⟩
    rw [T.injOn_chart.image_inter hcross hcyl.image_subset]
    rw [T.image_crossingFigure, image_comp]
    exact inter_assoc D (chart '' spliceCylinder) (chart '' (f '' spliceCylinder)) |>.trans
      (congrArg (D ∩ ·) (inter_eq_right.mpr (image_mono hcyl.image_subset)))

theorem PLSeamTubeChart.nonempty_precomp
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {chart : (ℝ × ℝ) × ℝ → M} (C : PLSeamTubeChart M chart)
    {f : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ}
    (hf : IsPLHomeomorphOn f spliceCylinder (f '' spliceCylinder))
    (hcyl : MapsTo f spliceCylinder spliceCylinder) :
    Nonempty (PLSeamTubeChart M (chart ∘ f)) := by
  have hpoly := isHPolytope_spliceCylinder.isPolyhedron.image_of_isPiecewiseAffineOn
    hf.isPiecewiseAffineOn hf.bijOn.injOn
  have hsub : f '' spliceCylinder ⊆ C.piece.complex.space := by
    rw [C.space_eq]
    exact hcyl.image_subset
  obtain ⟨P, hPspace, hPmap⟩ := C.piece.exists_restrict_of_isPolyhedron hpoly hsub
  have hparam : IsPLHomeomorphOn f C.piece.complex.space P.complex.space := by
    rw [C.space_eq, hPspace]
    exact hf
  let S := P.precomp C.piece.complex C.piece.finite_faces hparam
  have hmap : S.map = chart ∘ f := by
    change P.map ∘ f = chart ∘ f
    rw [hPmap, C.map_eq]
  have himage : C.piece.map '' (f '' spliceCylinder) = (chart ∘ f) '' spliceCylinder := by
    rw [C.map_eq, image_comp]
  have hbij : BijOn (chart ∘ f) C.piece.complex.space ((chart ∘ f) '' spliceCylinder) := by
    rw [← himage, ← hmap]
    exact S.bijOn
  refine ⟨⟨⟨C.piece.complex, C.piece.finite_faces, chart ∘ f, hbij, ?_, ?_, ?_⟩,
    C.space_eq, rfl⟩⟩
  · rw [← hmap]
    exact S.continuousOn
  · intro e he
    have h := S.isPiecewiseAffineOn_chart e he
    change IsPiecewiseAffineOn (e ∘ S.map)
      (C.piece.complex.space ∩ S.map ⁻¹' e.source) at h
    rwa [hmap] at h
  · intro e he
    have h := S.isPiecewiseAffineOn_chart_symm e he
    change IsPiecewiseAffineOn (Function.invFunOn S.map C.piece.complex.space ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' (C.piece.map '' (f '' spliceCylinder))) at h
    rwa [hmap, himage] at h

end DifferentialGeometry.Topology.PiecewiseLinear
