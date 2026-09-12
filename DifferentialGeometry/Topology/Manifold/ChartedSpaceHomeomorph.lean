import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open OpenPartialHomeomorph

namespace DifferentialGeometry.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {n : ℕ∞ω}
variable {M M' : Type*} [TopologicalSpace M] [TopologicalSpace M'] [ChartedSpace H M]

theorem atlas_homeomorphChartedSpace (f : M ≃ₜ M') :
    @atlas H _ M' _ (f.chartedSpace) =
      Set.range (@chartAt H _ M' _ (f.chartedSpace)) := rfl

theorem chartAt_homeomorphChartedSpace (f : M ≃ₜ M') (q : M') :
    @chartAt H _ M' _ (f.chartedSpace) q =
      (f.isLocalHomeomorph.localInverseAt (f.surjective.hasRightInverse.choose q)).trans
        (chartAt H (f.surjective.hasRightInverse.choose q)) := rfl

theorem isManifold_homeomorphChartedSpace (f : M ≃ₜ M') [IsManifold I n M] :
    @IsManifold 𝕜 _ E _ _ H _ I n M' _ (f.chartedSpace) := by
  refine @isManifold_of_contDiffOn 𝕜 _ E _ _ H _ I n M' _ (f.chartedSpace) ?_
  intro e e' he he'
  rw [atlas_homeomorphChartedSpace (H := H) f] at he he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  rw [chartAt_homeomorphChartedSpace (H := H) f q, chartAt_homeomorphChartedSpace (H := H) f q']
  set g := f.surjective.hasRightInverse.choose with hgdef
  set A := f.isLocalHomeomorph.localInverseAt (g q) with hA
  set A' := f.isLocalHomeomorph.localInverseAt (g q') with hA'
  set c := chartAt H (g q) with hc
  set c' := chartAt H (g q') with hc'
  have hAs : ⇑(A.symm) = (f : M → M') := by
    rw [hA]; exact IsLocalHomeomorph.localInverseAt_symm f.isLocalHomeomorph (g q)
  have hA's : ⇑(A'.symm) = (f : M → M') := by
    rw [hA']; exact IsLocalHomeomorph.localInverseAt_symm f.isLocalHomeomorph (g q')
  have hB : ∀ y, y ∈ (A.symm ≫ₕ A').source → A' (A.symm y) = y := by
    intro y hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    have hy2 : f y ∈ A'.source := by rw [← hAs]; exact hy.2
    rw [hAs]
    refine f.injective ?_
    have h := A'.left_inv hy2
    rwa [hA's] at h
  have hsrc : ∀ w, w ∈ ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')).source →
      w ∈ c.symm.source ∧ c.symm w ∈ A.symm.source ∧
        A.symm (c.symm w) ∈ A'.source ∧ A' (A.symm (c.symm w)) ∈ c'.source := by
    intro w hw
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] at hw
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hw
    simp only [coe_trans, Function.comp_apply, Set.mem_inter_iff, Set.mem_preimage] at hw
    exact ⟨hw.1.1, hw.1.2, hw.2.1, hw.2.2⟩
  have hsub : ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')).source ⊆ (c.symm ≫ₕ c').source := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hsrc w hw
    have hmem : c.symm w ∈ (A.symm ≫ₕ A').source := by
      rw [OpenPartialHomeomorph.trans_source]; exact ⟨h2, h3⟩
    have hb := hB (c.symm w) hmem
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨h1, by rw [← hb]; exact h4⟩
  have heq : ∀ w ∈ ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')).source,
      ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')) w = (c.symm ≫ₕ c') w := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hsrc w hw
    have hmem : c.symm w ∈ (A.symm ≫ₕ A').source := by
      rw [OpenPartialHomeomorph.trans_source]; exact ⟨h2, h3⟩
    have hb := hB (c.symm w) hmem
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    simp only [OpenPartialHomeomorph.trans_apply]
    rw [hb]
  have hY : (c.symm ≫ₕ c') ∈ contDiffGroupoid n I :=
    StructureGroupoid.compatible (contDiffGroupoid n I)
      (chart_mem_atlas H (g q)) (chart_mem_atlas H (g q'))
  refine (mem_groupoid_of_pregroupoid.mp hY).1.congr_mono (fun z hz => ?_) (fun z hz => ?_)
  · simp only [Function.comp_apply]
    exact congrArg (⇑I) (heq _ hz.1)
  · exact ⟨hsub hz.1, hz.2⟩

end DifferentialGeometry.Manifold

end
