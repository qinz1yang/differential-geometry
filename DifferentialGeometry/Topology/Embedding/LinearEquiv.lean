import Mathlib.Geometry.Manifold.SmoothEmbedding

open scoped ContDiff

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {f : M → E'}

lemma IsImmersion.continuousLinearEquiv_comp
    (hf : IsImmersion I 𝓘(𝕜, E') n f) (e : E' ≃L[𝕜] E'') :
    IsImmersion I 𝓘(𝕜, E'') n (e ∘ f) := by
  classical
  obtain ⟨F, hFadd, hFspace, hF⟩ := hf
  let _ := hFadd
  let _ := hFspace
  apply IsImmersionOfComplement.isImmersion (F := F)
  intro x
  let h := hF x
  let ψ := e.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (h.codChart.trans e.toHomeomorph.toOpenPartialHomeomorph)
  have hψsource : ψ.source = e.symm ⁻¹' h.codChart.source := by simp [ψ]
  have hψtarget : ψ.target = e.symm ⁻¹' h.codChart.target := by simp [ψ]
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E'') n E'' := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn 𝓘(𝕜, E'') 𝓘(𝕜, E'') n
        (e ∘ h.codChart ∘ e.symm) ψ.source
      apply e.contDiff.contMDiff.comp_contMDiffOn
      apply (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        e.symm.contDiff.contMDiff.contMDiffOn
      intro y hy
      exact hψsource ▸ hy
    · change ContMDiffOn 𝓘(𝕜, E'') 𝓘(𝕜, E'') n
        (e ∘ h.codChart.symm ∘ e.symm) ψ.target
      apply e.contDiff.contMDiff.comp_contMDiffOn
      apply (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        e.symm.contDiff.contMDiff.contMDiffOn
      intro y hy
      exact hψtarget ▸ hy
  apply IsImmersionAtOfComplement.mk_of_charts (h.equiv.trans e) h.domChart ψ
    h.mem_domChart_source
  · rw [hψsource]
    simpa only [Set.mem_preimage, Function.comp_apply, e.symm_apply_apply] using
      h.mem_codChart_source
  · exact h.domChart_mem_maximalAtlas
  · exact hψ
  · intro y hy
    rw [Set.mem_preimage, hψsource]
    simpa only [Set.mem_preimage, Function.comp_apply, e.symm_apply_apply] using
      h.source_subset_preimage_source hy
  · intro y hy
    change e (h.codChart (e.symm (e (f ((h.domChart.extend I).symm y))))) =
      e (h.equiv (y, 0))
    rw [e.symm_apply_apply]
    exact congrArg e (h.writtenInCharts hy)

lemma IsSmoothEmbedding.continuousLinearEquiv_comp
    (hf : IsSmoothEmbedding I 𝓘(𝕜, E') n f) (e : E' ≃L[𝕜] E'') :
    IsSmoothEmbedding I 𝓘(𝕜, E'') n (e ∘ f) :=
  ⟨hf.isImmersion.continuousLinearEquiv_comp e,
    e.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩

end Manifold
