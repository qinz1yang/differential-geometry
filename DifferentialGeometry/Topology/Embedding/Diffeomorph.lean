import Mathlib.Geometry.Manifold.SmoothEmbedding

open scoped ContDiff

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace N'] [ChartedSpace G N']
  {n : ℕ∞ω} {f : M → N}

lemma IsImmersion.diffeomorph_comp [IsManifold J n N']
    (hf : IsImmersion I J n f) (Φ : Diffeomorph J J N N' n) :
    IsImmersion I J n (Φ ∘ f) := by
  classical
  obtain ⟨F, hFadd, hFspace, hF⟩ := hf
  let _ := hFadd
  let _ := hFspace
  refine ⟨F, hFadd, hFspace, ?_⟩
  intro x
  let h := hF x
  let ψ := Φ.symm.toHomeomorph.toOpenPartialHomeomorph.trans h.codChart
  have hψsource : ψ.source = Φ.symm ⁻¹' h.codChart.source := by
    simp [ψ]
  have hψtarget : ψ.target = h.codChart.target := by
    simp [ψ]
  have hψ : ψ ∈ IsManifold.maximalAtlas J n N' := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn J J n (h.codChart ∘ Φ.symm) ψ.source
      apply (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        Φ.symm.contMDiff.contMDiffOn
      intro y hy
      exact (hψsource ▸ hy)
    · change ContMDiffOn J J n (Φ ∘ h.codChart.symm) ψ.target
      rw [hψtarget]
      exact Φ.contMDiff.comp_contMDiffOn
        (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas)
  apply IsImmersionAtOfComplement.mk_of_charts h.equiv h.domChart ψ
    h.mem_domChart_source
  · rw [hψsource]
    simpa only [Set.mem_preimage, Function.comp_apply, Φ.symm_apply_apply] using
      h.mem_codChart_source
  · exact h.domChart_mem_maximalAtlas
  · exact hψ
  · intro y hy
    rw [Set.mem_preimage, hψsource]
    simpa only [Set.mem_preimage, Function.comp_apply, Φ.symm_apply_apply] using
      h.source_subset_preimage_source hy
  · intro y hy
    change J (h.codChart (Φ.symm (Φ (f ((h.domChart.extend I).symm y))))) =
      h.equiv (y, 0)
    rw [Φ.symm_apply_apply]
    exact h.writtenInCharts hy

lemma IsSmoothEmbedding.diffeomorph_comp [IsManifold J n N']
    (hf : IsSmoothEmbedding I J n f) (Φ : Diffeomorph J J N N' n) :
    IsSmoothEmbedding I J n (Φ ∘ f) :=
  ⟨hf.isImmersion.diffeomorph_comp Φ,
    Φ.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩

lemma _root_.Diffeomorph.isSmoothEmbedding [IsManifold J n N] [IsManifold J n N']
    (Φ : Diffeomorph J J N N' n) : IsSmoothEmbedding J J n Φ := by
  simpa only [Function.comp_id] using
    (IsSmoothEmbedding.id (I := J) (M := N) (n := n)).diffeomorph_comp Φ

end Manifold
