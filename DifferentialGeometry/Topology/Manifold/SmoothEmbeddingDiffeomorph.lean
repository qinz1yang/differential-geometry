import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold IsManifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F H H' M N P : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [TopologicalSpace H] [TopologicalSpace H']
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
variable [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace H' N]
variable [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J ∞ P]

theorem isSmoothEmbedding_diffeomorph_comp (f : M → N) (hf : IsSmoothEmbedding I J ∞ f)
    (D : N ≃ₘ⟮J, J⟯ P) : IsSmoothEmbedding I J ∞ (D ∘ f) := by
  refine ⟨?_, D.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩
  obtain ⟨C, hC, hC', hImm⟩ := hf.isImmersion
  let := hC
  let := hC'
  refine ⟨C, hC, hC', ?_⟩
  intro x
  let h := hImm x
  let c := D.symm.toHomeomorph.toOpenPartialHomeomorph.trans h.codChart
  have hc : c ∈ maximalAtlas J ∞ P := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        D.symm.contMDiff.contMDiffOn (fun _ hy => hy.2)
    · exact D.contMDiff.comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono (fun _ hy => hy.1))
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    ((D.contMDiff.comp hf.contMDiff).continuous.continuousAt) h.equiv h.domChart c
    h.mem_domChart_source (by exact ⟨mem_univ _, by simpa using h.mem_codChart_source⟩)
    h.domChart_mem_maximalAtlas hc
  intro z hz
  change J (h.codChart (D.symm (D (f ((h.domChart.extend I).symm z))))) = h.equiv (z, 0)
  rw [D.symm_apply_apply]
  exact h.writtenInCharts hz

theorem isSmoothEmbedding_diffeomorph_precomp
    {E F H H' M N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
    (f : M → N) (hf : IsSmoothEmbedding I J ∞ f) (D : P ≃ₘ⟮I, I⟯ M) :
    IsSmoothEmbedding I J ∞ (f ∘ D) := by
  refine ⟨?_, hf.isEmbedding.comp D.toHomeomorph.isEmbedding⟩
  obtain ⟨C, hC, hC', hImm⟩ := hf.isImmersion
  let := hC
  let := hC'
  refine ⟨C, hC, hC', ?_⟩
  intro x
  let h := hImm (D x)
  let c := D.toHomeomorph.toOpenPartialHomeomorph.trans h.domChart
  have hc : c ∈ maximalAtlas I ∞ P := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
        D.contMDiff.contMDiffOn (fun _ hy => hy.2)
    · exact D.symm.contMDiff.comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mono
          (fun _ hy => hy.1))
  have hxc : x ∈ c.source := by
    refine ⟨mem_univ _, ?_⟩
    simpa using h.mem_domChart_source
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    ((hf.contMDiff.comp D.contMDiff).continuous.continuousAt) h.equiv c h.codChart
    hxc h.mem_codChart_source hc h.codChart_mem_maximalAtlas
  intro z hz
  change J (h.codChart (f (D ((c.extend I).symm z)))) = h.equiv (z, 0)
  have hy : (c.extend I).symm z ∈ c.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (c.extend I).map_target hz
  have hcval : c ((c.extend I).symm z) = h.domChart (D ((c.extend I).symm z)) := rfl
  have hval : (h.domChart.extend I) (D ((c.extend I).symm z)) = z := by
    have h2 : (c.extend I) ((c.extend I).symm z) = z := (c.extend I).right_inv hz
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply] at h2
    rwa [hcval] at h2
  have hdom : D ((c.extend I).symm z) ∈ h.domChart.source := by
    have h := hy.2
    simp only [c, Set.mem_preimage, OpenPartialHomeomorph.symm_symm,
      Homeomorph.toOpenPartialHomeomorph_apply, Diffeomorph.coe_toHomeomorph] at h
    exact h
  have hzt : z ∈ (h.domChart.extend I).target := by
    rw [OpenPartialHomeomorph.extend_target_eq_image_source]
    exact ⟨D ((c.extend I).symm z), hdom, hval⟩
  have hsymm : D ((c.extend I).symm z) = (h.domChart.extend I).symm z :=
    (PartialEquiv.eq_symm_apply _ (by rwa [OpenPartialHomeomorph.extend_source]) hzt).mpr hval
  rw [hsymm]
  exact h.writtenInCharts hzt

end DifferentialGeometry.Topology.Manifold
