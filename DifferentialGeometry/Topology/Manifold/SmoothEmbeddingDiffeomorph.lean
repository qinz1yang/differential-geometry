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
end DifferentialGeometry.Topology.Manifold
