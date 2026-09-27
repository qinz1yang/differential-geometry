import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold IsManifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F H H' M N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [TopologicalSpace H] [TopologicalSpace H']
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
variable [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem isSmoothEmbedding_intoOpen (U : Opens N) (f : M → U)
    (hf : IsSmoothEmbedding I J ∞ (Subtype.val ∘ f)) : IsSmoothEmbedding I J ∞ f := by
  refine ⟨?_, hf.isEmbedding.codRestrict U (fun x => (f x).property)⟩
  obtain ⟨C, hC, hC', hImm⟩ := hf.isImmersion
  let := hC
  let := hC'
  refine ⟨C, hC, hC', ?_⟩
  intro x
  let h := hImm x
  let c := h.codChart.subtypeRestr (show Nonempty U from ⟨f x⟩)
  have hc : c ∈ maximalAtlas J ∞ U := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn J J ∞ (h.codChart ∘ (Subtype.val : U → N)) c.source
      have hval : ContMDiff J J ∞ (Subtype.val : U → N) := contMDiff_subtype_val
      exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        hval.contMDiffOn
        (fun y hy => by simpa only [c, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hy)
    · intro z hz
      have hOld : ContMDiffAt J J ∞ h.codChart.symm z :=
        (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).contMDiffAt
          (h.codChart.open_target.mem_nhds (h.codChart.subtypeRestr_target_subset ⟨f x⟩ hz))
      have hVal : ContMDiffAt J J ∞ (Subtype.val ∘ c.symm) z := by
        apply hOld.congr_of_eventuallyEq
        filter_upwards [c.open_target.mem_nhds hz] with y hy
        exact h.codChart.subtypeRestr_symm_apply ⟨f x⟩ hy
      exact ((ContMDiffAt.subtypeVal_comp_iff U c.symm z).mp hVal).contMDiffWithinAt
  have hfc : ContinuousAt f x :=
    _root_.Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hf.contMDiff.continuous.continuousAt
  have hfx : f x ∈ c.source := by
    simpa only [c, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage, Function.comp_apply]
      using h.mem_codChart_source
  apply IsImmersionAtOfComplement.mk_of_continuousAt (f := f) (x := x) hfc
    h.equiv h.domChart c h.mem_domChart_source hfx h.domChart_mem_maximalAtlas hc
  intro z hz
  exact h.writtenInCharts hz
end DifferentialGeometry.Topology.Manifold
