import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace Manifold

theorem IsImmersionAtOfComplement.extend_writtenInCharts_self {E H M N F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H N]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {I : ModelWithCorners ℝ E H} {f : M → N} {x : M}
    (h : IsImmersionAtOfComplement F I I ∞ f x) {y : E}
    (hy : y ∈ (h.domChart.extend I).target) :
    I (h.codChart (f ((h.domChart.extend I).symm y))) = h.equiv (y, 0) := by
  have hw := h.writtenInCharts hy
  simpa only [OpenPartialHomeomorph.extend_coe, Function.comp_apply] using hw

theorem IsImmersionAtOfComplement.extend_apply_self {E H M N F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H N]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {I : ModelWithCorners ℝ E H} {f : M → N} {x : M}
    (h : IsImmersionAtOfComplement F I I ∞ f x) :
    I (h.codChart (f x)) = h.equiv (I (h.domChart x), 0) := by
  have hx : (h.domChart.extend I) x ∈ (h.domChart.extend I).target := by
    rw [OpenPartialHomeomorph.extend_target_eq_image_source]
    exact ⟨x, h.mem_domChart_source, rfl⟩
  have hleft : (h.domChart.extend I).symm ((h.domChart.extend I) x) = x :=
    (h.domChart.extend I).left_inv (by
      rw [OpenPartialHomeomorph.extend_source]
      exact h.mem_domChart_source)
  have hw := h.extend_writtenInCharts_self hx
  rw [hleft] at hw
  simpa only [OpenPartialHomeomorph.extend_coe, Function.comp_apply] using hw

end Manifold
