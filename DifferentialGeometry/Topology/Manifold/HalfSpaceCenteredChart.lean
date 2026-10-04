import DifferentialGeometry.Topology.Manifold.ModelImmersion
import DifferentialGeometry.Topology.Manifold.ProductSectionCenteredChart
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace EuclideanHalfSpace

private def tangentialShift (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1)))
    (hv : v 0 = 0) (x : EuclideanHalfSpace (n + 1)) : EuclideanHalfSpace (n + 1) :=
  ⟨x.val + v, by change 0 ≤ x.val 0 + v 0; rw [hv, add_zero]; exact x.property⟩

private theorem tangentialShift_contMDiff (n : ℕ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v 0 = 0) :
    ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ (tangentialShift n v hv) := by
  apply (ContMDiff.iff_comp_isImmersion ((𝓡∂ (n + 1)).isImmersion_coe ∞)).mpr
  refine ⟨(continuous_subtype_val.add continuous_const).subtype_mk _, ?_⟩
  change ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
    (fun x : EuclideanHalfSpace (n + 1) => x.val + v)
  exact (𝓡∂ (n + 1)).contMDiff.add contMDiff_const

def tangentialShiftDiffeomorph (n : ℕ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v 0 = 0) :
    EuclideanHalfSpace (n + 1) ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯
      EuclideanHalfSpace (n + 1) where
  toFun := tangentialShift n v hv
  invFun := tangentialShift n (-v) (by change -(v 0) = 0; rw [hv, neg_zero])
  left_inv x := by
    apply Subtype.ext
    change (x.val + v) + -v = x.val
    exact add_neg_cancel_right x.val v
  right_inv x := by
    apply Subtype.ext
    change (x.val + -v) + v = x.val
    simp only [add_assoc, neg_add_cancel, add_zero]
  contMDiff_toFun := tangentialShift_contMDiff n v hv
  contMDiff_invFun := tangentialShift_contMDiff n (-v)
    (by change -(v 0) = 0; rw [hv, neg_zero])

theorem tangentialShiftDiffeomorph_apply (n : ℕ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v 0 = 0)
    (x : EuclideanHalfSpace (n + 1)) :
    (tangentialShiftDiffeomorph n v hv x).val = x.val + v := rfl

end EuclideanHalfSpace

namespace Manifold

variable {n : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) N] [IsManifold (𝓡∂ (n + 1)) ∞ N]


theorem exists_centered_halfSpace_chart (y : N)
    (hy : (𝓡∂ (n + 1)).IsBoundaryPoint y) :
    ∃ c : OpenPartialHomeomorph N (EuclideanHalfSpace (n + 1)),
      y ∈ c.source ∧ c ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) ∞ N ∧
        (𝓡∂ (n + 1)) (c y) = 0 := by
  let c := chartAt (EuclideanHalfSpace (n + 1)) y
  have hzero : (c y).val 0 = 0 := by
    change extChartAt (𝓡∂ (n + 1)) y y ∈ frontier (range (𝓡∂ (n + 1))) at hy
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hy
    exact hy.symm
  let v := -((c y).val)
  have hv : v 0 = 0 := by change -((c y).val 0) = 0; rw [hzero, neg_zero]
  let D := EuclideanHalfSpace.tangentialShiftDiffeomorph n v hv
  let d := c.trans D.toHomeomorph.toOpenPartialHomeomorph
  have hs : d.source = c.source := by simp [d]
  have hc : c ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) ∞ N :=
    IsManifold.chart_mem_maximalAtlas y
  refine ⟨d, hs.symm ▸ mem_chart_source _ y, ?_, ?_⟩
  · apply d.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ (D ∘ c) d.source
      rw [hs]
      exact D.contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hc)
    · change ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞
        (c.symm ∘ D.symm) d.target
      exact (contMDiffOn_symm_of_mem_maximalAtlas hc).comp
        D.symm.contMDiff.contMDiffOn (fun _ hz => hz.2)
  · change (c y).val + -((c y).val) = 0
    exact add_neg_cancel _



theorem isSmoothEmbedding_prodMk_boundary_point
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
    (y : N) (hy : (𝓡∂ (n + 1)).IsBoundaryPoint y) :
    IsSmoothEmbedding I (I.prod (𝓡∂ (n + 1))) ∞ (fun x : M => (x, y)) := by
  obtain ⟨c, hcy, hc, hz⟩ := exists_centered_halfSpace_chart y hy
  exact isSmoothEmbedding_prodMk_const_of_centered_chart y c hcy hc hz



theorem isSmoothEmbedding_const_prodMk_boundary_point
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
    (y : N) (hy : (𝓡∂ (n + 1)).IsBoundaryPoint y) :
    IsSmoothEmbedding I ((𝓡∂ (n + 1)).prod I) ∞ (fun x : M => (y, x)) := by
  obtain ⟨c, hcy, hc, hz⟩ := exists_centered_halfSpace_chart y hy
  exact isSmoothEmbedding_const_prodMk_of_centered_chart y c hcy hc hz

end Manifold
