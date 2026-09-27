import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Topology.Embedding.ProductChartCurve

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Neck

variable {F H' M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M]

theorem cylindricalChart.axial_chart (C : cylindricalChart J (M := M)) (z : C.domain) :
    C.axial (C.chart z : M) = (Real.sqrt C.scale)⁻¹ * (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2 := by
  change Subtype.val.extend _ _ (C.chart z : M) = _
  rw [Subtype.val_injective.extend_apply _ _ (C.chart z), C.chart.symm_apply_apply]

theorem cylindricalChart.exists_inward_affine_curve
    {W : Type*} [TopologicalSpace W]
    (C : cylindricalChart J (M := M)) (ι : W → M) (hemb : IsEmbedding ι)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (t τ b r : ℝ)
    (hτ : τ = 1 ∨ τ = -1) (hr : 0 < r)
    (hsegment : ∀ s ∈ Icc 0 r, (p, t + τ * s) ∈ C.domain)
    (himage : ∀ s (hs : s ∈ Icc 0 r),
      (C.chart ⟨(p, t + τ * s), hsegment s hs⟩ : M) ∈ range ι) :
    ∃ γ : ℝ → W, Continuous γ ∧
      (∀ s (hs : s ∈ Icc 0 r),
        ι (γ s) = (C.chart ⟨(p, t + τ * s), hsegment s hs⟩ : M)) ∧
      (∀ᶠ s in 𝓝[≥] (0 : ℝ),
        τ * C.axial (ι (γ s)) + b =
          (τ * (Real.sqrt C.scale)⁻¹ * t + b) + (Real.sqrt C.scale)⁻¹ * s) ∧
      0 < (Real.sqrt C.scale)⁻¹ := by
  obtain ⟨γ, hγ, hγeq⟩ := DifferentialGeometry.Topology.Embedding.exists_curve_of_product_chart_segment
    C.domain C.target C.chart.toHomeomorph ι hemb p t τ r hr hsegment himage
  change ∀ s (hs : s ∈ Icc 0 r),
    ι (γ s) = (C.chart ⟨(p, t + τ * s), hsegment s hs⟩ : M) at hγeq
  refine ⟨γ, hγ, hγeq, ?_, inv_pos.mpr (Real.sqrt_pos.mpr C.scale_pos)⟩
  filter_upwards [Icc_mem_nhdsGE hr] with s hs
  rw [hγeq s hs, C.axial_chart]
  rcases hτ with rfl | rfl <;> dsimp only [Prod.snd] <;> ring

end DifferentialGeometry.Geometry.Neck
