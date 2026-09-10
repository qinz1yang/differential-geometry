import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Topology.Compactness.OpensProductChartBand
import Mathlib.Topology.Algebra.GroupWithZero

noncomputable section
open Set
open scoped Manifold ContDiff

namespace Poincare.Geometry.Neck

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem cylindricalChart.isCompact_affine_axial_band
    (C : cylindricalChart J (M := M)) (U : Set C.domain)
    (τ b l r : ℝ) (hτ : τ ≠ 0)
    (hband : (univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ
      ((fun t : ℝ ↦ τ * (Real.sqrt C.scale)⁻¹ * t + b) ⁻¹' Icc l r) ⊆ Subtype.val '' U) :
    IsCompact (C.region U ∩ (fun x ↦ τ * C.axial x + b) ⁻¹' Icc l r) := by
  have hα : τ * (Real.sqrt C.scale)⁻¹ ≠ 0 :=
    mul_ne_zero hτ (inv_ne_zero (Real.sqrt_pos.mpr C.scale_pos).ne')
  let χ := (Homeomorph.mulLeft₀ (τ * (Real.sqrt C.scale)⁻¹) hα).trans (Homeomorph.addRight b)
  apply Poincare.Topology.Compactness.isCompact_coordinate_band_of_opens_product_chart
    C.domain C.target C.chart.toHomeomorph U χ (fun x ↦ τ * C.axial x + b) _ l r hband
  intro p
  change τ * (Subtype.val.extend
    (fun y : C.target ↦ (Real.sqrt C.scale)⁻¹ *
      (C.chart.symm y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2)
    (fun _ ↦ 0) (C.chart p : M)) + b = τ * (Real.sqrt C.scale)⁻¹ * (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2 + b
  rw [Subtype.val_injective.extend_apply, C.chart.symm_apply_apply]
  ring

theorem cylindricalChart.closure_preimage_affine_axial_band_subset_region
    [T2Space M] (C : cylindricalChart J (M := M)) (U : Set C.domain)
    (τ b l r : ℝ) (hτ : τ ≠ 0)
    (hband : (univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ
      ((fun t : ℝ ↦ τ * (Real.sqrt C.scale)⁻¹ * t + b) ⁻¹' Icc l r) ⊆ Subtype.val '' U)
    {W : Type*} [TopologicalSpace W] (ι : W → M) (hι : Continuous ι) :
    closure (ι ⁻¹' C.region U ∩ (fun w ↦ τ * C.axial (ι w) + b) ⁻¹' Icc l r) ⊆
      ι ⁻¹' C.region U := by
  have hclosed := (C.isCompact_affine_axial_band U τ b l r hτ hband).isClosed.preimage hι
  change IsClosed (ι ⁻¹' C.region U ∩ (fun w ↦ τ * C.axial (ι w) + b) ⁻¹' Icc l r) at hclosed
  rw [hclosed.closure_eq]
  exact inter_subset_left

end Poincare.Geometry.Neck
