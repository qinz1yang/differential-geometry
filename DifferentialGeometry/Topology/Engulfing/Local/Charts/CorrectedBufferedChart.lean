import DifferentialGeometry.Topology.Engulfing.Local.Charts.ChartCorrection

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology

variable {M : Type*} [TopologicalSpace M] {n : ℕ}

noncomputable def BufferedChart.corrected (b : BufferedChart M n)
    (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {r R η : ℝ} (hr : 0 < r) (hrR : r < R)
    (hH : ∀ y, ‖H y - y‖ < η) (hR : R + η ≤ b.outerRadius) : BufferedChart M n where
  chart := correctedAffineChart b.chart H
  center := b.center
  innerRadius := r
  outerRadius := R
  inner_pos := hr
  radii_lt := hrR
  outer_subset := correctedAffineChart_closedBall_subset_target b.chart H b.center hH hR b.outer_subset

theorem BufferedChart.corrected_core_subset (b : BufferedChart M n)
    (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {r R η : ℝ} (hr : 0 < r) (hrR : r < R)
    (hH : ∀ y, ‖H y - y‖ < η) (hR : R + η ≤ b.outerRadius)
    (hinner : r + η ≤ b.innerRadius) :
    (b.corrected H hr hrR hH hR).core ⊆ b.core :=
  correctedAffineChart_core_subset b.chart H b.center hH hinner

theorem BufferedChart.corrected_obstacle_contains (b : BufferedChart M n)
    (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {r R η : ℝ} (hr : 0 < r) (hrR : r < R)
    (hH : ∀ y, ‖H y - y‖ < η) (hR : R + η ≤ b.outerRadius)
    (hinner : r + η ≤ b.innerRadius) {X : Set M}
    {T O : Set (EuclideanSpace ℝ (Fin n))}
    (hX : b.chart '' (X ∩ b.core) ⊆ T) (hO : H.symm '' T ⊆ O) :
    (b.corrected H hr hrR hH hR).chart ''
      (X ∩ (b.corrected H hr hrR hH hR).core) ⊆ O := by
  rintro _ ⟨x, hx, rfl⟩
  apply hO
  exact mem_image_of_mem H.symm (hX ⟨x, ⟨hx.1,
    b.corrected_core_subset H hr hrR hH hR hinner hx.2⟩, rfl⟩)

end DifferentialGeometry.Topology.Engulfing
