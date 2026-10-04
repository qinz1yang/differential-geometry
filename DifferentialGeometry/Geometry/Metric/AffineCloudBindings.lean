import DifferentialGeometry.Geometry.Metric.AffinePlaneCoherence

set_option autoImplicit false
noncomputable section
open Set Metric
namespace GC.MetricGeometry

theorem normal_coherence_of_max_radius_cloud_tests
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P Q : Submodule ℝ H) [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q]
    (hdim : Module.finrank ℝ P = Module.finrank ℝ Q)
    (T : Set H) (o i : H) (hi : i ∈ T)
    (r₀ rᵢ B L δ : ℝ) (hr₀ : 0 < r₀) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hlower : r₀ / B ≤ rᵢ) (hupper : rᵢ ≤ B * r₀)
    (hcenter : dist i o ≤ L * max r₀ rᵢ) (hδ : 0 < δ)
    (hδsmall : δ < min (1 / (4 * B))
      (min (1 / (2 * (L * B + 3))) (1 / (4 * (B + 1)))))
    (hcloud₀ : hausdorffEDist (T ∩ ball o (r₀ / δ))
      ((AffineSubspace.mk' o P : Set H) ∩ ball o (r₀ / δ)) ≤ ENNReal.ofReal (δ * r₀))
    (hcloudᵢ : hausdorffEDist (T ∩ ball i (rᵢ / δ))
      ((AffineSubspace.mk' i Q : Set H) ∩ ball i (rᵢ / δ)) ≤ ENNReal.ofReal (δ * rᵢ)) :
    ‖Pᗮ.starProjection (i - o)‖ ≤ δ * r₀ ∧
      ‖Pᗮ.starProjection - Qᗮ.starProjection‖ ≤ 6 * (B + 1) * δ := by
  have hmax : max r₀ rᵢ ≤ B * r₀ := max_le (by nlinarith) hupper
  have hc : ‖i - o‖ ≤ (L * B) * r₀ := by
    rw [← dist_eq_norm]
    have hh := hcenter.trans (mul_le_mul_of_nonneg_left hmax (by linarith : 0 ≤ L))
    nlinarith
  have hs := lt_of_lt_of_le hδsmall (min_le_right _ _)
  have hs' := lt_of_lt_of_le hs (min_le_right _ _)
  have ht := lt_of_lt_of_le hs (min_le_left _ _)
  have hb : δ * (2 * (L * B + 3)) < 1 :=
    (lt_div_iff₀ (by positivity)).mp ht
  have hi' : δ * (L * B + 2) < 1 := by nlinarith
  exact normal_offset_and_projection_gap_le_of_large_affine_hausdorffEDist
    P Q hdim T o i hi hr₀ hB hlower hupper hc hδ hs' hi' hcloud₀ hcloudᵢ

end GC.MetricGeometry
