import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckImageRadius

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Geometry.Curvature Surgery.Topology

universe u

theorem exists_uniform_spatial_neck_closed_collar_radius {eps r : ℝ}
    (heps : 0 < eps) (hr : 0 ≤ r) (hfit : r < eps⁻¹) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        (g : SmoothRiemannianMetric I3 M) (p : M) (nk : SpatialNeck g eps p),
        ∀ x ∈ nk.map '' (univ ×ˢ Icc (-r) r),
          riemannianEDistOf (scaleMetric (metricScalarAt g p) nk.Q_pos g) p x ≤
            ENNReal.ofReal B := by
  let L := (r + eps⁻¹) / 2
  have hL : 0 < L := by dsimp only [L]; positivity
  have hrL : r < L := by dsimp only [L]; linarith
  have hLeps : L < eps⁻¹ := by dsimp only [L]; linarith
  have hepsL : eps < L⁻¹ := (lt_inv_comm₀ heps hL).mpr hLeps
  obtain ⟨B, hB, hbound⟩ := exists_uniform_spatial_neck_image_radius.{u} heps hepsL
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ g p nk x hx
  obtain ⟨z, hz, rfl⟩ := hx
  apply hbound M g p nk z
  rw [inv_inv]
  exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩

theorem eventually_spatial_neck_collar_subset_of_tendsto_endpoint
    {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M)
    (hintrinsic : ∀ x y : M, riemannianEDistOf g x y = ENNReal.ofReal (dist x y))
    {eps r delta : ℝ} (hr : 0 ≤ r) (hfit : r < eps⁻¹)
    (U : Set M) (endpoint : UniformSpace.Completion M) (hdelta : 0 < delta)
    (hcapture : {x : M | dist (x : UniformSpace.Completion M) endpoint < delta} ⊆ U)
    (p : ℕ → M) (t : ℕ → ℝ) (neck : ∀ n, SpatialNeck g eps (p n))
    (ht : Tendsto t atTop (𝓝 0)) (htpos : ∀ n, 0 < t n)
    (hradial : ∀ n, dist (p n : UniformSpace.Completion M) endpoint = t n)
    (hscale : ∀ n, 1 ≤ metricScalarAt g (p n) * (t n)^2) :
    ∀ᶠ n in atTop, (neck n).map '' (univ ×ˢ Icc (-r) r) ⊆ U := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_spatial_neck_closed_collar_radius.{u}
    (neck 0).eps_pos hr hfit
  have hlimit : Tendsto (fun n => (B + 1) * t n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul (B + 1)
  filter_upwards [hlimit.eventually_lt_const hdelta] with n hn
  intro x hx
  apply hcapture
  have hroot : 0 < Real.sqrt (metricScalarAt g (p n)) := Real.sqrt_pos.mpr (neck n).Q_pos
  have hrootScale : 1 ≤ Real.sqrt (metricScalarAt g (p n)) * t n := by
    nlinarith [hscale n, Real.sq_sqrt (neck n).Q_pos.le,
      mul_pos hroot (htpos n)]
  have hb := hbound M g (p n) (neck n) x hx
  rw [edistOf_scale, hintrinsic, ← ENNReal.ofReal_mul hroot.le] at hb
  have hdist := (ENNReal.ofReal_le_ofReal_iff hB.le).mp hb
  have hxbound : dist (p n) x ≤ B * t n := by
    have hm := mul_le_mul_of_nonneg_right hdist (htpos n).le
    have hh := mul_le_mul_of_nonneg_right hrootScale (dist_nonneg (x := p n) (y := x))
    nlinarith only [hm, hh]
  have htri := dist_triangle (x : UniformSpace.Completion M) (p n) endpoint
  rw [UniformSpace.Completion.dist_eq, hradial, dist_comm x (p n)] at htri
  change dist (x : UniformSpace.Completion M) endpoint < delta
  have hbnd : dist (x : UniformSpace.Completion M) endpoint ≤ (B + 1) * t n := by
    nlinarith only [htri, hxbound]
  exact hbnd.trans_lt hn

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
