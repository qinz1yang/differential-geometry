import DifferentialGeometry.Geometry.Comparison.Toponogov.LimitingRadialAngle

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace DifferentialGeometry.Toponogov

variable {X : Type*} [MetricSpace X] {ι : Type*} {z : X}
  {L : ι → ℝ} {gamma : ι → ℝ → X}

theorem dist_le_sqrt_limitingRadialAngle
    (hrad : IsRadialFamily z L gamma) {i j : ι} {s t : ℝ}
    (hs : s ∈ Ioc 0 (L i)) (ht : t ∈ Ioc 0 (L j)) :
    dist (gamma i s) (gamma j t) ≤
      Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * Real.cos (limitingRadialAngle L gamma i j)) := by
  have hsides := radialComparisonAngle_sideInequalities hrad hs ht
  have hangle : radialComparisonAngle gamma i j s t ≤ limitingRadialAngle L gamma i j :=
    le_csSup (positiveRectangleValues_radial_bddAbove L gamma i j) ⟨s, hs, t, ht, rfl⟩
  have hsq := sq_le_cos_of_comparisonAngle_le hs.1 ht.1 hsides.1 hsides.2
    (limitingRadialAngle_mem_Icc gamma (hs.1.trans_le hs.2) (ht.1.trans_le ht.2)).2 hangle
  simpa only [Real.sqrt_sq dist_nonneg] using Real.sqrt_le_sqrt hsq

private theorem tendsto_mul_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun s : ℝ => s * a) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun s : ℝ => s * a) (𝓝 (0 : ℝ)) (𝓝 (0 * a)) :=
      (continuous_id.mul_const a).continuousAt
    simpa only [zero_mul] using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_pos hs ha

theorem tendsto_rescaled_radial_distance
    (hrad : IsRadialFamily z L gamma) {i j : ι}
    (hLi : 0 < L i) (hLj : 0 < L j)
    (hmono : CoordinatewiseNonincreasingOn (L i) (L j) (radialComparisonAngle gamma i j))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun rho : ℝ => dist (gamma i (rho * a)) (gamma j (rho * b)) / rho)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos (limitingRadialAngle L gamma i j)))) := by
  have harg : Tendsto (fun rho : ℝ => (rho * a, rho * b))
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) :=
    (tendsto_mul_nhdsGT_zero ha).prodMk (tendsto_mul_nhdsGT_zero hb)
  have hangle := (tendsto_limitingRadialAngle gamma hLi hLj hmono).comp harg
  have hmodel : Tendsto (fun rho : ℝ => Real.sqrt
      (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos (radialComparisonAngle gamma i j (rho * a) (rho * b))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos (limitingRadialAngle L gamma i j)))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub ((Real.continuous_cos.continuousAt.tendsto.comp hangle).const_mul (2 * a * b)))
  apply hmodel.congr'
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_mul_nhdsGT_zero ha).eventually (Ioc_mem_nhdsGT hLi),
    (tendsto_mul_nhdsGT_zero hb).eventually (Ioc_mem_nhdsGT hLj)] with rho hrho hsa htb
  have hr : 0 < rho := hrho
  have hsides := radialComparisonAngle_sideInequalities hrad hsa htb
  have hc := cos_comparisonAngle hsa.1 htb.1 hsides.1 hsides.2
  change Real.cos (radialComparisonAngle gamma i j (rho * a) (rho * b)) =
    ((rho * a) ^ 2 + (rho * b) ^ 2 - dist (gamma i (rho * a)) (gamma j (rho * b)) ^ 2) /
      (2 * (rho * a) * (rho * b)) at hc
  have heq : a ^ 2 + b ^ 2 - 2 * a * b *
      Real.cos (radialComparisonAngle gamma i j (rho * a) (rho * b)) =
      (dist (gamma i (rho * a)) (gamma j (rho * b)) / rho) ^ 2 := by
    rw [hc]
    field_simp [ha.ne', hb.ne', hr.ne']
    ring
  rw [heq, Real.sqrt_sq (div_nonneg dist_nonneg hr.le)]

end DifferentialGeometry.Toponogov
