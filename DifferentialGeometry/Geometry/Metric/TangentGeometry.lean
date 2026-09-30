import DifferentialGeometry.Geometry.Metric.IntrinsicTangentBlowup
import DifferentialGeometry.Geometry.Comparison.RescaledLocalComparison
import DifferentialGeometry.Geometry.Metric.Approximation.ComparisonLimit
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleLength
import DifferentialGeometry.Geometry.Metric.EuclideanConeProper

set_option autoImplicit false

open Set Metric Filter Topology

namespace Metric

open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov

theorem tangent_geometry_of_intrinsic_8_buffer
    {X : Type*} [m : MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {q : X} {R : ℝ} (hR : 0 < R)
    (hq : dist q p < R / 2) [LocallyCompactSpace (ball p (8 * R))]
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
      (by change dist q p < 8 * R; linarith)
    CompactSpace (SpaceOfDirections q) →
      fourPointComparison 0 (univ : Set (TangentCone q)) ∧
      ∀ a b : TangentCone q, ∃ f : Icc (0 : ℝ) 1 → TangentCone q,
        Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist q p < 8 * R; linarith)
  intro hcompact
  let : CompactSpace (SpaceOfDirections q) := hcompact
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht : ∀ n, 0 < t n := by intro n; dsimp [t]; positivity
  have hzero : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv := pointedGHConverges_tangent_of_intrinsic_8_buffer hcurves p hR hq hlocal
    t ht hzero hcompact
  have hq8 : q ∈ ball p (8 * R) := by change dist q p < 8 * R; linarith
  obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ :=
    (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
      (by positivity : 0 < 8 * R) ⟨q, hq8⟩).mp (hlocal ⟨q, hq8⟩)
  constructor
  · apply @PointedGHConverges.fourPointComparison_zero_of_eventual_comparison
      (fun _ : ℕ => X) (TangentCone q)
      (fun n => m.rescale (t n)⁻¹ (inv_pos.mpr (ht n))) inferInstance
      (fun _ => q) EuclideanCone.tip (fun n => 1 * (t n) ^ 2) hconv (fun n => by positivity)
      (by simpa using hzero.pow 2)
    intro B hB
    exact eventually_fourPointComparison_rescale_of_local
      (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ t ht hzero B hB
  · intro a b
    apply @PointedGHConverges.exists_metric_segment_of_source_curves
      (TangentCone q) inferInstance (fun _ : ℕ => X)
      (fun n => m.rescale (t n)⁻¹ (inv_pos.mpr (ht n)))
      (fun _ => q) EuclideanCone.tip inferInstance hconv _ a b
    intro n x y ε hε
    exact MetricSpace.rescale_arbitrarily_short_curves hcurves (t n)⁻¹
      (inv_pos.mpr (ht n)) x y hε

end Metric
