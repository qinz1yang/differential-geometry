import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison
import DifferentialGeometry.Geometry.Metric.RiemannianShortCurves
import DifferentialGeometry.Geometry.Metric.Approximation.ZeroStratumSmallCoreCover
import DifferentialGeometry.Topology.MetricSpace.GeodesicMidpoint
import DifferentialGeometry.Topology.MetricSpace.CurveMidpoint

/-!
# Minimizing segments of a complete Riemannian metric (Hopf–Rinow)

For a smooth metric `g` on a connected manifold whose length distance is complete
(`RiemannianMetricComplete g`), the induced metric space (`inducedMetricSpace g`) has
constant-speed minimizing segments between any two points, and so does every rescaling of it.
This removes the compactness assumption of `inducedMetricSpace_segments`
(`ZeroStratumRiemannian.lean`): properness comes from Hopf–Rinow
(`inducedMetricSpace_properSpace_of_riemannianMetricComplete`), arbitrarily short curves from
`exists_arbitrarily_short_riemannian_curve`, and segments from approximate midpoints.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]

/-- Constant-speed minimizing segments for the distance of a complete metric `g`. -/
theorem inducedMetricSpace_segments_of_riemannianMetricComplete
    {g : SmoothRiemannianMetric I M} (hg : RiemannianMetricComplete (I := I) g) :
    letI := inducedMetricSpace g
    ∀ x y : M, ∃ f : Icc (0 : ℝ) 1 → M,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let := inducedMetricSpace g
  have : ProperSpace M := inducedMetricSpace_properSpace_of_riemannianMetricComplete hg
  have : CompleteSpace M := riemannianMetricComplete_iff_inducedMetricSpace.mp hg
  intro x y
  exact Metric.exists_metric_segment_of_approximate_midpoints
    (Metric.approximate_midpoints_of_arbitrarily_short_curves
      (fun a b η hη => DifferentialGeometry.Geometry.Metric.exists_arbitrarily_short_riemannian_curve
        g (inducedMetricSpace_hmetric g) a b hη)) x y

/-- The same segments for the rescaled distance `c · d_g` (the distance of `c² g`). -/
theorem inducedMetricSpace_rescale_segments_of_riemannianMetricComplete
    {g : SmoothRiemannianMetric I M} (hg : RiemannianMetricComplete (I := I) g)
    {c : ℝ} (hc : 0 < c) :
    letI := (inducedMetricSpace g).rescale c hc
    ∀ x y : M, ∃ f : Icc (0 : ℝ) 1 → M,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (f s) (f t) = dist x y * dist s t :=
  GC.MetricGeometry.rescale_segments (inducedMetricSpace g) hc
    (inducedMetricSpace_segments_of_riemannianMetricComplete hg)

/-- The same segments for any metric space structure on `M` whose distance is the `g`-length
distance (`hmetric`, the convention of LC09 and of the soul toolkit) and which is complete. -/
theorem segments_of_riemannianEDistOf_eq {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b)) :
    ∀ x y : M, ∃ f : Icc (0 : ℝ) 1 → M,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  have hg : RiemannianMetricComplete (I := I) g :=
    (riemannianMetricComplete_iff_completeSpace hmetric).mpr inferInstance
  have : ProperSpace M := by
    refine ProperSpace.of_isCompact_closedBall_of_le 0 fun p r hr => ?_
    have heq : Metric.closedBall p r = riemannianClosedBallOf g p r := by
      ext y
      rw [Metric.mem_closedBall, dist_comm]
      change dist p y ≤ r ↔ riemannianEDistOf (I := I) g p y ≤ ENNReal.ofReal r
      rw [hmetric, ENNReal.ofReal_le_ofReal_iff hr]
    rw [heq]
    exact isCompact_riemannianClosedBallOf hg p r
  intro x y
  exact Metric.exists_metric_segment_of_approximate_midpoints
    (Metric.approximate_midpoints_of_arbitrarily_short_curves
      (fun a b η hη => DifferentialGeometry.Geometry.Metric.exists_arbitrarily_short_riemannian_curve
        g hmetric a b hη)) x y

end DifferentialGeometry.Geometry.Collapse
