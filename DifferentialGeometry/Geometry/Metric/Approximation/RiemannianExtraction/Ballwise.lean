import DifferentialGeometry.Geometry.Comparison.RiemannianCovering.ArbitraryCurvature
import DifferentialGeometry.Geometry.Metric.Approximation.PointedPrecompactness
import DifferentialGeometry.Geometry.Metric.Approximation.MidpointTransfer
import DifferentialGeometry.Topology.MetricSpace.IntrinsicEDist

set_option autoImplicit false
open Set Metric Filter DifferentialGeometry
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (TangentBundle I (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

theorem exists_pointed_limit_of_ballwise_sectional_lower_bounds
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) (A : ℝ → ℝ)
    (hsec : ∀ R > 0, ∀ i, ∀ y ∈ ball (p i) R,
      SectionalBoundedBelowAt (g i) y (-A R)) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ a b : Y, Metric.intrinsicEDist a b = edist a b) ∧
        ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  have hnets : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i : ℕ,
      ∃ T : Finset (X i), T.card ≤ N ∧
        (∀ y ∈ T, dist y (p i) ≤ R) ∧
        ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ T, dist x y ≤ ε := by
    intro R hR ε hε
    refine ⟨(1 + ⌈4 * (2 : ℝ) ^ 2 * Real.sqrt (Module.finrank ℝ E) *
      Real.sinh (2 * (Real.sqrt (max 1 (A (8 * R))) * R)) /
      (Real.sqrt (max 1 (A (8 * R))) * ε)⌉₊) ^ Module.finrank ℝ E, ?_⟩
    intro i
    obtain ⟨T, hcard, hT, hnet⟩ := exists_closedBall_net_of_arbitrary_sectional_lower_bound
      (g i) (hmetric i) (p i) hR hε (hsec (8 * R) (by positivity) i)
    refine ⟨T, hcard, fun y hy => hT hy, fun x hx => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    exact ⟨y, hy, hxy.le⟩
  obtain ⟨Y, m, q, φ, hφ, hproper, hconv⟩ :=
    exists_pointedGHConverges_of_uniform_finite_nets p hnets
  let _ := m
  let _ := hproper
  have hcurves := fun i (a b : X (φ i)) (ε : ℝ) (hε : 0 < ε) =>
    DifferentialGeometry.Geometry.Metric.exists_arbitrarily_short_riemannian_curve
      (g (φ i)) (hmetric (φ i)) a b hε
  exact ⟨Y, m, q, φ, hφ, hproper, hconv,
    Metric.intrinsicEDist_eq_edist_of_arbitrarily_short_curves
      (hconv.arbitrarily_short_curves hcurves),
    hconv.exists_metric_segment_of_source_curves hcurves⟩

end GC.MetricGeometry
