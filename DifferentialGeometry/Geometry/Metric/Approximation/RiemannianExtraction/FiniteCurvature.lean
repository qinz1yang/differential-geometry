import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianExtraction.Ballwise
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalNorm


set_option autoImplicit false
noncomputable section
open Set Metric Filter DifferentialGeometry
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness

namespace GC.MetricGeometry

universe u
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (TangentBundle I (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

theorem exists_pointed_limit_of_original_finite_curvature_bounds
    (K : ℕ) (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) (A : ℝ → ℝ)
    (hcurv : ∀ R > 0, ∀ i, ∀ j ≤ K,
      ∀ y ∈ riemannianBallOf (g i) (p i) R, curvDerivNorm j (g i) y ≤ A R) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ a b : Y, Metric.intrinsicEDist a b = edist a b) ∧
        ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  apply exists_pointed_limit_of_ballwise_sectional_lower_bounds g hmetric p A
  intro R hR i y hy
  have hy' : y ∈ riemannianBallOf (g i) (p i) R := by
    change riemannianEDistOf (g i) (p i) y < ENNReal.ofReal R
    rw [hmetric i, ENNReal.ofReal_lt_ofReal_iff hR, dist_comm]
    exact hy
  have hzero : Real.sqrt (Tensor0SBundle.normSq0S (g i) y 4
      (metricRm04At (g i) y)) ≤ A R := hcurv R hR i 0 (Nat.zero_le K) y hy'
  exact sectionalBoundedBelowAt_neg_of_sqrt_normSq0S_le (g i) y hzero

end GC.MetricGeometry
