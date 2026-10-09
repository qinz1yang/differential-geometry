import DifferentialGeometry.Geometry.Metric.Approximation.UniformSplittingCompatibility
import DifferentialGeometry.Geometry.Collapse.OriginalRadialSplitting
import DifferentialGeometry.Geometry.Collapse.CompleteRiemannianSegments
import DifferentialGeometry.Geometry.Comparison.RiemannianFourPoint
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves

/-!
# AC76 for actual complete Riemannian manifolds

Blueprint `master207A.tex`, AC76 (`thm:alexandrov-uniform-compatibility`, A:5986): for
`1 ≤ j ≤ k ≤ n` and `0 < τ, ν < 1` there is `0 < σ < 1` such that on a complete pointed length
space with local curvature `≥ −σ` and Hausdorff dimension `≤ n` on `B(p, σ⁻¹)` and no normalized
`(k+1, ν)`-splitting, every normalized `(j,σ)`-splitting is `τ`-compatible with every normalized
`(k,σ)`-splitting. The metric theorem is `exists_splitting_compatibility_parameter`
(`UniformSplittingCompatibility.lean`). This file is its producer for a complete smooth Riemannian
`n`-manifold whose metric-space distance is the Riemannian distance (`hmetric`), with sectional
curvature `≥ −σ` on exactly `B(p, σ⁻¹)`:

* length space: Hopf–Rinow segments (`segments_of_riemannianEDistOf_eq`) and
  `Metric.arbitrarily_short_curves_of_metric_segments`;
* dimension: `dimH_univ_le_finrank_of_riemannian_distance` (`n = finrank E`);
* local comparison: `exists_local_fourPointComparison_of_sectional_lower_bound` on the open ball.

The constant `σ` depends only on `j, k, finrank E, τ, ν`. The `(k+1)`-exclusion and the two
splittings are the row's own data; nothing else is assumed.
-/

set_option autoImplicit false

open Set Metric Bundle Manifold
open DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **AC76, actual producer.** On a complete smooth Riemannian manifold of dimension
`n = finrank E ≥ k` with sectional curvature `≥ −σ` on `B(p, σ⁻¹)` and no normalized
`(k+1, ν)`-splitting at `p`, every normalized `(j,σ)`-splitting is `τ`-compatible with every
normalized `(k,σ)`-splitting. -/
theorem exists_splitting_compatibility_parameter_riemannian {j k : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ Module.finrank ℝ E)
    {τ ν : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (hν : 0 < ν) (hνone : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M] (g : SmoothRiemannianMetric I M),
      (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) → ∀ p : M,
      (∀ y ∈ ball p σ⁻¹, SectionalBoundedBelowAt g y (-σ)) →
      (¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
        ∃ w : W, Nonempty (KleinerLottApprox p
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k + 1))), w)) ν)) →
      ∀ (A B : Type u) [MetricSpace A] [MetricSpace B] (a : A) (b : B)
        (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a)) σ)
        (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b)) σ),
        SplittingCompatible φ ψ τ := by
  have neZero_AC7679 : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨σ, hσ, hσone, hσprop⟩ :=
    exists_splitting_compatibility_parameter.{u} hj hjk hkn hτ hτone hν hνone
  refine ⟨σ, hσ, hσone, ?_⟩
  intro M _ _ _ _ _ g hmetric p hsec hno A B _ _ a b φ ψ
  exact hσprop M p
    (Metric.arbitrarily_short_curves_of_metric_segments
      (DifferentialGeometry.Geometry.Collapse.segments_of_riemannianEDistOf_eq g hmetric))
    ((dimH_mono (subset_univ _)).trans (dimH_univ_le_finrank_of_riemannian_distance g hmetric))
    (exists_local_fourPointComparison_of_sectional_lower_bound g hmetric isOpen_ball hσ.le hsec)
    hno A B a b φ ψ

end GC.MetricGeometry
