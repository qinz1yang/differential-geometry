import DifferentialGeometry.Geometry.Curvature.DerivativeIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDouble
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.DerivativeBounds

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

theorem normSq_iterCov_compactDoubleMetric_capMap (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (k : ℕ) (x : E3) (hx : x ∈ Metric.ball 0 (R + 1)) :
    normSq0S (compactDoubleMetric north R hR) (compactDoubleCapMap north R x) (4 + k)
      (iterCov (compactDoubleMetric north R hR) 4 (metricRm04 (compactDoubleMetric north R hR))
        k (compactDoubleCapMap north R x)) =
      normSq0S metric x (4 + k) (iterCov metric 4 (metricRm04 metric) k x) := by
  let U : TopologicalSpace.Opens E3 := ⟨Metric.ball 0 (R + 1), Metric.isOpen_ball⟩
  exact (normSq_iterCov_metricRm04_of_metric_isometry_on_open metric
    (compactDoubleMetric north R hR) U (compactDoubleCapMap north R)
    (contMDiff_compactDoubleCapMap north R).contMDiffOn
    (fun y hy v w => (compactDoubleMetric_cap_pullback north R hR y hy v w).symm) k ⟨x, hx⟩).symm

theorem normSq_iterCov_compactDoubleMetric_antipodal_capMap (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (k : ℕ) (x : E3) (hx : x ∈ Metric.ball 0 (R + 1)) :
    let p := sphereAntipodalDiffeomorph (n := 3) (compactDoubleCapMap north R x)
    normSq0S (compactDoubleMetric north R hR) p (4 + k)
      (iterCov (compactDoubleMetric north R hR) 4 (metricRm04 (compactDoubleMetric north R hR)) k p) =
      normSq0S metric x (4 + k) (iterCov metric 4 (metricRm04 metric) k x) := by
  let U : TopologicalSpace.Opens E3 := ⟨Metric.ball 0 (R + 1), Metric.isOpen_ball⟩
  let F := (sphereAntipodalDiffeomorph (n := 3) : S3 → S3) ∘ compactDoubleCapMap north R
  have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F :=
    (sphereAntipodalDiffeomorph (n := 3)).contMDiff.comp (contMDiff_compactDoubleCapMap north R)
  exact (normSq_iterCov_metricRm04_of_metric_isometry_on_open metric
    (compactDoubleMetric north R hR) U F hF.contMDiffOn
    (fun y hy v w => (compactDoubleMetric_antipodal_cap_pullback north R hR y hy v w).symm)
    k ⟨x, hx⟩).symm

theorem exists_pos_bounds_iterCov_compactDoubleMetric :
    ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
      ∀ (north : S3) (R : ℝ) (hR : max transitionEnd 2 + 2 ≤ R) (k : ℕ) (p : S3),
        Real.sqrt (normSq0S (compactDoubleMetric north R hR) p (4 + k)
          (iterCov (compactDoubleMetric north R hR) 4
            (metricRm04 (compactDoubleMetric north R hR)) k p)) ≤ A k := by
  choose A hA hbound using exists_pos_bound_iterCov_metricRm04
  refine ⟨A, hA, ?_⟩
  intro north R hR k p
  obtain ⟨x, hx, he | he⟩ := compactDoubleCapMap_cover north R
    (by linarith [le_max_right transitionEnd 2]) p
  · have hh := congrArg Real.sqrt (normSq_iterCov_compactDoubleMetric_capMap north R hR k x hx)
    rw [he] at hh
    exact hh.le.trans (hbound k x)
  · have hh := congrArg Real.sqrt (normSq_iterCov_compactDoubleMetric_antipodal_capMap north R hR k x hx)
    rw [he] at hh
    exact hh.le.trans (hbound k x)
end DifferentialGeometry.PDE.RicciFlow.StandardCap
