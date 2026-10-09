import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDoublePatch
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDoubleCurvature

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

theorem normSq_iterCov_compactDoublePatchedMetric_capMap (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (g : SmoothRiemannianMetric (𝓡 3) E3)
    (hend : ∀ x : E3, R - 1 ≤ ‖x‖ → ∀ v w : E3, g.inner x v w = metric.inner x v w)
    (k : ℕ) (x : E3) (hx : x ∈ Metric.ball 0 (R + 1)) :
    normSq0S (compactDoublePatchedMetric north R hR g hend) (compactDoubleCapMap north R x)
      (4 + k) (iterCov (compactDoublePatchedMetric north R hR g hend) 4
        (metricRm04 (compactDoublePatchedMetric north R hR g hend)) k (compactDoubleCapMap north R x)) =
      normSq0S g x (4 + k) (iterCov g 4 (metricRm04 g) k x) := by
  let U : TopologicalSpace.Opens E3 := ⟨Metric.ball 0 (R + 1), Metric.isOpen_ball⟩
  exact (normSq_iterCov_metricRm04_of_metric_isometry_on_open g
    (compactDoublePatchedMetric north R hR g hend) U (compactDoubleCapMap north R)
    (contMDiff_compactDoubleCapMap north R).contMDiffOn
    (fun y hy v w => (compactDoublePatchedMetric_cap_pullback north R hR g hend y hy v w).symm)
    k ⟨x, hx⟩).symm

theorem normSq_iterCov_compactDoublePatchedMetric_exterior (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (g : SmoothRiemannianMetric (𝓡 3) E3)
    (hend : ∀ x : E3, R - 1 ≤ ‖x‖ → ∀ v w : E3, g.inner x v w = metric.inner x v w)
    (k : ℕ) (p : S3) (hp : p ∉ compactDoubleCapMap north R '' Metric.closedBall 0 (R - 1)) :
    normSq0S (compactDoublePatchedMetric north R hR g hend) p (4 + k)
      (iterCov (compactDoublePatchedMetric north R hR g hend) 4
        (metricRm04 (compactDoublePatchedMetric north R hR g hend)) k p) =
      normSq0S (compactDoubleMetric north R hR) p (4 + k)
        (iterCov (compactDoubleMetric north R hR) 4 (metricRm04 (compactDoubleMetric north R hR)) k p) := by
  let U : TopologicalSpace.Opens S3 :=
    ⟨(compactDoubleCapMap north R '' Metric.closedBall 0 (R - 1))ᶜ,
      ((isCompact_closedBall (0 : E3) (R - 1)).image
        (contMDiff_compactDoubleCapMap north R).continuous).isClosed.isOpen_compl⟩
  exact normSq_iterCov_metricRm04_of_metric_isometry_on_open
    (compactDoublePatchedMetric north R hR g hend) (compactDoubleMetric north R hR)
    U id contMDiffOn_id
    (fun y hy v w => by
      simpa only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using
        compactDoublePatchedMetric_inner_exterior north R hR g hend y hy v w)
    k ⟨p, hp⟩

theorem exists_uniform_bounds_iterCov_compactDoublePatchedMetric (A : ℕ → ℝ) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ (north : S3) (R : ℝ) (hR : max transitionEnd 2 + 2 ≤ R)
        (g : SmoothRiemannianMetric (𝓡 3) E3)
        (hend : ∀ x : E3, R - 1 ≤ ‖x‖ → ∀ v w : E3, g.inner x v w = metric.inner x v w),
        (∀ k : ℕ, ∀ x : E3,
          Real.sqrt (normSq0S g x (4 + k) (iterCov g 4 (metricRm04 g) k x)) ≤ A k) →
        ∀ k : ℕ, ∀ p : S3,
          Real.sqrt (normSq0S (compactDoublePatchedMetric north R hR g hend) p (4 + k)
            (iterCov (compactDoublePatchedMetric north R hR g hend) 4
              (metricRm04 (compactDoublePatchedMetric north R hR g hend)) k p)) ≤ B k := by
  obtain ⟨C, hC, hc⟩ := exists_pos_bounds_iterCov_compactDoubleMetric
  refine ⟨fun k => max (A k) (C k), (fun k => (hC k).trans_le (le_max_right _ _)), ?_⟩
  intro north R hR g hend hg k p
  by_cases hp : p ∈ compactDoubleCapMap north R '' Metric.closedBall 0 (R - 1)
  · obtain ⟨x, hx, rfl⟩ := hp
    have hball : x ∈ Metric.ball 0 (R + 1) :=
      Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt (by linarith))
    rw [normSq_iterCov_compactDoublePatchedMetric_capMap north R hR g hend k x hball]
    exact (hg k x).trans (le_max_left _ _)
  · rw [normSq_iterCov_compactDoublePatchedMetric_exterior north R hR g hend k p hp]
    exact (hc north R hR k p).trans (le_max_right _ _)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
