import DifferentialGeometry.Geometry.Curvature.RiemannPerturbation
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

/-- A negative reference plane persists under a small relative metric error
through order two, with an explicit sectional-curvature margin. -/
theorem metricRm04_lt_neg_mul_gram_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (x : M) {eps c a K : ℝ}
    (heps : eps ≤ 1 / 2) (ha : 0 ≤ a)
    (hsmall : ∀ j : ℕ, j ≤ 2 → metricDerivNorm j g G G x ≤ eps)
    (u v : TangentSpace I x) (hu : G.inner x u u = 1) (hv : G.inner x v v = 1)
    (hcurv : metricRm04StandardAt G x u v v u ≤ -c)
    (hmodel : Real.sqrt (G.inner x (riemannOp (LeviCivita G) x u v v)
      (riemannOp (LeviCivita G) x u v v)) ≤ K)
    (hbudget : eps * (360 + K) + a * (1 + eps) ^ 2 < c) :
    metricRm04StandardAt g x u v v u <
      -a * (g.inner x u u * g.inner x v v - g.inner x u v ^ 2) := by
  have heps0 : 0 ≤ eps := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hdiagU : g.inner x u u ≤ 1 + eps := by
    simpa only [hu, mul_one] using
      (inner_bounds_of_metricDerivNorm_le G g x (hsmall 0 (by norm_num)) u).2
  have hdiagV : g.inner x v v ≤ 1 + eps := by
    simpa only [hv, mul_one] using
      (inner_bounds_of_metricDerivNorm_le G g x (hsmall 0 (by norm_num)) v).2
  have hprod := mul_le_mul hdiagU hdiagV (metric_inner_self_nonneg g x v)
    (by linarith : 0 ≤ 1 + eps)
  have hgram : g.inner x u u * g.inner x v v - g.inner x u v ^ 2 ≤
      (1 + eps) ^ 2 := by
    nlinarith [sq_nonneg (g.inner x u v)]
  have herr := abs_metricRm04_sub_le_of_small_metric_derivatives
    g G x heps hsmall u v v u
  simp only [hu, hv, Real.sqrt_one, mul_one] at herr
  have herror : |metricRm04StandardAt g x u v v u -
      metricRm04StandardAt G x u v v u| ≤ eps * (360 + K) :=
    herr.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (360 : ℝ)) hmodel) heps0)
  have hstrict : metricRm04StandardAt g x u v v u < -a * (1 + eps) ^ 2 := by
    linarith [(abs_le.mp herror).2]
  exact hstrict.trans_le (mul_le_mul_of_nonpos_left hgram (neg_nonpos.mpr ha))

/-- The same controlled reference plane violates the proposed lower bound
for the actual metric at the original point. -/
theorem not_sectionalBoundedBelowAt_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (x : M) {eps c a K : ℝ}
    (heps : eps ≤ 1 / 2) (ha : 0 ≤ a)
    (hsmall : ∀ j : ℕ, j ≤ 2 → metricDerivNorm j g G G x ≤ eps)
    (u v : TangentSpace I x) (hu : G.inner x u u = 1) (hv : G.inner x v v = 1)
    (hcurv : metricRm04StandardAt G x u v v u ≤ -c)
    (hmodel : Real.sqrt (G.inner x (riemannOp (LeviCivita G) x u v v)
      (riemannOp (LeviCivita G) x u v v)) ≤ K)
    (hbudget : eps * (360 + K) + a * (1 + eps) ^ 2 < c) :
    ¬ SectionalBoundedBelowAt g x (-a) := by
  intro hsec
  exact (not_le_of_gt (metricRm04_lt_neg_mul_gram_of_small_metric_derivatives
    g G x heps ha hsmall u v hu hv hcurv hmodel hbudget)) (hsec u v)

theorem not_sectionalBoundedBelowAt_neg_one_eighth_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (x : M) {eps : ℝ}
    (heps : eps ≤ 1 / 10000)
    (hsmall : ∀ j : ℕ, j ≤ 2 → metricDerivNorm j g G G x ≤ eps)
    (u v : TangentSpace I x) (hu : G.inner x u u = 1) (hv : G.inner x v v = 1)
    (hcurv : metricRm04StandardAt G x u v v u ≤ -(1 / 4 : ℝ))
    (hmodel : Real.sqrt (G.inner x (riemannOp (LeviCivita G) x u v v)
      (riemannOp (LeviCivita G) x u v v)) ≤ 2) :
    ¬ SectionalBoundedBelowAt g x (-(1 / 8 : ℝ)) := by
  apply not_sectionalBoundedBelowAt_of_small_metric_derivatives g G x
    (by linarith : eps ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    hsmall u v hu hv hcurv hmodel
  have heps0 : 0 ≤ eps := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hquad : eps ^ 2 ≤ eps / 10000 := by
    nlinarith [mul_nonneg heps0 (sub_nonneg.mpr heps)]
  nlinarith

end DifferentialGeometry.Geometry.Curvature
