import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Metric.Construction.ConvexCombination

set_option autoImplicit false
noncomputable section
open Set Filter Topology DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

def truncationCutoff (R : ℝ) (x : E3) : ℝ :=
  1 - Real.smoothTransition (‖x‖ - (R - 2))

theorem truncationCutoff_mem (R : ℝ) (x : E3) :
    truncationCutoff R x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact sub_nonneg.mpr (Real.smoothTransition.le_one _)
  · exact sub_le_self _ (Real.smoothTransition.nonneg _)

theorem truncationCutoff_eq_one (R : ℝ) {x : E3} (hx : ‖x‖ ≤ R - 2) :
    truncationCutoff R x = 1 := by
  rw [truncationCutoff, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx), sub_zero]

theorem truncationCutoff_eq_zero (R : ℝ) {x : E3} (hx : R - 1 ≤ ‖x‖) :
    truncationCutoff R x = 0 := by
  rw [truncationCutoff, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem truncationCutoff_contMDiff (R : ℝ) (hR : 2 < R) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (truncationCutoff R) := by
  apply ContDiff.contMDiff
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E3 => (1 : ℝ)) 0).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
      (show ‖(0 : E3)‖ < R - 2 by simpa using sub_pos.mpr hR)] with y hy
    exact truncationCutoff_eq_one R hy.le
  · exact contDiffAt_const.sub
      (Real.smoothTransition.contDiff.contDiffAt.comp x
        ((contDiffAt_norm ℝ hx).sub contDiffAt_const))

def metricTruncation (g : SmoothRiemannianMetric (𝓡 3) E3) (R : ℝ) (hR : 2 < R) :
    SmoothRiemannianMetric (𝓡 3) E3 :=
  g.convexComb metric (truncationCutoff R) (truncationCutoff_contMDiff R hR)
    (truncationCutoff_mem R)

theorem metricTruncation_inner (g : SmoothRiemannianMetric (𝓡 3) E3)
    (R : ℝ) (hR : 2 < R) (x : E3) (v w : TangentSpace (𝓡 3) x) :
    (metricTruncation g R hR).inner x v w =
      truncationCutoff R x * g.inner x v w +
        (1 - truncationCutoff R x) * metric.inner x v w := by
  exact convexComb_inner _ _ _ _ _ _ _ _

theorem metricTruncation_inner_core (g : SmoothRiemannianMetric (𝓡 3) E3)
    (R : ℝ) (hR : 2 < R) {x : E3} (hx : ‖x‖ ≤ R - 2)
    (v w : TangentSpace (𝓡 3) x) :
    (metricTruncation g R hR).inner x v w = g.inner x v w := by
  rw [metricTruncation_inner, truncationCutoff_eq_one R hx]
  ring

theorem metricTruncation_inner_end (g : SmoothRiemannianMetric (𝓡 3) E3)
    (R : ℝ) (hR : 2 < R) {x : E3} (hx : R - 1 ≤ ‖x‖)
    (v w : TangentSpace (𝓡 3) x) :
    (metricTruncation g R hR).inner x v w = metric.inner x v w := by
  rw [metricTruncation_inner, truncationCutoff_eq_zero R hx]
  ring

theorem metricTruncation_lower (g : SmoothRiemannianMetric (𝓡 3) E3)
    (R : ℝ) (hR : 2 < R) (ell : ℝ)
    (hlower : ∀ (x : E3) (v : TangentSpace (𝓡 3) x),
      ell * metric.inner x v v ≤ g.inner x v v)
    (x : E3) (v : TangentSpace (𝓡 3) x) :
    min ell 1 * metric.inner x v v ≤ (metricTruncation g R hR).inner x v v := by
  have hnonneg : 0 ≤ metric.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (metric.pos x v hv).le
  have hleft := (mul_le_mul_of_nonneg_right (min_le_left ell 1) hnonneg).trans (hlower x v)
  have hright : min ell 1 * metric.inner x v v ≤ metric.inner x v v := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_right ell 1) hnonneg
  have hχ := truncationCutoff_mem R x
  rw [metricTruncation_inner]
  calc
    _ = truncationCutoff R x * (min ell 1 * metric.inner x v v) +
        (1 - truncationCutoff R x) * (min ell 1 * metric.inner x v v) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hleft hχ.1)
      (mul_le_mul_of_nonneg_left hright (sub_nonneg.mpr hχ.2))

theorem metricTruncation_complete (g : SmoothRiemannianMetric (𝓡 3) E3)
    (R : ℝ) (hR : 2 < R) (ell : ℝ) (hell : 0 < ell)
    (hlower : ∀ (x : E3) (v : TangentSpace (𝓡 3) x),
      ell * metric.inner x v v ≤ g.inner x v v) :
    RiemannianMetricComplete (metricTruncation g R hR) :=
  RiemannianMetricComplete.of_lower metric_complete (lt_min hell zero_lt_one)
    (metricTruncation_lower g R hR ell hlower)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
