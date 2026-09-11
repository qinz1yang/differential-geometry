import DifferentialGeometry.Analysis.Calculus.SmoothExtension.SmoothExtension
import DifferentialGeometry.Geometry.Metric.Euclidean.Construction
import DifferentialGeometry.Geometry.Metric.RadialField
import DifferentialGeometry.Geometry.Metric.RoundNormal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Profile

noncomputable section

open Bundle Set Filter Topology DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

def metricField : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ := by
  classical
  let b : E3 →L[ℝ] E3 →L[ℝ] ℝ := innerSL ℝ
  exact Function.update (radialBilinearField warpingFunction) 0 b

@[simp] theorem metricField_zero (v w : E3) : metricField 0 v w = ⟪v, w⟫_ℝ := by
  simp only [metricField, Function.update_self]
  rfl

theorem metricField_of_ne_zero {x : E3} (hx : x ≠ 0) :
    metricField x = radialBilinearField warpingFunction x := by
  simp [metricField, hx]

theorem metricField_symm (x v w : E3) : metricField x v w = metricField x w v := by
  by_cases hx : x = 0
  · subst x
    simp only [metricField_zero, real_inner_comm]
  · rw [metricField_of_ne_zero hx]
    exact radialBilinearField_symm _ _ _ _

theorem metricField_pos (x : E3) {v : E3} (hv : v ≠ 0) : 0 < metricField x v v := by
  by_cases hx : x = 0
  · subst x
    rw [metricField_zero]
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  · rw [metricField_of_ne_zero hx]
    exact radialBilinearField_pos hx (warpingFunction_pos (norm_pos_iff.mpr hx)).ne' hv

theorem metricField_eq_roundNormalMetric
    (p : Metric.sphere (0 : E4) 1) {x : E3}
    (hxr : ‖x‖ < roundNormalRadius p) (hxa : ‖x‖ ≤ transitionStart) (v w : E3) :
    metricField x v w = (roundNormalMetric p).inner x v w := by
  by_cases hx : x = 0
  · subst x
    rw [metricField_zero, roundNormalMetric_inner_zero]
  · rw [metricField_of_ne_zero hx, roundNormalMetric_inner_eq_radialBilinearForm p hx hxr]
    simp only [radialBilinearField, NormedSpace.normalize,
      warpingFunction_eq_sqrt_two_mul_sin hxa]

theorem contDiff_metricField : ContDiff ℝ ∞ metricField := by
  classical
  let p : Metric.sphere (0 : E4) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  let C : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ := fun x => by exact (roundNormalMetric p).inner x
  have hC : ContDiff ℝ ∞ C := contDiff_metric_inner (roundNormalMetric p)
  have hmatch : radialBilinearField warpingFunction =ᶠ[𝓝[≠] (0 : E3)] C := by
    have hr : 0 < min (roundNormalRadius p) transitionStart :=
      lt_min (roundNormalRadius_pos p) transitionStart_pos
    have hn : ∀ᶠ x : E3 in 𝓝 0, ‖x‖ < min (roundNormalRadius p) transitionStart :=
      continuous_norm.continuousAt.eventually_lt_const (by simpa using hr)
    filter_upwards [self_mem_nhdsWithin, hn.filter_mono nhdsWithin_le_nhds] with x hx hxr
    ext v w
    change radialBilinearField warpingFunction x v w = (roundNormalMetric p).inner x v w
    rw [← metricField_of_ne_zero hx]
    exact metricField_eq_roundNormalMetric p (hxr.trans_le (min_le_left _ _))
      (hxr.le.trans (min_le_right _ _)) v w
  have hs := DifferentialGeometry.Analysis.contDiff_update_of_eventuallyEq
    (radialBilinearField warpingFunction) C 0
    (fun _ hx => contDiffAt_radialBilinearField contDiff_warpingFunction.contDiffAt hx)
    hC.contDiffAt hmatch
  have hzero : C 0 = (show E3 →L[ℝ] E3 →L[ℝ] ℝ from innerSL ℝ) := by
    ext v w
    exact roundNormalMetric_inner_zero p v w
  simpa only [metricField, hzero] using hs

def metric : SmoothRiemannianMetric (𝓡 3) (EuclideanSpace ℝ (Fin 3)) :=
  smoothMetricOfBilinearField metricField metricField_symm
    (fun x _ hv => metricField_pos x hv) contDiff_metricField

theorem metric_inner (x v w : E3) : metric.inner x v w = metricField x v w :=
  smoothMetricOfBilinearField_inner _ _ _ _ x v w

@[simp] theorem metric_inner_zero (v w : E3) : metric.inner 0 v w = ⟪v, w⟫_ℝ := by
  rw [metric_inner, metricField_zero]

theorem metric_inner_of_ne_zero {x : E3} (hx : x ≠ 0) (v w : E3) :
    metric.inner x v w = radialBilinearField warpingFunction x v w := by
  rw [metric_inner, metricField_of_ne_zero hx]

theorem metric_inner_round (p : Metric.sphere (0 : E4) 1) {x : E3}
    (hxr : ‖x‖ < roundNormalRadius p) (hxa : ‖x‖ ≤ transitionStart) (v w : E3) :
    metric.inner x v w = (roundNormalMetric p).inner x v w := by
  rw [metric_inner]
  exact metricField_eq_roundNormalMetric p hxr hxa v w

theorem metric_inner_cylindrical {x : E3} (hx : transitionEnd ≤ ‖x‖) (v w : E3) :
    metric.inner x v w =
      radialBilinearForm (NormedSpace.normalize x) ((Real.sqrt 2 / ‖x‖) ^ 2) v w := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (transitionEnd_pos.trans_le hx)
  rw [metric_inner_of_ne_zero hx0, radialBilinearField, warpingFunction_eq_sqrt_two hx]

theorem metric_inner_linearIsometry (f : E3 →ₗᵢ[ℝ] E3) (x v w : E3) :
    metric.inner (f x) (f v) (f w) = metric.inner x v w := by
  rw [metric_inner, metric_inner]
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, metricField_zero, f.inner_map_map]
  · have hfx : f x ≠ 0 := by
      intro h
      exact hx (f.injective (h.trans f.map_zero.symm))
    rw [metricField_of_ne_zero hfx, metricField_of_ne_zero hx]
    exact radialBilinearField_linearIsometry f _ x v w

theorem metric_inner_radial (x v : E3) : metric.inner x x v = ⟪x, v⟫_ℝ := by
  by_cases hx : x = 0
  · subst x
    exact metric_inner_zero 0 v
  · rw [metric_inner_of_ne_zero hx]
    exact radialBilinearField_radial _ x v

theorem metric_inner_unit_radial {x : E3} (hx : x ≠ 0) :
    metric.inner x (NormedSpace.normalize (V := E3) x)
      (NormedSpace.normalize (V := E3) x) = 1 := by
  rw [metric_inner_of_ne_zero hx]
  exact radialBilinearField_unit_radial_self _ hx

theorem inner_sq_le_metric {x : E3} (hx : x ≠ 0) (v : E3) :
    ⟪NormedSpace.normalize x, v⟫_ℝ ^ 2 ≤ metric.inner x v v := by
  rw [metric_inner_of_ne_zero hx]
  exact inner_sq_le_radialBilinearField _ hx v

theorem metric_inner_le (x v : E3) : metric.inner x v v ≤ ‖v‖ ^ 2 := by
  by_cases hx : x = 0
  · subst x
    rw [metric_inner_zero, real_inner_self_eq_norm_sq]
  · rw [metric_inner_of_ne_zero hx]
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have ha0 : 0 ≤ warpingFunction ‖x‖ / ‖x‖ :=
      (div_pos (warpingFunction_pos hr) hr).le
    have ha1 : warpingFunction ‖x‖ / ‖x‖ ≤ 1 :=
      (div_le_one hr).mpr (warpingFunction_le hr.le)
    have ha2 : (warpingFunction ‖x‖ / ‖x‖) ^ 2 ≤ 1 := by nlinarith
    simpa only [max_eq_right ha2, one_mul] using
      radialBilinearField_upper_bound warpingFunction hx v

theorem metric_inner_polar {e : E3} (he : ‖e‖ = 1)
    {v w : E3} (hv : ⟪e, v⟫_ℝ = 0) (hw : ⟪e, w⟫_ℝ = 0)
    {r : ℝ} (hr : 0 < r) (s t : ℝ) :
    metric.inner (r • e) (s • e + r • v) (t • e + r • w) =
      s * t + warpingFunction r ^ 2 * ⟪v, w⟫_ℝ := by
  have he0 : e ≠ 0 := norm_ne_zero_iff.mp (by rw [he]; norm_num)
  rw [metric_inner_of_ne_zero (smul_ne_zero hr.ne' he0)]
  exact radialBilinearField_polar _ he hv hw hr s t

end DifferentialGeometry.PDE.RicciFlow.StandardCap
