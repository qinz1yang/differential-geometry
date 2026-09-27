import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Curvature
import DifferentialGeometry.Geometry.Curvature.ScalarSectional
import DifferentialGeometry.Geometry.Metric.RadialFrame

set_option autoImplicit false
noncomputable section
open Bundle DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold InnerProductSpace
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

theorem metricScalarAt_tip (p : Metric.sphere (0 : E4) 1) {x : E3}
    (hxr : ‖x‖ < roundNormalRadius p) (hxa : ‖x‖ < transitionStart) :
    metricScalarAt metric x = 3 := by
  have h := metricScalarAt_of_constant_sectional metric x (1 / 2)
    (fun u v => metricRm04_tip p hxr hxa u v)
  norm_num at h
  exact h

theorem metricScalarAt_zero : metricScalarAt metric (0 : E3) = 3 := by
  let p : Metric.sphere (0 : E4) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  exact metricScalarAt_tip p (by simpa using roundNormalRadius_pos p)
    (by simpa using transitionStart_pos)

theorem metricScalarAt_eq_warping {x : E3} (hx : x ≠ 0) :
    metricScalarAt metric x =
      4 * (-deriv (deriv warpingFunction) ‖x‖ / warpingFunction ‖x‖) +
      2 * ((1 - deriv warpingFunction ‖x‖ ^ 2) / warpingFunction ‖x‖ ^ 2) := by
  classical
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have ha : warpingFunction ‖x‖ ≠ 0 := (warpingFunction_pos (norm_pos_iff.mpr hx)).ne'
  obtain ⟨b, hb⟩ := exists_radial_orthonormalBasis hx
  let B := radialMetricBasis warpingFunction hx ha b
  have hB : ∀ i j : Fin 3, metric.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    metric_inner_radialMetricBasis metric (metric_eventually_radial hx).eq_of_nhds hx ha b hb
  have haux (n : ℕ) (hd : Module.finrank ℝ E3 = n)
      (C : Fin n → TangentSpace (𝓡 3) x)
      (hC : ∀ i j, metric.inner x (C i) (C j) = if i = j then (1 : ℝ) else 0) :
      metricScalarAt metric x = ∑ i, ∑ j, metricRm04StandardAt metric x (C j) (C i) (C i) (C j) := by
    subst n
    exact metricScalarAt_eq_sum_metricRm04StandardAt metric x C hC
  have htrace := haux 3 (by simp) B hB
  have hterm (i j : Fin 3) : metricRm04StandardAt metric x (B j) (B i) (B i) (B j) =
      if i = j then 0 else if i = 0 ∨ j = 0 then
        -deriv (deriv warpingFunction) ‖x‖ / warpingFunction ‖x‖ else
        (1 - deriv warpingFunction ‖x‖ ^ 2) / warpingFunction ‖x‖ ^ 2 := by
    change metricRm04StandardAt metric x
      (radialMetricBasis warpingFunction hx ha b j) (radialMetricBasis warpingFunction hx ha b i)
      (radialMetricBasis warpingFunction hx ha b i) (radialMetricBasis warpingFunction hx ha b j) = _
    simp only [radialMetricBasis_apply]
    rw [metricRm04StdAt_radialBilinearField metric
      (metric_eventually_radial hx) contDiff_warpingFunction hx ha]
    simp only [real_inner_smul_left, real_inner_smul_right, b.inner_eq_ite,
      inner_radial_orthonormalBasis b hb]
    fin_cases i <;> fin_cases j <;> norm_num <;> field_simp <;> ring
  rw [htrace]
  simp only [hterm]
  simp [Fin.sum_univ_succ]
  ring

theorem one_le_metricScalarAt (x : E3) : 1 ≤ metricScalarAt metric x := by
  by_cases hx : x = 0
  · subst x
    rw [metricScalarAt_zero]
    norm_num
  · rw [metricScalarAt_eq_warping hx]
    exact one_le_warpingFunction_derivative_combination (norm_pos_iff.mpr hx)

theorem metricScalarAt_cylindrical {x : E3} (hx : transitionEnd ≤ ‖x‖) :
    metricScalarAt metric x = 1 := by
  rw [metricScalarAt_eq_warping (norm_pos_iff.mp (transitionEnd_pos.trans_le hx)),
    deriv_warpingFunction_eq_zero_of_transitionEnd_le hx,
    deriv_deriv_warpingFunction_eq_zero_of_transitionEnd_le hx,
    warpingFunction_eq_sqrt_two hx]
  norm_num

end DifferentialGeometry.PDE.RicciFlow.StandardCap
