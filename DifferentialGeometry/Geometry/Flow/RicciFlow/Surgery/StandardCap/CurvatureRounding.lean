import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ScalarRounding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompatibleEnd
import DifferentialGeometry.Geometry.Curvature.ConformalLeastImprovement

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

theorem exists_curvature_rounding_collar {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 10000) :
    ∃ A : ℝ, 0 < A ∧ 2 * A < 1 / 2 ∧
      (∀ q : S2 × ℝ, q.2 ∈ Ico (-2 * A) 0 → ∀ u v : E3,
        metric.inner (conformalChart q : E3) u u *
          metric.inner (conformalChart q : E3) v v -
          (metric.inner (conformalChart q : E3) u v) ^ 2 ≠ 0 →
        0 < sectionalCurvature metric (conformalChart q : E3) u v) ∧
      (∀ z ∈ Ioo (-A) 0,
        conformalFactor z < 0 ∧ 0 < deriv conformalFactor z ∧
          deriv (deriv conformalFactor) z < 0 ∧
          max |conformalFactor z| |deriv conformalFactor z| ≤
            η * (-deriv (deriv conformalFactor) z)) ∧
      intervalDerivativeNorm contDiff_conformalFactor 2 (-A) 0 < η ∧
      ∀ h : SmoothRiemannianMetric IC (roundingCollar A),
        metricDerivENormSupOn univ 2 h (roundingReference A) (roundingReference A) <
          ENNReal.ofReal (1 / 100000000 : ℝ) →
        ∀ x : roundingCollar A,
          metricScalarAt h x + (-deriv (deriv conformalFactor) (x : S2 × ℝ).2) / 2 ≤
              metricScalarAt (roundingMetric A h) x ∧
            2 * leastCurvatureOperatorEigenvalueAt h x (metricAlgebraicCurvatureTensorAt h x) +
                (-deriv (deriv conformalFactor) (x : S2 × ℝ).2) / 2 ≤
              2 * leastCurvatureOperatorEigenvalueAt (roundingMetric A h) x
                (metricAlgebraicCurvatureTensorAt (roundingMetric A h) x) := by
  obtain ⟨A, hA, hAsmall, hprofile, hnorm, hscalar⟩ :=
    exists_scalar_rounding_collar hη (hηsmall.trans (by norm_num))
  refine ⟨A, hA, hAsmall, (fun q hq u v hplane =>
    sectionalCurvature_conformalChart_pos q hq.2 u v hplane), hprofile, hnorm, ?_⟩
  intro h hclose x
  have hj (k : ℕ) (hk : k ≤ 2) :
      metricDerivNorm k h (roundingReference A) (roundingReference A) x ≤ 1 / 100000000 :=
    (metricDerivNorm_lt_of_sup_lt univ 2 h (roundingReference A) (roundingReference A)
      hclose hk (mem_univ x)).le
  obtain ⟨hF, hp, hd, hrel⟩ := hprofile (x : S2 × ℝ).2 x.property
  have hD : 0 ≤ -deriv (deriv conformalFactor) (x : S2 × ℝ).2 := neg_nonneg.mpr hd.le
  have hsmall (k : ℕ) (hk : k ≤ 2) :
      |iteratedDeriv k conformalFactor (x : S2 × ℝ).2| ≤ 1 / 10000 := by
    have hh := norm_iteratedDeriv_le_intervalDerivativeNorm contDiff_conformalFactor hk
      (show (x : S2 × ℝ).2 ∈ Icc (-A) 0 from ⟨x.property.1.le, x.property.2.le⟩)
    rw [Real.norm_eq_abs] at hh
    exact (hh.trans hnorm.le).trans hηsmall
  have hrel' : max |conformalFactor (x : S2 × ℝ).2| |deriv conformalFactor (x : S2 × ℝ).2| ≤
      -deriv (deriv conformalFactor) (x : S2 × ℝ).2 / 10000 := by
    have hh := hrel.trans (mul_le_mul_of_nonneg_right hηsmall hD)
    calc
      _ ≤ (1 / 10000 : ℝ) * (-deriv (deriv conformalFactor) (x : S2 × ℝ).2) := hh
      _ = _ := by ring
  constructor
  · have hh := hscalar h
      (hclose.trans_le (ENNReal.ofReal_le_ofReal (by norm_num :
        (1 / 100000000 : ℝ) ≤ 1 / 10000))) x
    linarith
  · exact least_curvature_conformal_improvement_of_roundCylinder_metric_jets
      (roundingCollar A) h x (1 / 100000000) le_rfl hj conformalFactor contDiff_conformalFactor
      hF.le (by simpa only [iteratedDeriv_zero] using hsmall 0 (by norm_num))
      ((le_max_left _ _).trans hrel') hp.le
      (by simpa only [iteratedDeriv_one, abs_of_pos hp] using hsmall 1 (by norm_num))
      (by simpa only [abs_of_pos hp] using (le_max_right _ _).trans hrel')
      (by simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one, iteratedDeriv_zero, abs_of_neg hd] using hsmall 2 (by norm_num))

end DifferentialGeometry.PDE.RicciFlow.StandardCap
