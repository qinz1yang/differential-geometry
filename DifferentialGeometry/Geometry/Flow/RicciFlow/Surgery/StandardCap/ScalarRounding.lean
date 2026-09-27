import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalEstimates
import DifferentialGeometry.Geometry.Curvature.ConformalScalarImprovement
import DifferentialGeometry.Geometry.Curvature.ScalarRoundCylinder
import DifferentialGeometry.Geometry.Operator.Restriction
import DifferentialGeometry.Geometry.Operator.Cylinder
import DifferentialGeometry.Geometry.Metric.DerivativeENorm
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev cylinder := roundCylinderMetric (E := E3) (n := 2)
private abbrev sphereMetric := scaleMetric 2 (by norm_num) (roundMetric (E := E3) (n := 2))

def roundingCollar (A : ℝ) : TopologicalSpace.Opens (S2 × ℝ) :=
  ⟨{q | q.2 ∈ Ioo (-A) 0}, isOpen_Ioo.preimage continuous_snd⟩

abbrev roundingReference (A : ℝ) : SmoothRiemannianMetric IC (roundingCollar A) :=
  cylinder.restrictOpen (roundingCollar A)

private theorem height_smooth (A : ℝ) :
    ContMDiff IC 𝓘(ℝ) ∞ (fun y : roundingCollar A => (y : S2 × ℝ).2) :=
  contMDiff_snd.comp (contMDiff_subtype_val (I := IC) (U := roundingCollar A))

def roundingMetric (A : ℝ) (h : SmoothRiemannianMetric IC (roundingCollar A)) :
    SmoothRiemannianMetric IC (roundingCollar A) :=
  conformalMetricOfContDiff h (fun y : roundingCollar A => conformalFactor (y : S2 × ℝ).2)
    (contDiff_conformalFactor.contMDiff.comp (height_smooth A))

private theorem height_gradient_unit (A : ℝ) (x : roundingCollar A) :
    (roundingReference A).inner x
      (gradFun (roundingReference A) (fun y : roundingCollar A => (y : S2 × ℝ).2) x)
      (gradFun (roundingReference A) (fun y : roundingCollar A => (y : S2 × ℝ).2) x) = 1 := by
  have ht := gradFun_restrictOpen cylinder (roundingCollar A) Prod.snd x mdifferentiableAt_snd
  rw [mfderiv_subtype_val_apply] at ht
  have ha := gradFun_height_eq_cylinderAxis sphereMetric (x : S2 × ℝ)
  have hg : gradFun (roundingReference A) (fun y : roundingCollar A => (y : S2 × ℝ).2) x =
      cylinderAxis (I := 𝓡 2) (x : S2 × ℝ) := ht.trans ha
  change cylinder.inner (x : S2 × ℝ) _ _ = 1
  erw [hg]
  exact cylinderMetric_axis_unit sphereMetric (x : S2 × ℝ)

private theorem height_hessian_zero (A : ℝ) (x : roundingCollar A)
    (v w : TangentSpace IC x) :
    hessFun (roundingReference A) (fun y : roundingCollar A => (y : S2 × ℝ).2) x v w = 0 := by
  apply (hessFun_restrictOpen_of_contMDiff cylinder (roundingCollar A) Prod.snd contMDiff_snd x v w).trans
  exact DifferentialGeometry.Geometry.Connection.hessFun_height_cylinderMetric sphereMetric
    (x : S2 × ℝ) _ _

theorem exists_scalar_rounding_collar {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 10) :
    ∃ A : ℝ, 0 < A ∧ 2 * A < 1 / 2 ∧
      (∀ z ∈ Ioo (-A) 0,
        conformalFactor z < 0 ∧ 0 < deriv conformalFactor z ∧
          deriv (deriv conformalFactor) z < 0 ∧
          max |conformalFactor z| |deriv conformalFactor z| ≤
            η * (-deriv (deriv conformalFactor) z)) ∧
      intervalDerivativeNorm contDiff_conformalFactor 2 (-A) 0 < η ∧
      ∀ h : SmoothRiemannianMetric IC (roundingCollar A),
        metricDerivENormSupOn univ 2 h (roundingReference A) (roundingReference A) <
          ENNReal.ofReal (1 / 10000 : ℝ) →
        ∀ x : roundingCollar A,
          metricScalarAt h x + 2 * (-deriv (deriv conformalFactor) (x : S2 × ℝ).2) ≤
            metricScalarAt (roundingMetric A h) x := by
  obtain ⟨A, hA, hAsmall, _, hprofile, hnorm⟩ := exists_conformal_collar hη
  refine ⟨A, hA, hAsmall, hprofile, hnorm, ?_⟩
  intro h hclose x
  have hj (k : ℕ) (hk : k ≤ 2) :
      metricDerivNorm k h (roundingReference A) (roundingReference A) x ≤ 1 / 10000 :=
    (metricDerivNorm_lt_of_sup_lt univ 2 h (roundingReference A) (roundingReference A)
      hclose hk (mem_univ x)).le
  have hs := abs_scalar_curvature_restricted_roundCylinder_sub_one_le
    (roundingCollar A) h x (1 / 10000) (by norm_num) hj
  have hR : 0 ≤ metricScalarAt h x := by
    have hh := (abs_le.mp hs).1
    linarith
  obtain ⟨hF, hp, hD, hrel⟩ := hprofile (x : S2 × ℝ).2 x.property
  have hpD : |deriv conformalFactor (x : S2 × ℝ).2| ≤
      (1 / 10 : ℝ) * (-deriv (deriv conformalFactor) (x : S2 × ℝ).2) :=
    ((le_max_right _ _).trans hrel).trans
      (mul_le_mul_of_nonneg_right hηsmall (neg_nonneg.mpr hD.le))
  have hpabs : |deriv conformalFactor (x : S2 × ℝ).2| ≤ 1 / 10 := by
    have hh := norm_iteratedDeriv_le_intervalDerivativeNorm contDiff_conformalFactor
      (m := 2) (j := 1) (by norm_num)
      (show (x : S2 × ℝ).2 ∈ Icc (-A) 0 from ⟨x.property.1.le, x.property.2.le⟩)
    rw [iteratedDeriv_one, Real.norm_eq_abs] at hh
    exact (hh.trans hnorm.le).trans hηsmall
  have hp1 : |deriv conformalFactor (x : S2 × ℝ).2| ≤
      -deriv (deriv conformalFactor) (x : S2 × ℝ).2 := by linarith
  have hp2 : (deriv conformalFactor (x : S2 × ℝ).2) ^ 2 ≤
      -deriv (deriv conformalFactor) (x : S2 × ℝ).2 / 100 := by
    have hh := mul_le_mul hpabs hpD (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 10)
    nlinarith [sq_abs (deriv conformalFactor (x : S2 × ℝ).2)]
  exact scalar_conformal_improvement_of_parallel_unit_gradient
    (roundingReference A) h (fun y : roundingCollar A => (y : S2 × ℝ).2) (height_smooth A)
    conformalFactor contDiff_conformalFactor (by simp) x (1 / 10000) (by norm_num)
    (fun k hk => hj k (hk.trans (by norm_num))) (height_gradient_unit A x)
    (height_hessian_zero A x) hR hF.le hp1 hp2

end DifferentialGeometry.PDE.RicciFlow.StandardCap
