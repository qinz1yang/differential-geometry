import DifferentialGeometry.Geometry.Connection.LeviCivita.AlongCurve
import DifferentialGeometry.Geometry.Metric.AddCircle
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.DimensionOne
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection

namespace AddCircle

theorem LeviCivita_parameterTangent
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (z : AddCircle (1 : ℝ)) (v : TangentSpace 𝓘(ℝ, ℝ) z) :
    (LeviCivita g).toFun parameterTangent z v =
      ((show ℝ from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun y => g.inner y (parameterTangent y) (parameterTangent y)) z v) /
          (2 * g.inner z (parameterTangent z) (parameterTangent z))) •
            parameterTangent z := by
  exact (LeviCivita_isMetricCompatible g).covariantDerivative_eq_smul_of_finrank_eq_one
    (Module.finrank_self ℝ)
    (contMDiff_parameterTangent.mdifferentiableAt (by decide))
    (parameterTangent_ne_zero z) v

theorem LeviCivita_parameterTangent_eq_zero (z : AddCircle (1 : ℝ))
    (v : TangentSpace 𝓘(ℝ, ℝ) z) :
    (LeviCivita flatMetric).toFun parameterTangent z v = 0 := by
  rw [LeviCivita_parameterTangent]
  have heq : (fun y => flatMetric.inner y (parameterTangent y) (parameterTangent y)) =
      fun _ => (1 : ℝ) := funext flatMetric_parameterTangent_unit
  rw [heq, mfderiv_const]
  change ((0 : ℝ) / _) • parameterTangent z = 0
  rw [zero_div, zero_smul]

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

theorem covDerivAlong_parameterTangent_eq_zero {γ : ℝ → AddCircle (1 : ℝ)} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ t) :
    covDerivAlong flatMetric γ (fun s => parameterTangent (γ s)) t = 0 := by
  rw [← derivAlongWithin_leviCivita_eq_covDerivAlong flatMetric γ _
    (J := Set.univ) (by simp) hγ BoundarylessManifold.isInteriorPoint]
  rw [(LeviCivita flatMetric).derivAlongWithin_section hγ.mdifferentiableWithinAt
    (contMDiff_parameterTangent.mdifferentiableAt (by decide))]
  exact LeviCivita_parameterTangent_eq_zero _ _

theorem covDerivAlong_coe_parameterTangent_eq_zero (t : ℝ) :
    covDerivAlong flatMetric (fun s : ℝ => (s : AddCircle (1 : ℝ)))
      (fun s => parameterTangent (s : AddCircle (1 : ℝ))) t = 0 :=
  covDerivAlong_parameterTangent_eq_zero (contMDiff_coe.mdifferentiableAt (by decide))


end AddCircle
