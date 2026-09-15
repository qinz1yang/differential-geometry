import DifferentialGeometry.Geometry.Connection.LeviCivita.AddCircle
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

namespace AddCircle

theorem gradientFun_parameterTangent
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f : AddCircle (1 : ℝ) → ℝ) (z : AddCircle (1 : ℝ)) :
    gradientFun g f z =
      ((show ℝ from mvfderiv 𝓘(ℝ, ℝ) f z (parameterTangent z)) /
        g.inner z (parameterTangent z) (parameterTangent z)) • parameterTangent z := by
  apply inner_parameterTangent_injective g z
  dsimp only
  rw [inner_gradientFun, map_smul, smul_apply]
  change _ = (_ / _) * _
  rw [div_mul_cancel₀ _ (parameterTangent_inner_pos g z).ne']

theorem divergence_parameterTangent
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (z : AddCircle (1 : ℝ)) :
    divergence (LeviCivita g) parameterTangent z =
      (show ℝ from mvfderiv 𝓘(ℝ, ℝ)
        (fun y => g.inner y (parameterTangent y) (parameterTangent y)) z
        (parameterTangent z)) / (2 * g.inner z (parameterTangent z) (parameterTangent z)) := by
  let q : AddCircle (1 : ℝ) → ℝ := fun y =>
    g.inner y (parameterTangent y) (parameterTangent y)
  have heq : ((LeviCivita g).toFun parameterTangent z).toLinearMap =
      (((2 * q z)⁻¹ • mvfderiv 𝓘(ℝ, ℝ) q z).toLinearMap).smulRight
        (parameterTangent z) := by
    apply LinearMap.ext
    intro v
    change (LeviCivita g).toFun parameterTangent z v = _
    rw [LeviCivita_parameterTangent]
    change (_ / (2 * q z)) • parameterTangent z =
      ((2 * q z)⁻¹ * _) • parameterTangent z
    rw [div_eq_mul_inv, mul_comm]
    rfl
  rw [divergence, heq, LinearMap.trace_smulRight]
  change (2 * q z)⁻¹ * _ = _ / (2 * q z)
  rw [div_eq_mul_inv, mul_comm]
  rfl

theorem laplacian_parameterTangent
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {f : AddCircle (1 : ℝ) → ℝ} {z : AddCircle (1 : ℝ)}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 f z) :
    laplacian (LeviCivita g) g f z =
      (g.inner z (parameterTangent z) (parameterTangent z))⁻¹ *
        (show ℝ from mvfderiv 𝓘(ℝ, ℝ)
          (fun y => mvfderiv 𝓘(ℝ, ℝ) f y (parameterTangent y)) z
          (parameterTangent z)) -
        (show ℝ from mvfderiv 𝓘(ℝ, ℝ)
          (fun y => g.inner y (parameterTangent y) (parameterTangent y)) z
          (parameterTangent z)) /
            (2 * (g.inner z (parameterTangent z) (parameterTangent z)) ^ 2) *
              (show ℝ from mvfderiv 𝓘(ℝ, ℝ) f z (parameterTangent z)) := by
  let q : AddCircle (1 : ℝ) → ℝ := fun y =>
    g.inner y (parameterTangent y) (parameterTangent y)
  let D : AddCircle (1 : ℝ) → ℝ := fun y =>
    mvfderiv 𝓘(ℝ, ℝ) f y (parameterTangent y)
  have hq : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) q z :=
    (contMDiff_parameterTangent_inner g).mdifferentiableAt (by decide)
  have hD : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) D z :=
    mdifferentiableAt_mfderiv_parameterTangent hf
  have hqne : q z ≠ 0 := (parameterTangent_inner_pos g z).ne'
  have hgrad : gradientFun g f = (D / q) • parameterTangent :=
    funext (gradientFun_parameterTangent g f)
  rw [laplacian, hgrad, divergence_smul (LeviCivita g) inferInstance (hD.div hq hqne)
    (contMDiff_parameterTangent.mdifferentiableAt (by decide)), divergence_parameterTangent]
  have hdiv : mvfderiv 𝓘(ℝ, ℝ) (D / q) z =
      (1 / q z) • mvfderiv 𝓘(ℝ, ℝ) D z - (D z / q z ^ 2) • mvfderiv 𝓘(ℝ, ℝ) q z :=
    (hD.hasMFDerivAt.div hq.hasMFDerivAt hqne).mfderiv
  change (D z / q z) * ((show ℝ from mvfderiv 𝓘(ℝ, ℝ) q z (parameterTangent z)) /
      (2 * q z)) + (show ℝ from mvfderiv 𝓘(ℝ, ℝ) (D / q) z (parameterTangent z)) = _
  rw [hdiv]
  change (D z / q z) * ((show ℝ from mvfderiv 𝓘(ℝ, ℝ) q z (parameterTangent z)) /
      (2 * q z)) + ((1 / q z) * (show ℝ from mvfderiv 𝓘(ℝ, ℝ) D z (parameterTangent z)) -
        (D z / q z ^ 2) * (show ℝ from mvfderiv 𝓘(ℝ, ℝ) q z (parameterTangent z))) =
    (q z)⁻¹ * (show ℝ from mvfderiv 𝓘(ℝ, ℝ) D z (parameterTangent z)) -
      (show ℝ from mvfderiv 𝓘(ℝ, ℝ) q z (parameterTangent z)) / (2 * q z ^ 2) * D z
  field_simp
  ring


theorem laplacian_coe
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {f : AddCircle (1 : ℝ) → ℝ} {x : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 f (x : AddCircle (1 : ℝ))) :
    laplacian (LeviCivita g) g f (x : AddCircle (1 : ℝ)) =
      (g.inner (x : AddCircle (1 : ℝ)) (parameterTangent (x : AddCircle (1 : ℝ)))
        (parameterTangent (x : AddCircle (1 : ℝ))))⁻¹ *
          deriv (deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ)))) x -
        deriv (fun t : ℝ => g.inner (t : AddCircle (1 : ℝ))
          (parameterTangent (t : AddCircle (1 : ℝ)))
          (parameterTangent (t : AddCircle (1 : ℝ)))) x /
            (2 * (g.inner (x : AddCircle (1 : ℝ)) (parameterTangent (x : AddCircle (1 : ℝ)))
              (parameterTangent (x : AddCircle (1 : ℝ)))) ^ 2) *
                deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ))) x := by
  rw [deriv_deriv_comp_coe_of_contMDiffAt hf,
    deriv_comp_coe ((contMDiff_parameterTangent_inner g).mdifferentiableAt (by decide)),
    deriv_comp_coe (hf.mdifferentiableAt (by decide))]
  exact laplacian_parameterTangent g hf

noncomputable def laplacianPrincipalCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ :=
  ⟨fun z => (metricCoefficient g z)⁻¹,
    (metricCoefficient g).contMDiff.inv₀ (fun z => (metricCoefficient_pos g z).ne')⟩

noncomputable def laplacianDriftCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ where
  val z := -(show ℝ from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (metricCoefficient g) z
    (parameterTangent z)) / (2 * metricCoefficient g z ^ 2)
  property := by
    have hD := contMDiff_mfderiv_parameterTangent (m := ∞)
      (metricCoefficient g).contMDiff (by simp) le_rfl
    exact hD.neg.div₀ (contMDiff_const.mul ((metricCoefficient g).contMDiff.pow 2))
      (fun z => mul_ne_zero two_ne_zero (pow_ne_zero 2 (metricCoefficient_pos g z).ne'))

theorem laplacianPrincipalCoefficient_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (z : AddCircle (1 : ℝ)) :
    laplacianPrincipalCoefficient g z = (metricCoefficient g z)⁻¹ := rfl

theorem laplacianDriftCoefficient_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (z : AddCircle (1 : ℝ)) :
    laplacianDriftCoefficient g z =
      -(show ℝ from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (metricCoefficient g) z
        (parameterTangent z)) / (2 * metricCoefficient g z ^ 2) := rfl

theorem laplacian_eq_principal_add_drift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {f : AddCircle (1 : ℝ) → ℝ} {z : AddCircle (1 : ℝ)}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 f z) :
    laplacian (LeviCivita g) g f z =
      laplacianPrincipalCoefficient g z *
        (show ℝ from mvfderiv 𝓘(ℝ, ℝ)
          (fun y => mvfderiv 𝓘(ℝ, ℝ) f y (parameterTangent y)) z (parameterTangent z)) +
      laplacianDriftCoefficient g z *
        (show ℝ from mvfderiv 𝓘(ℝ, ℝ) f z (parameterTangent z)) := by
  rw [laplacian_parameterTangent g hf, laplacianPrincipalCoefficient_apply,
    laplacianDriftCoefficient_apply]
  rw [neg_div, neg_mul, sub_eq_add_neg]
  rfl

theorem gradientFun_flatMetric (f : AddCircle (1 : ℝ) → ℝ) (z : AddCircle (1 : ℝ)) :
    gradientFun flatMetric f z =
      (show ℝ from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f z (parameterTangent z)) • parameterTangent z := by
  rw [gradientFun_parameterTangent, flatMetric_parameterTangent_unit, div_one]
  rfl

theorem laplacian_flatMetric
    {f : AddCircle (1 : ℝ) → ℝ} (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 f)
    (z : AddCircle (1 : ℝ)) :
    laplacian (LeviCivita flatMetric) flatMetric f z =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f y (parameterTangent y)) z (parameterTangent z) := by
  rw [laplacian_parameterTangent flatMetric (hf z)]
  have heq : (fun y => flatMetric.inner y (parameterTangent y) (parameterTangent y)) =
      fun _ => (1 : ℝ) := funext flatMetric_parameterTangent_unit
  rw [heq, mvfderiv_const, flatMetric_parameterTangent_unit]
  change 1⁻¹ * _ - (0 : ℝ) / (2 * 1 ^ 2) * _ = _
  simp only [inv_one, one_mul, zero_div, zero_mul, sub_zero]
  rfl

theorem laplacian_flatMetric_coe
    {f : AddCircle (1 : ℝ) → ℝ} (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 f) (x : ℝ) :
    laplacian (LeviCivita flatMetric) flatMetric f (x : AddCircle (1 : ℝ)) =
      deriv (deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ)))) x := by
  rw [laplacian_flatMetric hf]
  exact (deriv_deriv_comp_coe hf x).symm

end AddCircle
