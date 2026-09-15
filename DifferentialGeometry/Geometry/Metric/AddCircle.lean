import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Geometry.Metric.CompactExistence
import DifferentialGeometry.Geometry.Metric.Scaling

section

noncomputable section
open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

namespace AddCircle

private def auxiliaryMetric : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) :=
  Classical.choice (DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric_of_compact
    (I := 𝓘(ℝ, ℝ)))

theorem parameterTangent_inner_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (z : AddCircle (1 : ℝ)) :
    0 < g.inner z (parameterTangent z) (parameterTangent z) :=
  g.pos z _ (parameterTangent_ne_zero z)

theorem contMDiff_parameterTangent_inner
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun z => g.inner z (parameterTangent z) (parameterTangent z)) := by
  have hh := ContMDiff.clm_bundle_apply₂ (F₁ := ℝ) (F₂ := ℝ)
    g.contMDiff contMDiff_parameterTangent contMDiff_parameterTangent
  intro x
  have hx := hh x
  rw [contMDiffAt_totalSpace] at hx
  exact hx.2

noncomputable def metricCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ :=
  ⟨fun z => g.inner z (parameterTangent z) (parameterTangent z),
    contMDiff_parameterTangent_inner g⟩

theorem metricCoefficient_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (z : AddCircle (1 : ℝ)) :
    metricCoefficient g z = g.inner z (parameterTangent z) (parameterTangent z) := rfl

theorem metricCoefficient_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (z : AddCircle (1 : ℝ)) :
    0 < metricCoefficient g z := by
  exact parameterTangent_inner_pos g z

theorem inner_parameterTangent_injective
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (z : AddCircle (1 : ℝ)) :
    Function.Injective (fun v : TangentSpace 𝓘(ℝ, ℝ) z =>
      g.inner z v (parameterTangent z)) := by
  intro v w h
  change g.inner z v (parameterTangent z) = g.inner z w (parameterTangent z) at h
  apply sub_eq_zero.mp
  have hz : g.inner z (v - w) (parameterTangent z) = 0 := by
    rw [map_sub, sub_apply, h, sub_self]
  obtain ⟨a, ha⟩ := exists_smul_parameterTangent z (v - w)
  rw [← ha, map_smul, smul_apply] at hz
  change a * g.inner z (parameterTangent z) (parameterTangent z) = 0 at hz
  have ha0 : a = 0 := (mul_eq_zero.mp hz).resolve_right (parameterTangent_inner_pos g z).ne'
  rw [← ha, ha0, zero_smul]

def flatMetric : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) where
  inner z := (auxiliaryMetric.inner z (parameterTangent z) (parameterTangent z))⁻¹ •
    auxiliaryMetric.inner z
  symm z := (scaleMetric _ (inv_pos.mpr (parameterTangent_inner_pos auxiliaryMetric z)) auxiliaryMetric).symm z
  pos z := (scaleMetric _ (inv_pos.mpr (parameterTangent_inner_pos auxiliaryMetric z)) auxiliaryMetric).pos z
  isVonNBounded z := (scaleMetric _ (inv_pos.mpr (parameterTangent_inner_pos auxiliaryMetric z)) auxiliaryMetric).isVonNBounded z
  contMDiff := by
    have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun z => (auxiliaryMetric.inner z (parameterTangent z) (parameterTangent z))⁻¹) :=
      (contMDiff_parameterTangent_inner auxiliaryMetric).inv₀
        (fun z => (parameterTangent_inner_pos auxiliaryMetric z).ne')
    exact hs.smul_section auxiliaryMetric.contMDiff

theorem flatMetric_parameterTangent_unit (z : AddCircle (1 : ℝ)) :
    flatMetric.inner z (parameterTangent z) (parameterTangent z) = 1 := by
  change (auxiliaryMetric.inner z (parameterTangent z) (parameterTangent z))⁻¹ *
    auxiliaryMetric.inner z (parameterTangent z) (parameterTangent z) = 1
  exact inv_mul_cancel₀ (parameterTangent_inner_pos auxiliaryMetric z).ne'





theorem eq_flatMetric_of_parameterTangent_unit
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (h : ∀ z, g.inner z (parameterTangent z) (parameterTangent z) = 1) :
    g = flatMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  obtain ⟨a, rfl⟩ := exists_smul_parameterTangent z v
  obtain ⟨b, rfl⟩ := exists_smul_parameterTangent z w
  simp only [map_smul, smul_apply, smul_eq_mul, h, flatMetric_parameterTangent_unit]

set_option backward.isDefEq.respectTransparency false in
theorem flatMetric_inner_mfderiv_coe (x a b : ℝ) :
    flatMetric.inner (x : AddCircle (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) x a)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) x b) = a * b := by
  have ha : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) x a = a • parameterTangent (x : AddCircle (1 : ℝ)) := by
    rw [parameterTangent_coe, ← map_smul]
    congr 1
    change a = a * 1
    exact (mul_one a).symm
  have hb : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) x b = b • parameterTangent (x : AddCircle (1 : ℝ)) := by
    rw [parameterTangent_coe, ← map_smul]
    congr 1
    change b = b * 1
    exact (mul_one b).symm
  rw [ha, hb, (flatMetric.inner (x : AddCircle (1 : ℝ))).map_smul, smul_apply,
    (flatMetric.inner (x : AddCircle (1 : ℝ)) (parameterTangent (x : AddCircle (1 : ℝ)))).map_smul]
  change a * (b * _) = a * b
  rw [flatMetric_parameterTangent_unit, mul_one]

end AddCircle

end

end
