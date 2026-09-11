import DifferentialGeometry.Geometry.Metric.RadialCurvature
import DifferentialGeometry.Geometry.Metric.RadialFrame
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.ReactionTensor
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold InnerProductSpace Topology ContDiff
namespace DifferentialGeometry.Geometry.Riemannian
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem radial_components
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) E3) {a : ℝ → ℝ} {x : E3}
    (hg : (fun y => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 x]
      radialBilinearField a)
    (ha : ContDiff ℝ ∞ a) (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0)
    (b : OrthonormalBasis (Fin 3) ℝ E3) (hb : b 0 = NormedSpace.normalize x)
    (i j k l : Fin 3) :
    metricRm04StandardAt (I := 𝓘(ℝ, E3)) g x
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E3)) x).symm (b i))
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E3)) x).symm (b j))
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E3)) x).symm (b k))
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E3)) x).symm (b l)) =
      Dim3Reaction.rm (Dim3Reaction.ricciFromSectional3
        (-a ‖x‖ * deriv (deriv a) ‖x‖ / ‖x‖ ^ 2)
        (-a ‖x‖ * deriv (deriv a) ‖x‖ / ‖x‖ ^ 2)
        (a ‖x‖ ^ 2 * (1 - deriv a ‖x‖ ^ 2) / ‖x‖ ^ 4)) i j k l := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [metricRm04StdAt_radialBilinearField g hg ha hx hane]
  generalize -a ‖x‖ * deriv (deriv a) ‖x‖ / ‖x‖ ^ 2 = R
  generalize a ‖x‖ ^ 2 * (1 - deriv a ‖x‖ ^ 2) / ‖x‖ ^ 4 = T
  simp only [b.inner_eq_ite, inner_radial_orthonormalBasis b hb]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Dim3Reaction.rm, Dim3Reaction.ricciFromSectional3, Dim3Reaction.sc,
      Dim3Reaction.kd] <;> field_simp <;> ring

theorem metricAlgebraicCurvatureTensorAt_radialBilinearField_nonnegative
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) E3) {a : ℝ → ℝ} {x : E3}
    (hg : (fun y => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 x]
      radialBilinearField a)
    (ha : ContDiff ℝ ∞ a) (hx : x ≠ 0) (hapos : 0 < a ‖x‖)
    (hconc : deriv (deriv a) ‖x‖ ≤ 0) (hslope : |deriv a ‖x‖| ≤ 1) :
    metricAlgebraicCurvatureTensorAt (I := 𝓘(ℝ, E3)) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := 𝓘(ℝ, E3)) (M := E3) := by
  obtain ⟨b, hb⟩ := exists_radial_orthonormalBasis hx
  let B : Module.Basis (Fin 3) ℝ (TangentSpace 𝓘(ℝ, E3) x) :=
    b.toBasis.map (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E3)) x).symm.toLinearEquiv
  have hR : 0 ≤ -a ‖x‖ * deriv (deriv a) ‖x‖ / ‖x‖ ^ 2 :=
    div_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hapos.le) hconc) (sq_nonneg _)
  have hT : 0 ≤ a ‖x‖ ^ 2 * (1 - deriv a ‖x‖ ^ 2) / ‖x‖ ^ 4 :=
    div_nonneg (mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr hslope))) (by positivity)
  apply algebraicCurvatureOperatorNonnegative_of_components_eq_rm B
    (metricAlgebraicCurvatureTensorAt (I := 𝓘(ℝ, E3)) g x) _ _ _ hR hR hT
  intro i j k l
  change metricRm04StandardAt g x (B i) (B j) (B k) (B l) = _
  simpa only [B, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
    ContinuousLinearEquiv.coe_toLinearEquiv] using
    radial_components g hg ha hx hapos.ne' b hb i j k l

private theorem metric_gram_isAlgCurvForm
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) E3) (x : E3) (K : ℝ) :
    IsAlgCurvForm (fun u v w z : TangentSpace 𝓘(ℝ, E3) x =>
      K * (g.inner x u z * g.inner x v w - g.inner x u w * g.inner x v z)) where
  add_left := by
    intro u u' v w z
    simp only [map_add, add_apply]
    ring
  smul_left := by
    intro c u v w z
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  anti_first := by intros; ring
  anti_last := by intros; ring
  bianchi := by
    intro u v w z
    simp only [g.symm x]
    ring

theorem metricAlgebraicCurvatureTensorAt_nonnegative_of_constant_sectional_numerator
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) E3) (x : E3) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ u v : TangentSpace 𝓘(ℝ, E3) x,
      metricRm04StandardAt g x u v v u =
        K * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)) :
    metricAlgebraicCurvatureTensorAt (I := 𝓘(ℝ, E3)) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := 𝓘(ℝ, E3)) (M := E3) := by
  have hAlg : IsAlgCurvForm (fun u v w z : TangentSpace 𝓘(ℝ, E3) x =>
      metricRm04StandardAt g x u v w z) :=
    mem_algebraicCurvatureTensorSubmodule.mp (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
  have hfull := hAlg.ext (metric_gram_isAlgCurvForm g x K) (by
    intro u v
    rw [hAlg.anti_last u v u v, hsec u v]
    rw [g.symm x v u]
    ring)
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, E3) x) = 3 := by
    change Module.finrank ℝ E3 = 3
    simp
  obtain ⟨B0, hB0⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g x
  let e : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, E3) x)) ≃ Fin 3 := finCongr hdim
  let B : Module.Basis (Fin 3) ℝ (TangentSpace 𝓘(ℝ, E3) x) := B0.reindex e
  have hB (i j : Fin 3) : g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := by
    dsimp only [B]
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hB0]
    simp only [Equiv.apply_eq_iff_eq]
  apply algebraicCurvatureOperatorNonnegative_of_components_eq_rm B
    (metricAlgebraicCurvatureTensorAt (I := 𝓘(ℝ, E3)) g x) K K K hK hK hK
  intro i j k l
  change metricRm04StandardAt g x (B i) (B j) (B k) (B l) = _
  rw [hfull]
  simp only [hB]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Dim3Reaction.rm, Dim3Reaction.ricciFromSectional3, Dim3Reaction.sc,
      Dim3Reaction.kd] <;> ring

end DifferentialGeometry.Geometry.Riemannian
