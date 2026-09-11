import DifferentialGeometry.Geometry.Measure.Area.ManifoldDensity
import Mathlib.LinearAlgebra.Complex.Determinant









noncomputable section

open Bundle Manifold DifferentialGeometry
open scoped InnerProductSpace Bundle Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem twoJacobian_changeOfFrame (v w : V) (a b c d : ℝ) :
    twoJacobian (a • v + b • w) (c • v + d • w) =
      |a * d - b * c| * twoJacobian v w := by
  unfold twoJacobian
  calc
    _ = Real.sqrt ((a * d - b * c) ^ 2 *
        (⟪v, v⟫_ℝ * ⟪w, w⟫_ℝ - ⟪v, w⟫_ℝ ^ 2)) := by
      congr 1
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right]
      rw [real_inner_comm w v]
      ring
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem complex_linearMap_det (A : ℂ →ₗ[ℝ] ℂ) :
    A.det = (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem tangentTwoJacobian_changeOfFrame (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) (a b c d : ℝ) :
    tangentTwoJacobian g (a • v + b • w) (c • v + d • w) =
      |a * d - b * c| * tangentTwoJacobian g v w := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact twoJacobian_changeOfFrame v w a b c d

theorem tangentTwoJacobian_comp_complex (g : SmoothRiemannianMetric I M) {x : M}
    (B : ℂ →L[ℝ] TangentSpace I x) (A : ℂ →L[ℝ] ℂ) :
    tangentTwoJacobian g (B (A 1)) (B (A Complex.I)) =
      |A.toLinearMap.det| * tangentTwoJacobian g (B 1) (B Complex.I) := by
  have hv (z : ℂ) : B z = z.re • B 1 + z.im • B Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    simp [Complex.real_smul, Complex.re_add_im]
  rw [hv (A 1), hv (A Complex.I), tangentTwoJacobian_changeOfFrame,
    complex_linearMap_det]
  simp only [ContinuousLinearMap.coe_coe, mul_comm]

set_option backward.isDefEq.respectTransparency false in


theorem riemannianAreaDensity_precomp (g : SmoothRiemannianMetric I M)
    {u : ℂ → M} {φ : ℂ → ℂ} {z : ℂ}
    (hu : MDifferentiableAt 𝓘(ℝ, ℂ) I u (φ z)) (hφ : DifferentiableAt ℝ φ z) :
    riemannianAreaDensity g (u ∘ φ) z =
      |(fderiv ℝ φ z).toLinearMap.det| * riemannianAreaDensity g u (φ z) := by
  unfold riemannianAreaDensity
  rw [mfderiv_comp z hu hφ.mdifferentiableAt, mfderiv_eq_fderiv]
  exact tangentTwoJacobian_comp_complex g _ _

end DifferentialGeometry.Geometry
