import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section

open Bundle Manifold Metric Set Module
open scoped Manifold ContDiff RealInnerProductSpace ENNReal Topology

namespace DifferentialGeometry.Geometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {v : E3}

noncomputable def sphereGraphMap (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (y : E2) : E3 :=
  (R y : E3) + Real.sqrt (1 - ‖y‖ ^ 2) • v

noncomputable def sphereGraphCLM (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) : E2 →L[ℝ] E3 :=
  (Submodule.subtypeL (ℝ ∙ v)ᗮ).comp R.toContinuousLinearMap

theorem sphereGraphMap_inner_base (hv : ‖v‖ = 1) (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (y : E2) :
    ⟪sphereGraphMap R y, v⟫ = Real.sqrt (1 - ‖y‖ ^ 2) := by
  have h0 : ⟪(R y : E3), v⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (R y).property
  rw [sphereGraphMap, inner_add_left, h0, zero_add, real_inner_smul_left,
    real_inner_self_eq_norm_mul_norm, hv]
  ring

theorem sphereGraphMap_norm_sq (hv : ‖v‖ = 1) (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    (y : E2) (hy : ‖y‖ ≤ 1) : ‖sphereGraphMap R y‖ ^ 2 = 1 := by
  have h0 : ⟪(R y : E3), v⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (R y).property
  have hnorm : ‖(R y : E3)‖ = ‖y‖ := by
    rw [← Submodule.coe_norm, R.norm_map]
  have h1 : 0 ≤ 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have horth : ⟪(R y : E3), Real.sqrt (1 - ‖y‖ ^ 2) • v⟫ = 0 := by
    rw [real_inner_smul_right, h0, mul_zero]
  have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (R y : E3)
    (Real.sqrt (1 - ‖y‖ ^ 2) • v) horth
  have h3 : ‖(R y : E3) + Real.sqrt (1 - ‖y‖ ^ 2) • v‖ ^ 2 =
      ‖(R y : E3)‖ ^ 2 + ‖Real.sqrt (1 - ‖y‖ ^ 2) • v‖ ^ 2 := by nlinarith [h2]
  rw [sphereGraphMap, h3, hnorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    hv, mul_one, Real.sq_sqrt h1]
  ring

theorem hasFDerivAt_sphereGraphMap (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {y : E2} (hy : ‖y‖ < 1) :
    HasFDerivAt (sphereGraphMap (v := v) R)
      (sphereGraphCLM (v := v) R +
        (((1 / (2 * Real.sqrt (1 - ‖y‖ ^ 2))) • (-(2 • innerSL ℝ y))).smulRight v)) y := by
  have h1 : ‖y‖ ^ 2 < 1 := by nlinarith [hy, norm_nonneg y]
  have hne : 1 - ‖y‖ ^ 2 ≠ 0 := by nlinarith
  have hbase : HasFDerivAt (fun y : E2 => 1 - ‖y‖ ^ 2) (-(2 • innerSL ℝ y)) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_sub 1
  have hsqrt := hbase.sqrt hne
  have hsmul : HasFDerivAt (fun y : E2 => Real.sqrt (1 - ‖y‖ ^ 2) • v)
      (((1 / (2 * Real.sqrt (1 - ‖y‖ ^ 2))) • (-(2 • innerSL ℝ y))).smulRight v) y :=
    hsqrt.smul_const v
  exact (ContinuousLinearMap.hasFDerivAt (sphereGraphCLM (v := v) R)).add hsmul

theorem fderiv_sphereGraphMap_apply (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {y : E2} (hy : ‖y‖ < 1) (z : E2) :
    fderiv ℝ (sphereGraphMap (v := v) R) y z =
      (R z : E3) + (-(⟪y, z⟫ / Real.sqrt (1 - ‖y‖ ^ 2))) • v := by
  rw [(hasFDerivAt_sphereGraphMap (v := v) R hy).fderiv]
  have hφpos : 0 < Real.sqrt (1 - ‖y‖ ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [norm_nonneg y])
  have hscalar : (1 / (2 * Real.sqrt (1 - ‖y‖ ^ 2))) • (-(2 • ⟪y, z⟫)) =
      -(⟪y, z⟫ / Real.sqrt (1 - ‖y‖ ^ 2)) := by
    rw [smul_eq_mul, nsmul_eq_mul]
    field_simp
    ring
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, neg_apply,
    sphereGraphCLM, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    innerSL_apply_apply]
  change (R z : E3) + ((1 / (2 * Real.sqrt (1 - ‖y‖ ^ 2))) • (-(2 • ⟪y, z⟫))) • v =
    (R z : E3) + (-(⟪y, z⟫ / Real.sqrt (1 - ‖y‖ ^ 2))) • v
  rw [hscalar]


section GraphGram

noncomputable def chartModelBasisTwo : Module.Basis (Fin 2) ℝ E2 :=
  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2).reindex
    (finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)))

noncomputable def sphereGraphGram : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => ⟪(chartModelBasisTwo i : E2), (chartModelBasisTwo j : E2)⟫

theorem sphereGraphGram_one_zero : sphereGraphGram 1 0 = sphereGraphGram 0 1 := by
  simp only [sphereGraphGram, Matrix.of_apply, real_inner_comm]

theorem inner_fderiv_sphereGraphMap (hv : ‖v‖ = 1) (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {y : E2} (hy : ‖y‖ < 1) (z z' : E2) :
    ⟪fderiv ℝ (sphereGraphMap (v := v) R) y z,
        fderiv ℝ (sphereGraphMap (v := v) R) y z'⟫ =
      ⟪z, z'⟫ + (⟪y, z⟫ * ⟪y, z'⟫) / (1 - ‖y‖ ^ 2) := by
  have h0z : ⟪(R z : E3), v⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (R z).property
  have h1z : ⟪v, (R z : E3)⟫ = 0 := by rw [real_inner_comm, h0z]
  have h0z' : ⟪(R z' : E3), v⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (R z').property
  have h1z' : ⟪v, (R z' : E3)⟫ = 0 := by rw [real_inner_comm, h0z']
  have hRR : ⟪(R z : E3), (R z' : E3)⟫ = ⟪z, z'⟫ := by
    rw [← Submodule.coe_inner (𝕜 := ℝ) (W := (ℝ ∙ v)ᗮ) (R z) (R z')]
    exact R.inner_map_map z z'
  rw [fderiv_sphereGraphMap_apply (v := v) R hy z,
    fderiv_sphereGraphMap_apply (v := v) R hy z']
  have hsq : 0 ≤ 1 - ‖y‖ ^ 2 := by nlinarith [hy, norm_nonneg y]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    h0z, h1z', hRR, real_inner_self_eq_norm_mul_norm, hv, mul_one, mul_zero,
    zero_add]
  rw [div_eq_mul_inv]
  field_simp
  rw [Real.sq_sqrt hsq]
  ring

theorem inner_y_chartBasis (y : E2) (i : Fin 2) :
    ⟪y, (chartModelBasisTwo i : E2)⟫ =
      sphereGraphGram 0 i * (chartModelBasisTwo.repr y 0) +
        sphereGraphGram 1 i * (chartModelBasisTwo.repr y 1) := by
  conv_lhs => rw [← chartModelBasisTwo.sum_repr y]
  rw [Fin.sum_univ_two, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  simp only [sphereGraphGram, Matrix.of_apply]
  ring

theorem norm_sq_eq_chart (y : E2) :
    ‖y‖ ^ 2 = sphereGraphGram 0 0 * (chartModelBasisTwo.repr y 0) ^ 2 +
      (sphereGraphGram 0 1 + sphereGraphGram 1 0) *
        (chartModelBasisTwo.repr y 0 * chartModelBasisTwo.repr y 1) +
      sphereGraphGram 1 1 * (chartModelBasisTwo.repr y 1) ^ 2 := by
  set c : Fin 2 → ℝ := fun i => chartModelBasisTwo.repr y i with hc
  have hdecomp : y = ∑ i, c i • (chartModelBasisTwo i : E2) :=
    (chartModelBasisTwo.sum_repr y).symm
  have h : ‖y‖ ^ 2 = ⟪y, y⟫ := by
    rw [real_inner_self_eq_norm_mul_norm]; ring
  conv_lhs => rw [h, hdecomp]
  simp only [Fin.sum_univ_two, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  simp only [sphereGraphGram, Matrix.of_apply, hc]
  ring

theorem sphereGraphGram_matrix_eq (hv : ‖v‖ = 1) (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {y : E2} (hy : ‖y‖ < 1) :
    (Matrix.of fun i j => ⟪fderiv ℝ (sphereGraphMap (v := v) R) y (chartModelBasisTwo i),
        fderiv ℝ (sphereGraphMap (v := v) R) y (chartModelBasisTwo j)⟫) =
      sphereGraphGram + (1 - ‖y‖ ^ 2)⁻¹ •
        Matrix.vecMulVec (fun i => ⟪y, (chartModelBasisTwo i : E2)⟫)
          (fun i => ⟪y, (chartModelBasisTwo i : E2)⟫) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.of_apply]
  rw [inner_fderiv_sphereGraphMap hv R hy, sphereGraphGram, Matrix.of_apply]
  rw [div_eq_mul_inv]
  ring

end GraphGram

end DifferentialGeometry.Geometry
