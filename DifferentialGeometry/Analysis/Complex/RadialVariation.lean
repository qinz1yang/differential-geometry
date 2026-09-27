import DifferentialGeometry.Topology.LoopSpace.RadialExtension
import DifferentialGeometry.Tensor.LinearAlgebra.PlanarBilinear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

noncomputable section

open MeasureTheory Set Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

def radialDiskStressCoefficient (ψ : ℝ → ℝ) (z : ℂ) (i j : Fin 2) : ℝ :=
  deriv ψ (Complex.arg z / (2 * Real.pi)) / 2 *
    ((Complex.orthonormalBasisOneI.repr (radialDirection z : ℂ)) i *
        (Complex.orthonormalBasisOneI.repr (radialDirection z : ℂ)) j -
      (Complex.orthonormalBasisOneI.repr (Complex.I * (radialDirection z : ℂ))) i *
        (Complex.orthonormalBasisOneI.repr (Complex.I * (radialDirection z : ℂ))) j)

theorem measurable_radialDiskStressCoefficient (ψ : ℝ → ℝ) (i j : Fin 2) :
    Measurable (fun z => radialDiskStressCoefficient ψ z i j) := by
  have hR (k : Fin 2) : Measurable (fun z : ℂ =>
      (Complex.orthonormalBasisOneI.repr (radialDirection z : ℂ)) k) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) k).measurable.comp
      (Complex.orthonormalBasisOneI.repr.continuous.measurable.comp
        measurable_coe_radialDirection)
  have hT (k : Fin 2) : Measurable (fun z : ℂ =>
      (Complex.orthonormalBasisOneI.repr (Complex.I * (radialDirection z : ℂ))) k) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) k).measurable.comp
      (Complex.orthonormalBasisOneI.repr.continuous.measurable.comp
        (measurable_coe_radialDirection.const_mul Complex.I))
  exact (((measurable_deriv ψ).comp
    (Complex.measurable_arg.div_const (2 * Real.pi))).div_const 2).mul
      ((hR i).mul (hR j) |>.sub ((hT i).mul (hT j)))

theorem norm_radialDiskStressCoefficient_le {ψ : ℝ → ℝ} {C : ℝ≥0}
    (hψ : LipschitzWith C ψ) (z : ℂ) (i j : Fin 2) :
    ‖radialDiskStressCoefficient ψ z i j‖ ≤ C := by
  let R := Complex.orthonormalBasisOneI.repr (radialDirection z : ℂ)
  let T := Complex.orthonormalBasisOneI.repr (Complex.I * (radialDirection z : ℂ))
  have hR (k : Fin 2) : |R k| ≤ 1 := by
    have h := PiLp.norm_apply_le R k
    simpa only [R, Real.norm_eq_abs, LinearIsometryEquiv.norm_map,
      Circle.norm_coe] using h
  have hT (k : Fin 2) : |T k| ≤ 1 := by
    have h := PiLp.norm_apply_le T k
    simpa only [T, Real.norm_eq_abs, LinearIsometryEquiv.norm_map,
      norm_mul, Complex.norm_I, Circle.norm_coe, one_mul] using h
  have hRmul : |R i * R j| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (R i), abs_nonneg (R j), hR i, hR j,
      mul_le_mul (hR i) (hR j) (abs_nonneg (R j)) (by norm_num)]
  have hTmul : |T i * T j| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (T i), abs_nonneg (T j), hT i, hT j,
      mul_le_mul (hT i) (hT j) (abs_nonneg (T j)) (by norm_num)]
  have hdiff : |R i * R j - T i * T j| ≤ 2 :=
    (abs_sub (R i * R j) (T i * T j)).trans (by linarith)
  have ha : |deriv ψ (Complex.arg z / (2 * Real.pi))| ≤ (C : ℝ) :=
    norm_deriv_le_of_lipschitz hψ
  change |deriv ψ (Complex.arg z / (2 * Real.pi)) / 2 *
    (R i * R j - T i * T j)| ≤ C
  rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ ((C : ℝ) / 2) * 2 :=
      mul_le_mul (div_le_div_of_nonneg_right ha (by norm_num)) hdiff
        (abs_nonneg _) (by positivity)
    _ = C := by ring

theorem radial_quadratic_variation_eq_sum (ψ : ℝ → ℝ) (z : ℂ)
    (Q : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :
    deriv ψ (Complex.arg z / (2 * Real.pi)) *
      (Q (radialDirection z) (radialDirection z) -
        Q (Complex.I * (radialDirection z : ℂ))
          (Complex.I * (radialDirection z : ℂ))) / 2 =
      ∑ i : Fin 2, ∑ j : Fin 2, radialDiskStressCoefficient ψ z i j *
        Q (Complex.orthonormalBasisOneI i) (Complex.orthonormalBasisOneI j) := by
  rw [bilinear_quadratic_sub_quarter_turn]
  simp only [Fin.sum_univ_two, radialDiskStressCoefficient,
    Complex.orthonormalBasisOneI_repr_apply, Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.I_mul_re, Complex.I_mul_im]
  ring

end DifferentialGeometry.Geometry

end
