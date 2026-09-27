import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LaplacianCalculus
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Gradient



noncomputable section

open InnerProductSpace
open scoped ContDiff

namespace DifferentialGeometry.Analysis

private theorem partial_log {f : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hz : f z ≠ 0) (v : ℂ) :
    fderiv ℝ (fun q => Real.log (f q)) z v = fderiv ℝ f z v / f z := by
  rw [(hf.hasFDerivAt.log hz).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring




theorem laplacian_log_add {a b : ℂ → ℝ} {z : ℂ}
    (ha : ContDiffAt ℝ 2 a z) (hb : ContDiffAt ℝ 2 b z)
    (hapos : 0 < a z) (hbpos : 0 < b z) :
    Laplacian.laplacian (fun q => Real.log (a q + b q)) z =
      a z / (a z + b z) * Laplacian.laplacian (fun q => Real.log (a q)) z +
      b z / (a z + b z) * Laplacian.laplacian (fun q => Real.log (b q)) z +
      (a z * b z / (a z + b z) ^ 2) *
        ‖gradient (fun q => Real.log (a q)) z - gradient (fun q => Real.log (b q)) z‖ ^ 2 := by
  have ha0 := hapos.ne'
  have hb0 := hbpos.ne'
  have hab0 := (add_pos hapos hbpos).ne'
  rw [laplacian_log (ha.add hb) hab0, laplacian_log ha ha0, laplacian_log hb hb0,
    norm_gradient_sub_complex_sq]
  erw [ha.laplacian_add hb, fderiv_fun_add (ha.differentiableAt (by norm_num))
    (hb.differentiableAt (by norm_num))]
  simp only [_root_.add_apply, partial_log (ha.differentiableAt (by norm_num)) ha0,
    partial_log (hb.differentiableAt (by norm_num)) hb0]
  field_simp
  ring




theorem neg_half_laplacian_log_add_le {a b : ℂ → ℝ} {z : ℂ}
    (ha : ContDiffAt ℝ 2 a z) (hb : ContDiffAt ℝ 2 b z)
    (hapos : 0 < a z) (hbpos : 0 < b z) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (a q + b q)) z ≤
      a z / (a z + b z) * (-(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (a q)) z) +
      b z / (a z + b z) * (-(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (b q)) z) := by
  rw [laplacian_log_add ha hb hapos hbpos]
  have hn : 0 ≤ (a z * b z / (a z + b z) ^ 2) *
      ‖gradient (fun q => Real.log (a q)) z - gradient (fun q => Real.log (b q)) z‖ ^ 2 := by
    positivity
  linarith

end DifferentialGeometry.Analysis
