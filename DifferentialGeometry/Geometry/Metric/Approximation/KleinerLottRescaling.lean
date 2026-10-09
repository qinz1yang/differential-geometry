import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry.KleinerLottApprox

variable {X Y : Type*} [mX : MetricSpace X] [mY : MetricSpace Y]
variable {p : X} {q : Y} {ε δ c : ℝ}

def recenterRescale (f : KleinerLottApprox p q ε) (a : X) (hc : 0 < c)
    (hbudget : 3 * c * ε ≤ δ) (hδ : δ < 1)
    (hdomain : dist a p + δ⁻¹ / c + 2 * ε ≤ ε⁻¹) :
    @KleinerLottApprox X Y (mX.rescale c hc) (mY.rescale c hc) a (f.toFun a) δ := by
  have hε := f.error_pos
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hbudget
  have hi : 0 < δ⁻¹ / c := div_pos (inv_pos.mpr hδ0) hc
  have ha : a ∈ ball p ε⁻¹ := by change dist a p < _; linarith
  have hfa := (abs_le.mp (f.radial_error a ha)).2
  have hin (x : X) (hx : c * dist x a < δ⁻¹) : x ∈ ball p ε⁻¹ := by
    have hh : dist x a < δ⁻¹ / c := (lt_div_iff₀ hc).mpr (by nlinarith)
    have ht := dist_triangle x a p
    change dist x p < _
    linarith
  have hdist (x y : X) (hx : c * dist x a < δ⁻¹) (hy : c * dist y a < δ⁻¹) :
      |c * dist (f.toFun x) (f.toFun y) - c * dist x y| ≤ δ := by
    rw [← mul_sub, abs_mul, abs_of_pos hc]
    have hd := mul_le_mul_of_nonneg_left (f.distortion x (hin x hx) y (hin y hy)) hc.le
    nlinarith
  have hcover (y : Y) (hy : c * dist y (f.toFun a) < δ⁻¹ - δ) :
      ∃ x : X, c * dist x a < δ⁻¹ ∧ c * dist y (f.toFun x) ≤ δ := by
    have hy' : dist y (f.toFun a) < δ⁻¹ / c := by
      apply (lt_div_iff₀ hc).mpr
      nlinarith
    have htri := dist_triangle y (f.toFun a) q
    obtain ⟨x, hx, hd⟩ := f.coverage_witness y (by linarith)
    have herr := (abs_le.mp (f.distortion x hx a ha)).1
    have hxy := dist_triangle (f.toFun x) y (f.toFun a)
    rw [dist_comm (f.toFun x) y] at hxy
    refine ⟨x, ?_, ?_⟩
    · nlinarith [mul_lt_mul_of_pos_left hd hc, mul_le_mul_of_nonneg_left herr hc.le,
        mul_le_mul_of_nonneg_left hxy hc.le]
    · nlinarith [mul_lt_mul_of_pos_left hd hc]
  let F := f.toFun
  letI : MetricSpace X := mX.rescale c hc
  letI : MetricSpace Y := mY.rescale c hc
  refine ⟨hδ0, hδ, F, rfl, ?_, ?_⟩
  · exact fun x hx y hy => hdist x y hx hy
  · intro y hy
    obtain ⟨x, hx, hd⟩ := hcover y hy
    exact (infDist_le_dist_of_mem (show F x ∈ F '' ball a δ⁻¹ from
      ⟨x, hx, rfl⟩)).trans hd

@[simp] theorem recenterRescale_apply (f : KleinerLottApprox p q ε) (a : X) (hc : 0 < c)
    (hbudget : 3 * c * ε ≤ δ) (hδ : δ < 1)
    (hdomain : dist a p + δ⁻¹ / c + 2 * ε ≤ ε⁻¹) (x : X) :
    @KleinerLottApprox.toFun X Y (mX.rescale c hc) (mY.rescale c hc) a (f.toFun a) δ
      (f.recenterRescale a hc hbudget hδ hdomain) x = f.toFun x := rfl

end GC.MetricGeometry.KleinerLottApprox
