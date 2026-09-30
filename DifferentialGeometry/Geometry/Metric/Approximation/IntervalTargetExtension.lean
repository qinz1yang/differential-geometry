import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry.KleinerLottApprox

variable {X : Type*} [MetricSpace X] {p : X} {C L s : ℝ}

def enlargeIntervalTarget (hC : 0 ≤ C)
    (f : KleinerLottApprox p (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hCL : C ≤ L) (hLC : L ≤ C + s) (hs : s < 1 / 4) :
    KleinerLottApprox p (⟨0, le_rfl, hC.trans hCL⟩ : Icc (0 : ℝ) L) (4 * s) := by
  have hs0 := f.error_pos
  have hsi : (4 * s)⁻¹ < s⁻¹ := by
    apply (inv_lt_inv₀ (by positivity : 0 < 4 * s) hs0).mpr
    linarith
  let F : X → Icc (0 : ℝ) L := fun x => ⟨(f.toFun x).val,
    (f.toFun x).property.1, (f.toFun x).property.2.trans hCL⟩
  refine ⟨by positivity, by linarith, F, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change (f.toFun p).val = 0
    rw [f.basepoint]
  · intro x hx x' hx'
    have hd := f.distortion x (hx.trans hsi) x' (hx'.trans hsi)
    change |dist (f.toFun x).val (f.toFun x').val - dist x x'| ≤ 4 * s
    exact hd.trans (by linarith)
  · intro y hy
    have hyr : (y : ℝ) < (4 * s)⁻¹ - 4 * s := by
      simpa only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg y.property.1] using hy
    let y₀ : Icc (0 : ℝ) C := ⟨min y.val C, le_min y.property.1 hC, min_le_right _ _⟩
    have hy₀ : dist y₀ (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) = min y.val C := by
      rw [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg y₀.property.1]
    have hy₀y : min y.val C ≤ y.val := min_le_left _ _
    obtain ⟨x, hx, hd⟩ := f.coverage_witness y₀ (by rw [hy₀]; linarith)
    have hxr : dist x p < min y.val C + 3 * s := by
      have hr := (abs_le.mp (f.radial_error x hx)).1
      have ht := dist_triangle (f.toFun x) y₀ (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C)
      rw [hy₀, dist_comm (f.toFun x) y₀] at ht
      linarith
    have hxin : x ∈ ball p (4 * s)⁻¹ := by change dist x p < _; linarith
    have hdiff : dist y.val (min y.val C) ≤ s := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy₀y)]
      by_cases h : y.val ≤ C
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right (le_of_not_ge h)]
        linarith [y.property.2]
    have hdist : dist y (F x) < 4 * s := by
      have ht := dist_triangle y.val (min y.val C) (f.toFun x).val
      change dist y.val (f.toFun x).val < _
      change dist (min y.val C) (f.toFun x).val < 2 * s at hd
      linarith
    exact (infDist_le_dist_of_mem (show F x ∈ F '' ball p (4 * s)⁻¹ from ⟨x, hxin, rfl⟩)).trans hdist.le

@[simp] theorem enlargeIntervalTarget_apply (hC : 0 ≤ C)
    (f : KleinerLottApprox p (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hCL : C ≤ L) (hLC : L ≤ C + s) (hs : s < 1 / 4) (x : X) :
    ((f.enlargeIntervalTarget hC hCL hLC hs).toFun x : ℝ) = (f.toFun x : ℝ) := rfl

end GC.MetricGeometry.KleinerLottApprox
