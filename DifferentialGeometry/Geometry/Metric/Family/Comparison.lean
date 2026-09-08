import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Manifold Set
open scoped ContDiff Manifold ENNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem inner_le_exp_mul_inner_of_abs_deriv_le
    (g : ℝ → SmoothRiemannianMetric I M) {a b K s t : ℝ}
    (hderiv : ∀ r ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      ∃ d : ℝ, HasDerivWithinAt (fun u => (g u).inner x v v) d (Icc a b) r ∧
        |d| ≤ K * (g r).inner x v v)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : M) (v : TangentSpace I x) :
    (g s).inner x v v ≤ Real.exp (K * |s - t|) * (g t).inner x v v := by
  classical
  by_cases hst : s = t
  · subst s
    simp only [sub_self, abs_zero, mul_zero, Real.exp_zero, one_mul, le_refl]
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [map_zero, mul_zero, le_refl]
  have hpos (r : ℝ) : 0 < (g r).inner x v v := (g r).pos x v hv
  choose d hd hbound using fun r hr => hderiv r hr x v
  let f' : ℝ → ℝ := fun r => if hr : r ∈ Icc a b then d r hr / (g r).inner x v v else 0
  have hlogderiv (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt (fun u => Real.log ((g u).inner x v v))
        (f' r) (Icc a b) r := by
    simpa only [f', dif_pos hr] using (hd r hr).log (hpos r).ne'
  have hlogbound (r : ℝ) (hr : r ∈ Icc a b) : ‖f' r‖ ≤ K := by
    dsimp only [f']
    rw [dif_pos hr]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos r), div_le_iff₀ (hpos r)]
    exact hbound r hr
  have hlog := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    hlogderiv hlogbound ht hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hlog
  have hle : Real.log ((g s).inner x v v) ≤
      K * |s - t| + Real.log ((g t).inner x v v) := by
    linarith [le_abs_self (Real.log ((g s).inner x v v) - Real.log ((g t).inner x v v))]
  calc
    (g s).inner x v v = Real.exp (Real.log ((g s).inner x v v)) :=
      (Real.exp_log (hpos s)).symm
    _ ≤ Real.exp (K * |s - t| + Real.log ((g t).inner x v v)) :=
      Real.exp_le_exp.mpr hle
    _ = Real.exp (K * |s - t|) * (g t).inner x v v := by
      rw [Real.exp_add, Real.exp_log (hpos t)]

theorem riemannianEDistOf_le_exp_mul_of_abs_deriv_le
    (g : ℝ → SmoothRiemannianMetric I M) {a b K s t : ℝ}
    (hderiv : ∀ r ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      ∃ d : ℝ, HasDerivWithinAt (fun u => (g u).inner x v v) d (Icc a b) r ∧
        |d| ≤ K * (g r).inner x v v)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x y : M) :
    riemannianEDistOf (g s) x y ≤
      ENNReal.ofReal (Real.exp ((K / 2) * |s - t|)) * riemannianEDistOf (g t) x y := by
  have h := edistOf_le_of_quad (g t) (g s) (Real.exp_pos (K * |s - t|))
    (inner_le_exp_mul_inner_of_abs_deriv_le g hderiv hs ht) x y
  rw [← Real.exp_half, show K * |s - t| / 2 = (K / 2) * |s - t| by ring] at h
  exact h

end DifferentialGeometry
