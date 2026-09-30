import DifferentialGeometry.Geometry.Metric.Approximation.ProductApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.PerturbApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation

set_option autoImplicit false

namespace GC.MetricGeometry.PointedBallApprox

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {R ε τ : ℝ}

noncomputable def toKleinerLottOfSmallError (f : PointedBallApprox p q R ε)
    (hτ : 0 < τ) (hτone : τ < 1) (hR : τ⁻¹ ≤ R) (hε : 2 * ε ≤ τ) :
    KleinerLottApprox p q τ := by
  classical
  let F : X → Y := fun x => if hx : dist x p ≤ R then f.toFun ⟨x, hx⟩ else q
  have hF (x : X) (hx : dist x p ≤ R) : F x = f.toFun ⟨x, hx⟩ := by
    simp only [F, dite_eq_left hx]
  refine ⟨hτ, hτone, F, ?_, ?_, ?_⟩
  · rw [hF p (by simpa using (f.error_pos.trans f.error_lt_radius).le)]
    exact f.basepoint
  · intro x hx y hy
    have hxR : dist x p ≤ R := (Metric.mem_ball.mp hx).le.trans hR
    have hyR : dist y p ≤ R := (Metric.mem_ball.mp hy).le.trans hR
    rw [hF x hxR, hF y hyR]
    have hd := f.distortion ⟨x, hxR⟩ ⟨y, hyR⟩
    dsimp only at hd
    linarith [f.error_pos]
  · intro y hy
    obtain ⟨x, hx⟩ := f.coverage y (by linarith [f.error_pos])
    have hrad := f.radial_lower x
    have htri := dist_triangle (f.toFun x) y q
    rw [dist_comm (f.toFun x) y] at htri
    have hxs : dist x.val p < τ⁻¹ := by linarith
    have hm : f.toFun x ∈ F '' Metric.ball p τ⁻¹ := ⟨x.val, hxs, hF x.val x.property⟩
    exact (Metric.infDist_le_dist_of_mem hm).trans (by linarith [f.error_pos])

theorem toKleinerLottOfSmallError_apply (f : PointedBallApprox p q R ε)
    (hτ : 0 < τ) (hτone : τ < 1) (hR : τ⁻¹ ≤ R) (hε : 2 * ε ≤ τ)
    (x : X) (hx : dist x p ≤ R) :
    (f.toKleinerLottOfSmallError hτ hτone hR hε).toFun x = f.toFun ⟨x, hx⟩ := by
  classical
  simp only [toKleinerLottOfSmallError, dite_eq_left hx]

end GC.MetricGeometry.PointedBallApprox
