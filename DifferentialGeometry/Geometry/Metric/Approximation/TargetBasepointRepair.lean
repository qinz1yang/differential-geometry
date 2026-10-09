import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.Transport

set_option autoImplicit false

namespace GC.MetricGeometry.PointedBallApprox

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {R ε η : ℝ}

noncomputable def repairTarget (f : PointedBallApprox p q R ε) (b : Y)
    (hη : 0 ≤ η) (hqb : dist q b ≤ η) (hE : ε + 2 * η < R) :
    PointedBallApprox p b R (ε + 2 * η) := by
  classical
  let G : BallCarrier p R → Y := fun x => if x.val = p then b else f.toFun x
  have hG (x : BallCarrier p R) : dist (G x) (f.toFun x) ≤ η := by
    dsimp only [G]
    split_ifs with hx
    · have hxp : x = ⟨p, by simpa using (f.error_pos.trans f.error_lt_radius).le⟩ := Subtype.ext hx
      rw [hxp, f.basepoint, dist_comm]
      exact hqb
    · simpa only [dist_self] using hη
  refine ⟨by linarith [f.error_pos], hE, G, ?_, ?_, ?_⟩
  · simp only [G, ite_true]
  · intro x y
    have hd := abs_lt.mp (f.distortion x y)
    have h₁ := dist_triangle4 (G x) (f.toFun x) (f.toFun y) (G y)
    have h₂ := dist_triangle4 (f.toFun x) (G x) (G y) (f.toFun y)
    rw [dist_comm (f.toFun y) (G y)] at h₁
    rw [dist_comm (f.toFun x) (G x)] at h₂
    exact abs_lt.mpr ⟨by linarith [hG x, hG y], by linarith [hG x, hG y]⟩
  · intro y hy
    have ht := dist_triangle y b q
    rw [dist_comm b q] at ht
    obtain ⟨x, hx⟩ := f.coverage y (by linarith)
    have ht' := dist_triangle y (f.toFun x) (G x)
    rw [dist_comm (f.toFun x) (G x)] at ht'
    exact ⟨x, by linarith [hG x]⟩

theorem repairTarget_apply_of_ne (f : PointedBallApprox p q R ε) (b : Y)
    (hη : 0 ≤ η) (hqb : dist q b ≤ η) (hE : ε + 2 * η < R)
    (x : BallCarrier p R) (hx : x.val ≠ p) :
    (f.repairTarget b hη hqb hE).toFun x = f.toFun x := by
  classical
  simp only [repairTarget, ite_eq_right hx]

theorem repairTarget_dist_le (f : PointedBallApprox p q R ε) (b : Y)
    (hη : 0 ≤ η) (hqb : dist q b ≤ η) (hE : ε + 2 * η < R)
    (x : BallCarrier p R) :
    dist ((f.repairTarget b hη hqb hE).toFun x) (f.toFun x) ≤ η := by
  by_cases hx : x.val = p
  · have hxp : x = ⟨p, by simpa using (f.error_pos.trans f.error_lt_radius).le⟩ := Subtype.ext hx
    rw [hxp, (f.repairTarget b hη hqb hE).basepoint, f.basepoint, dist_comm]
    exact hqb
  · rw [f.repairTarget_apply_of_ne b hη hqb hE x hx, dist_self]
    exact hη

end GC.MetricGeometry.PointedBallApprox
