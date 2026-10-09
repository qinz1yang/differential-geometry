import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {R ε a : ℝ}

namespace PointedBallApprox

private theorem distortion_le_of_dist_bounds (ha : 0 ≤ a)
    (f : BallCarrier p R → Y)
    (hdist : ∀ x x' : BallCarrier p R,
      (1 - a) * dist x.val x'.val ≤ dist (f x) (f x') ∧
        dist (f x) (f x') ≤ (1 + a) * dist x.val x'.val)
    (x x' : BallCarrier p R) :
    |dist (f x) (f x') - dist x.val x'.val| ≤ 2 * a * R := by
  have htriangle := dist_triangle x.val p x'.val
  rw [dist_comm p x'.val] at htriangle
  have hdiam : dist x.val x'.val ≤ 2 * R := by
    linarith [x.property, x'.property]
  have hmul := mul_le_mul_of_nonneg_left hdiam ha
  obtain ⟨hlower, hupper⟩ := hdist x x'
  apply abs_le.mpr
  constructor <;> nlinarith

def ofBilipschitz (ha : a ∈ Set.Ico (0 : ℝ) 1)
    (hε : 0 < ε) (hεR : ε < R) (herror : 2 * a * R < ε)
    (f : BallCarrier p R → Y)
    (hbase : f ⟨p, by simpa using (le_of_lt (lt_trans hε hεR))⟩ = q)
    (hdist : ∀ x x' : BallCarrier p R,
      (1 - a) * dist x.val x'.val ≤ dist (f x) (f x') ∧
        dist (f x) (f x') ≤ (1 + a) * dist x.val x'.val)
    (hcoverage : ∀ y : Y, dist y q ≤ R - ε → ∃ x, dist y (f x) < ε) :
    PointedBallApprox p q R ε where
  error_pos := hε
  error_lt_radius := hεR
  toFun := f
  basepoint := hbase
  distortion x x' := (distortion_le_of_dist_bounds ha.1 f hdist x x').trans_lt herror
  coverage := hcoverage

def ofIsometryEquiv (e : X ≃ᵢ Y) (p : X) (hε : 0 < ε) (hεR : ε < R) :
    PointedBallApprox p (e p) R ε := by
  refine ofBilipschitz (a := 0) ⟨le_rfl, by norm_num⟩ hε hεR
    (by simpa using hε) (fun x => e x.val) rfl ?_ ?_
  · intro x x'
    simp only [e.dist_eq, sub_zero, add_zero, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  · intro y hy
    have hradial : dist (e.symm y) p = dist y (e p) := by
      calc
        dist (e.symm y) p = dist (e (e.symm y)) (e p) := (e.dist_eq _ _).symm
        _ = dist y (e p) := by rw [e.apply_symm_apply]
    have hx : dist (e.symm y) p ≤ R := by
      rw [hradial]
      exact hy.trans (sub_le_self R hε.le)
    refine ⟨⟨e.symm y, hx⟩, ?_⟩
    simpa using hε

end PointedBallApprox
end GC.MetricGeometry
