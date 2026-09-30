import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation
import Mathlib.Tactic.Ring

namespace GC.MetricGeometry
open PointedBallApprox

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
variable {p : X} {q : Y} {o : Z} {ε j : ℝ}

noncomputable def commonSourceComparison
    (f : PointedBallApprox o p (4 * j + 4) ε)
    (g : PointedBallApprox o q (4 * j + 4) ε)
    (hj : 1 ≤ j) (hε : 10 * ε < j) : PointedBallApprox p q j (10 * ε) := by
  let rev := f.quasiInverse (s := 2 * j + 2) (by linarith [f.error_pos])
    (by linarith [f.error_pos])
  have h : 2 * (4 * ε + ε) = 10 * ε := by ring
  rw [← h]
  exact rev.comp g (by linarith) (by linarith) (by linarith [f.error_pos])

def identityApprox (p : X) {R ε : ℝ} (hε : 0 < ε) (hR : ε < R) :
    PointedBallApprox p p R ε where
  error_pos := hε
  error_lt_radius := hR
  toFun x := x.val
  basepoint := rfl
  distortion x x' := by simpa using hε
  coverage y hy := ⟨⟨y, by linarith⟩, by simpa using hε⟩

def realIdentity : PointedBallApprox (0 : ℝ) (0 : ℝ) 10 1 :=
  identityApprox (0 : ℝ) (by norm_num) (by norm_num)

def realRestriction : PointedBallApprox (0 : ℝ) (0 : ℝ) 3 2 := by
  simpa only [mul_one] using realIdentity.restrict (s := 3) (by norm_num) (by norm_num)

example : ∃ x : BallCarrier (0 : ℝ) 3, dist (1 : ℝ) (realRestriction.toFun x) < 2 :=
  realRestriction.coverage 1 (by norm_num [Real.dist_eq])

noncomputable def realCommonSource : PointedBallApprox (0 : ℝ) (0 : ℝ) 1 (1 / 10) := by
  have f := identityApprox (0 : ℝ) (R := 4 * 1 + 4) (ε := 1 / 100)
    (by norm_num) (by norm_num)
  convert commonSourceComparison (j := 1) f f (by norm_num) (by norm_num) using 1
  norm_num

theorem noApprox_atEqualRadius : ¬ Nonempty (PointedBallApprox (0 : ℝ) (0 : ℝ) 2 2) := by
  rintro ⟨f⟩
  exact (lt_irrefl (2 : ℝ)) f.error_lt_radius

end GC.MetricGeometry
