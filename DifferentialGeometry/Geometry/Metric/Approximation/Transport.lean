import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation

set_option autoImplicit false

namespace GC.MetricGeometry.PointedBallApprox

universe u v

variable {X : Type u} {Y : Type v} [oldX : MetricSpace X] [oldY : MetricSpace Y]
variable {p : X} {q : Y} {R ε η s : ℝ}

def enlargeError (f : PointedBallApprox p q R ε) (hεη : ε ≤ η) (hηR : η < R) :
    PointedBallApprox p q R η where
  error_pos := lt_of_lt_of_le f.error_pos hεη
  error_lt_radius := hηR
  toFun := f.toFun
  basepoint := f.basepoint
  distortion x x' := lt_of_lt_of_le (f.distortion x x') hεη
  coverage y hy := by
    obtain ⟨x, hx⟩ := f.coverage y (by linarith)
    exact ⟨x, lt_of_lt_of_le hx hεη⟩

def recenter (f : PointedBallApprox p q R ε) (a : X)
    (hs : 3 * ε < s) (hsR : dist a p + s ≤ R) :
    PointedBallApprox a (f.toFun ⟨a, by linarith [f.error_pos]⟩) s (3 * ε) where
  error_pos := by linarith [f.error_pos]
  error_lt_radius := hs
  toFun x := f.toFun ⟨x.val, by
    have h := dist_triangle x.val a p
    linarith [x.property]⟩
  basepoint := by rfl
  distortion x x' := by
    have h := f.distortion
      ⟨x.val, by linarith [dist_triangle x.val a p, x.property]⟩
      ⟨x'.val, by linarith [dist_triangle x'.val a p, x'.property]⟩
    dsimp at h ⊢
    linarith [f.error_pos]
  coverage y hy := by
    let aR : BallCarrier p R := ⟨a, by linarith [f.error_pos]⟩
    have ha := f.radial_upper aR
    have htri := dist_triangle y (f.toFun aR) q
    change dist y (f.toFun aR) ≤ s - 3 * ε at hy
    have hyR : dist y q ≤ R - ε := by
      dsimp only [aR] at ha
      linarith [f.error_pos]
    obtain ⟨x, hx⟩ := f.coverage y hyR
    have hdist := (abs_lt.mp (f.distortion x aR)).1
    have htri' := dist_triangle (f.toFun x) y (f.toFun aR)
    rw [dist_comm (f.toFun x) y] at htri'
    have hxs : dist x.val a ≤ s := by
      dsimp only [aR] at hdist
      linarith [f.error_pos]
    refine ⟨⟨x.val, hxs⟩, ?_⟩
    change dist y (f.toFun x) < 3 * ε
    linarith [f.error_pos]

def rescale (f : PointedBallApprox p q R ε) (c : ℝ) (hc : 0 < c)
    (mX : MetricSpace X) (mY : MetricSpace Y)
    (hX : ∀ x x' : X, @dist X mX.toDist x x' = c * @dist X oldX.toDist x x')
    (hY : ∀ y y' : Y, @dist Y mY.toDist y y' = c * @dist Y oldY.toDist y y') :
    @PointedBallApprox X Y mX mY p q (c * R) (c * ε) := by
  letI : MetricSpace X := oldX
  letI : MetricSpace Y := oldY
  let F : @BallCarrier X mX p (c * R) → Y := fun x => f.toFun ⟨x.val, by
    have hx := x.property
    rw [hX] at hx
    nlinarith⟩
  refine @PointedBallApprox.mk X Y mX mY p q (c * R) (c * ε)
    (mul_pos hc f.error_pos) (mul_lt_mul_of_pos_left f.error_lt_radius hc) F ?_ ?_ ?_
  · exact f.basepoint
  · intro x x'
    let xR : BallCarrier p R := ⟨x.val, by
      have hx := x.property
      rw [hX] at hx
      nlinarith⟩
    let xR' : BallCarrier p R := ⟨x'.val, by
      have hx := x'.property
      rw [hX] at hx
      nlinarith⟩
    change |@dist Y mY.toDist (f.toFun xR) (f.toFun xR') -
      @dist X mX.toDist x.val x'.val| < c * ε
    rw [hY, hX, ← mul_sub, abs_mul, abs_of_pos hc]
    exact mul_lt_mul_of_pos_left (f.distortion xR xR') hc
  · intro y hy
    have hy' : dist y q ≤ R - ε := by
      rw [hY, ← mul_sub] at hy
      nlinarith
    obtain ⟨x, hx⟩ := f.coverage y hy'
    have hxs : @dist X mX.toDist x.val p ≤ c * R := by
      rw [hX]
      exact mul_le_mul_of_nonneg_left x.property hc.le
    refine ⟨⟨x.val, hxs⟩, ?_⟩
    change @dist Y mY.toDist y (f.toFun x) < c * ε
    rw [hY]
    exact mul_lt_mul_of_pos_left hx hc

end GC.MetricGeometry.PointedBallApprox
