import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

namespace GC.MetricGeometry

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

abbrev BallCarrier (p : X) (R : ℝ) := {x : X // dist x p ≤ R}

structure PointedBallApprox (p : X) (q : Y) (R ε : ℝ) where
  error_pos : 0 < ε
  error_lt_radius : ε < R
  toFun : BallCarrier p R → Y
  basepoint : toFun ⟨p, by simpa using (le_of_lt (lt_trans error_pos error_lt_radius))⟩ = q
  distortion : ∀ x x', |dist (toFun x) (toFun x') - dist x.val x'.val| < ε
  coverage : ∀ y : Y, dist y q ≤ R - ε → ∃ x, dist y (toFun x) < ε

namespace PointedBallApprox

variable {p : X} {q : Y} {z : Z} {R S ε η s : ℝ}

theorem radial_error (f : PointedBallApprox p q R ε) (x : BallCarrier p R) :
    |dist (f.toFun x) q - dist x.val p| < ε := by
  simpa only [f.basepoint] using f.distortion x
    ⟨p, by simpa using (le_of_lt (lt_trans f.error_pos f.error_lt_radius))⟩

theorem radial_upper (f : PointedBallApprox p q R ε) (x : BallCarrier p R) :
    dist (f.toFun x) q < dist x.val p + ε := by
  have := (abs_lt.mp (f.radial_error x)).2
  linarith

theorem radial_lower (f : PointedBallApprox p q R ε) (x : BallCarrier p R) :
    dist x.val p < dist (f.toFun x) q + ε := by
  have := (abs_lt.mp (f.radial_error x)).1
  linarith

def restrict (f : PointedBallApprox p q R ε) (hs : 2 * ε < s) (hsR : s ≤ R) :
    PointedBallApprox p q s (2 * ε) where
  error_pos := by linarith [f.error_pos]
  error_lt_radius := hs
  toFun x := f.toFun ⟨x.val, le_trans x.property hsR⟩
  basepoint := f.basepoint
  distortion x x' := by
    have h := f.distortion ⟨x.val, le_trans x.property hsR⟩
      ⟨x'.val, le_trans x'.property hsR⟩
    dsimp at h ⊢
    linarith [f.error_pos]
  coverage y hy := by
    obtain ⟨x, hx⟩ := f.coverage y (by linarith [f.error_pos])
    have hrad := f.radial_lower x
    have htri := dist_triangle (f.toFun x) y q
    rw [dist_comm (f.toFun x) y] at htri
    have hxs : dist x.val p ≤ s := by linarith
    refine ⟨⟨x.val, hxs⟩, ?_⟩
    change dist y (f.toFun x) < 2 * ε
    linarith [f.error_pos]

theorem image_mem (f : PointedBallApprox p q R ε) (hsR : s ≤ R)
    (hsS : s + ε ≤ S) (x : BallCarrier p s) :
    dist (f.toFun ⟨x.val, le_trans x.property hsR⟩) q ≤ S := by
  have h := f.radial_upper ⟨x.val, le_trans x.property hsR⟩
  dsimp at h
  linarith [x.property]

def comp (f : PointedBallApprox p q R ε) (g : PointedBallApprox q z S η)
    (hs : 2 * (ε + η) < s) (hsR : s ≤ R) (hsS : s + ε ≤ S) :
    PointedBallApprox p z s (2 * (ε + η)) where
  error_pos := by linarith [f.error_pos, g.error_pos]
  error_lt_radius := hs
  toFun x := g.toFun ⟨f.toFun ⟨x.val, le_trans x.property hsR⟩, f.image_mem hsR hsS x⟩
  basepoint := by
    convert g.basepoint using 1
    apply congrArg g.toFun
    apply Subtype.ext
    exact f.basepoint
  distortion x x' := by
    have hf := abs_lt.mp (f.distortion ⟨x.val, le_trans x.property hsR⟩
      ⟨x'.val, le_trans x'.property hsR⟩)
    have hg := abs_lt.mp (g.distortion
      ⟨f.toFun ⟨x.val, le_trans x.property hsR⟩, f.image_mem hsR hsS x⟩
      ⟨f.toFun ⟨x'.val, le_trans x'.property hsR⟩, f.image_mem hsR hsS x'⟩)
    dsimp at hf hg ⊢
    apply abs_lt.mpr
    constructor <;> linarith [f.error_pos, g.error_pos]
  coverage w hw := by
    obtain ⟨y, hy⟩ := g.coverage w (by linarith [f.error_pos, g.error_pos])
    have hyrad := g.radial_lower y
    have hytri := dist_triangle (g.toFun y) w z
    rw [dist_comm (g.toFun y) w] at hytri
    have hybound : dist y.val q < s - 2 * ε := by linarith
    obtain ⟨x, hx⟩ := f.coverage y.val (by linarith [f.error_pos])
    have hxrad := f.radial_lower x
    have hxtri := dist_triangle (f.toFun x) y.val q
    rw [dist_comm (f.toFun x) y.val] at hxtri
    have hxs : dist x.val p ≤ s := by linarith
    let xx : BallCarrier p s := ⟨x.val, hxs⟩
    let fx : BallCarrier q S := ⟨f.toFun x, f.image_mem hsR hsS xx⟩
    have hg := (abs_lt.mp (g.distortion y fx)).2
    have htri := dist_triangle w (g.toFun y) (g.toFun fx)
    refine ⟨xx, ?_⟩
    change dist w (g.toFun fx) < 2 * (ε + η)
    dsimp only [fx] at hg
    linarith [f.error_pos]

noncomputable def inverseLift (f : PointedBallApprox p q R ε)
    (hsR : s + ε ≤ R) (y : BallCarrier q s) : BallCarrier p R := by
  classical
  exact if y.val = q then
    ⟨p, by simpa using (le_of_lt (lt_trans f.error_pos f.error_lt_radius))⟩
  else Classical.choose (f.coverage y.val (by linarith [y.property]))

theorem inverseLift_spec (f : PointedBallApprox p q R ε) (hsR : s + ε ≤ R)
    (y : BallCarrier q s) : dist y.val (f.toFun (f.inverseLift hsR y)) < ε := by
  classical
  unfold inverseLift
  split_ifs with h
  · simpa only [h, f.basepoint, dist_self] using f.error_pos
  · exact Classical.choose_spec (f.coverage y.val (by linarith [y.property]))

theorem inverseLift_basepoint (f : PointedBallApprox p q R ε)
    (hsR : s + ε ≤ R) (hs : 0 ≤ s) :
    (f.inverseLift hsR ⟨q, by simpa using hs⟩).val = p := by
  classical
  simp [inverseLift]

theorem inverseLift_distortion (f : PointedBallApprox p q R ε)
    (hsR : s + ε ≤ R) (y y' : BallCarrier q s) :
    |dist (f.inverseLift hsR y).val (f.inverseLift hsR y').val - dist y.val y'.val| <
      3 * ε := by
  let x := f.inverseLift hsR y
  let x' := f.inverseLift hsR y'
  have h := abs_lt.mp (f.distortion x x')
  have hy := f.inverseLift_spec hsR y
  have hy' := f.inverseLift_spec hsR y'
  change dist y.val (f.toFun x) < ε at hy
  change dist y'.val (f.toFun x') < ε at hy'
  have h1 := dist_triangle (f.toFun x) y.val y'.val
  have h2 := dist_triangle (f.toFun x) y'.val (f.toFun x')
  have h3 := dist_triangle y.val (f.toFun x) (f.toFun x')
  have h4 := dist_triangle y.val (f.toFun x') y'.val
  rw [dist_comm (f.toFun x) y.val] at h1
  rw [dist_comm (f.toFun x') y'.val] at h4
  apply abs_lt.mpr
  constructor <;> linarith

theorem forward_mem_inverseBall (f : PointedBallApprox p q R ε)
    (hsR : s + ε ≤ R) (x : BallCarrier p (s - 4 * ε)) :
    dist (f.toFun ⟨x.val, by linarith [x.property, f.error_pos]⟩) q ≤ s := by
  have h := f.radial_upper ⟨x.val, by linarith [x.property, f.error_pos]⟩
  dsimp at h
  linarith [x.property, f.error_pos]

theorem inverseLift_left_error (f : PointedBallApprox p q R ε)
    (hsR : s + ε ≤ R) (x : BallCarrier p (s - 4 * ε)) :
    dist (f.inverseLift hsR
      ⟨f.toFun ⟨x.val, by linarith [x.property, f.error_pos]⟩,
        f.forward_mem_inverseBall hsR x⟩).val x.val < 2 * ε := by
  let xx : BallCarrier p R := ⟨x.val, by linarith [x.property, f.error_pos]⟩
  let y : BallCarrier q s := ⟨f.toFun xx, f.forward_mem_inverseBall hsR x⟩
  have h := (abs_lt.mp (f.distortion xx (f.inverseLift hsR y))).1
  have hspec := f.inverseLift_spec hsR y
  change dist (f.toFun xx) (f.toFun (f.inverseLift hsR y)) < ε at hspec
  change dist (f.inverseLift hsR y).val xx.val < 2 * ε
  rw [dist_comm]
  linarith

noncomputable def quasiInverse (f : PointedBallApprox p q R ε)
    (hs : 4 * ε < s) (hsR : s + ε ≤ R) : PointedBallApprox q p s (4 * ε) where
  error_pos := by linarith [f.error_pos]
  error_lt_radius := hs
  toFun y := (f.inverseLift hsR y).val
  basepoint := f.inverseLift_basepoint hsR (by linarith [f.error_pos])
  distortion y y' := by
    have h := f.inverseLift_distortion hsR y y'
    linarith [f.error_pos]
  coverage x hx := by
    let xx : BallCarrier p (s - 4 * ε) := ⟨x, hx⟩
    let xxR : BallCarrier p R := ⟨x, by linarith [f.error_pos]⟩
    refine ⟨⟨f.toFun xxR, f.forward_mem_inverseBall hsR xx⟩, ?_⟩
    have h := f.inverseLift_left_error hsR xx
    rw [dist_comm]
    exact lt_trans h (by linarith [f.error_pos])

end PointedBallApprox
end GC.MetricGeometry
