import DifferentialGeometry.Geometry.Metric.Approximation.ProductCollapse
import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Topology.MetricSpace.ProperSpace

open Set Filter Metric
open scoped Topology

namespace Real

theorem abs_sqrt_sq_add_sq_sub_le (a b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |sqrt (a ^ 2 + b ^ 2) - sqrt (a ^ 2 + c ^ 2)| ≤ |b - c| := by
  have step (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
      sqrt (a ^ 2 + b ^ 2) ≤ sqrt (a ^ 2 + c ^ 2) + |b - c| := by
    have hs := sq_sqrt (show 0 ≤ a ^ 2 + b ^ 2 by positivity)
    have ht := sq_sqrt (show 0 ≤ a ^ 2 + c ^ 2 by positivity)
    have hn := sqrt_nonneg (a ^ 2 + b ^ 2)
    have hm := sqrt_nonneg (a ^ 2 + c ^ 2)
    have hd := abs_nonneg (b - c)
    have hbc : b ≤ c + |b - c| := by linarith [le_abs_self (b - c)]
    have hcs : c ≤ sqrt (a ^ 2 + c ^ 2) := by nlinarith [sq_nonneg a]
    have hbcs : b ^ 2 ≤ (c + |b - c|) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hcs) hd]
  exact abs_le.mpr ⟨by linarith [step c b hc hb, abs_sub_comm b c],
    by linarith [step b c hb hc]⟩

end Real

namespace WithLp

variable {E X Y : Type*} [MetricSpace E] [MetricSpace X] [MetricSpace Y]

theorem prod_dist_dist_sub_le (u v : E) (x x' : X) (y y' : Y) :
    |dist (toLp 2 (u, x)) (toLp 2 (v, x')) -
      dist (toLp 2 (u, y)) (toLp 2 (v, y'))| ≤ |dist x x' - dist y y'| := by
  rw [prod_dist_eq_sqrt_sq_add_sq, prod_dist_eq_sqrt_sq_add_sq]
  exact Real.abs_sqrt_sq_add_sq_sub_le _ _ _ dist_nonneg dist_nonneg

instance instProperSpaceL2Prod [ProperSpace E] [ProperSpace X] :
    ProperSpace (WithLp 2 (E × X)) where
  isCompact_closedBall p R := by
    have hc := ((isCompact_closedBall p.fst R).prod (isCompact_closedBall p.snd R)).image
      (WithLp.prod_continuous_toLp 2 E X)
    apply hc.of_isClosed_subset isClosed_closedBall
    intro x hx
    refine ⟨(x.fst, x.snd), ⟨?_, ?_⟩, rfl⟩
    · exact (dist_fst_le x p).trans hx
    · exact (dist_snd_le x p).trans hx

end WithLp

namespace GC.MetricGeometry.PointedBallApprox

variable {E X Y : Type*} [MetricSpace E] [MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {R ε : ℝ}

def l2Product (f : PointedBallApprox p q R ε) (u : E) (hεR : 3 * ε < R) :
    PointedBallApprox (WithLp.toLp 2 (u, p)) (WithLp.toLp 2 (u, q)) R (3 * ε) where
  error_pos := by linarith [f.error_pos]
  error_lt_radius := hεR
  toFun x := WithLp.toLp 2 (x.val.fst, f.toFun ⟨x.val.snd,
    (WithLp.dist_snd_le x.val (WithLp.toLp 2 (u, p))).trans x.property⟩)
  basepoint := by
    change WithLp.toLp 2 (u, f.toFun ⟨p, _⟩) = WithLp.toLp 2 (u, q)
    rw [f.basepoint]
  distortion x y := by
    have h := (WithLp.prod_dist_dist_sub_le x.val.fst y.val.fst
      (f.toFun ⟨x.val.snd, (WithLp.dist_snd_le _ _).trans x.property⟩)
      (f.toFun ⟨y.val.snd, (WithLp.dist_snd_le _ _).trans y.property⟩)
      x.val.snd y.val.snd).trans_lt (f.distortion _ _)
    exact h.trans (by linarith [f.error_pos])
  coverage y hy := by
    have hyq : dist y.snd q ≤ R - ε := by
      have h := (WithLp.dist_snd_le y (WithLp.toLp 2 (u, q))).trans hy
      change dist y.snd q ≤ R - 3 * ε at h
      linarith [f.error_pos]
    obtain ⟨z, hz⟩ := f.coverage y.snd hyq
    have hnear : dist y (WithLp.toLp 2 (y.fst, f.toFun z)) < ε := by
      change dist (WithLp.toLp 2 (y.fst, y.snd)) (WithLp.toLp 2 (y.fst, f.toFun z)) < ε
      rw [(WithLp.isometry_prodMk_left y.fst).dist_eq y.snd (f.toFun z)]
      exact hz
    have hd := (WithLp.prod_dist_dist_sub_le y.fst u z.val p (f.toFun z) q).trans_lt
      (by simpa only [dist_comm, abs_sub_comm, f.basepoint] using
        f.distortion z ⟨p, by simpa using (f.error_pos.trans f.error_lt_radius).le⟩)
    have ht := dist_triangle (WithLp.toLp 2 (y.fst, f.toFun z)) y
      (WithLp.toLp 2 (u, q))
    rw [dist_comm (WithLp.toLp 2 (y.fst, f.toFun z)) y] at ht
    have hrad : dist (WithLp.toLp 2 (y.fst, z.val)) (WithLp.toLp 2 (u, p)) ≤ R := by
      linarith [(abs_lt.mp hd).2, f.error_pos]
    refine ⟨⟨WithLp.toLp 2 (y.fst, z.val), hrad⟩, ?_⟩
    exact hnear.trans (by linarith [f.error_pos])

theorem l2Product_fst (f : PointedBallApprox p q R ε) (u : E) (hεR : 3 * ε < R)
    (x : BallCarrier (WithLp.toLp 2 (u, p)) R) :
    ((f.l2Product u hεR).toFun x).fst = x.val.fst := rfl

end GC.MetricGeometry.PointedBallApprox

namespace GC.MetricGeometry.PointedGHConverges

variable {E : Type*} {X : ℕ → Type*} {Y : Type*}
variable [MetricSpace E] [∀ i, MetricSpace (X i)] [MetricSpace Y]
variable [CompleteSpace E] {p : ∀ i, X i} {q : Y}

theorem l2Product (h : PointedGHConverges p q) (u : E) :
    PointedGHConverges (fun i => WithLp.toLp 2 (u, p i)) (WithLp.toLp 2 (u, q)) := by
  let := h.complete_space
  refine ⟨inferInstance, fun R ε hε hεR => ?_⟩
  filter_upwards [h.eventually_approx (R := R) (ε := ε / 3) (by linarith) (by linarith)] with i hi
  obtain ⟨f⟩ := hi
  have he : 3 * (ε / 3) = ε := by ring
  have hf := f.l2Product u (by linarith : 3 * (ε / 3) < R)
  rw [he] at hf
  exact ⟨hf⟩

end GC.MetricGeometry.PointedGHConverges
