import DifferentialGeometry.Geometry.Metric.L2Product
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation

set_option autoImplicit false

namespace WithLp

variable {E A : Type*} [MetricSpace E] [MetricSpace A]

theorem snd_dist_sq_le_of_fst_dist_gap (x y : WithLp 2 (E × A)) {B η : ℝ}
    (hB : dist x y ≤ B) (hgap : dist x y - dist x.fst y.fst ≤ η) :
    dist x.snd y.snd ^ 2 ≤ 2 * B * η := by
  have hfst := dist_fst_le x y
  have hnonneg : 0 ≤ dist x y - dist x.fst y.fst := sub_nonneg.mpr hfst
  have hη : 0 ≤ η := hnonneg.trans hgap
  have hsum : dist x y + dist x.fst y.fst ≤ 2 * B := by linarith
  calc
    dist x.snd y.snd ^ 2 = (dist x y - dist x.fst y.fst) *
        (dist x y + dist x.fst y.fst) := by nlinarith [prod_dist_sq_eq_add_sq x y]
    _ ≤ η * (2 * B) := mul_le_mul hgap hsum (by positivity) hη
    _ = 2 * B * η := by ring

end WithLp

namespace GC.MetricGeometry.KleinerLottApprox

variable {X Y E A : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace E] [MetricSpace A]
variable {p : X} {q : Y} {a : E} {b : A} {β R ε η : ℝ}

theorem snd_dist_sq_le_of_coordinate_control
    (F : KleinerLottApprox p (WithLp.toLp 2 (a, b)) β)
    (g : PointedBallApprox p q R ε) (e : Y ≃ᵢ E) (he : e q = a)
    (x : BallCarrier p R) (hx : dist x.val p < β⁻¹)
    (hcontrol : dist (F.toFun x.val).fst (e (g.toFun x)) ≤ η) :
    dist (F.toFun x.val).snd b ^ 2 ≤ 2 * (dist x.val p + β) * (β + ε + η) := by
  have hrad := (abs_le.mp (F.radial_error x.val hx)).2
  have hlower := g.radial_lower x
  have htri := dist_triangle (e (g.toFun x)) (F.toFun x.val).fst a
  have hd : dist (e (g.toFun x)) a = dist (g.toFun x) q := by
    rw [← he, e.dist_eq]
  rw [hd] at htri
  have hrev : dist (e (g.toFun x)) (F.toFun x.val).fst ≤ η := by
    simpa only [dist_comm] using hcontrol
  apply WithLp.snd_dist_sq_le_of_fst_dist_gap (F.toFun x.val) (WithLp.toLp 2 (a, b))
  · linarith
  · simp only [WithLp.toLp_fst]
    linarith

end GC.MetricGeometry.KleinerLottApprox
