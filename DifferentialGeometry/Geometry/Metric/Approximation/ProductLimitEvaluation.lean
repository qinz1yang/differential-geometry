import DifferentialGeometry.Geometry.Metric.Approximation.ControlledProductLimit

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

universe u v w z

variable {X : Type u} {E : Type v} {Z : Type w} {W : Type z}
variable [MetricSpace X] [MetricSpace E] [MetricSpace Z] [MetricSpace W]
variable {p : X} {a : E} {b : Z} {w : W} {δ K η : ℝ}

theorem KleinerLottApprox.productLimitApprox_factor_mem
    (φ : KleinerLottApprox p (WithLp.toLp 2 (a, b)) δ)
    (hη : 0 < η) (hδ : δ < η / 24) (hK : K + η < δ⁻¹)
    (x : BallCarrier p K) :
    dist (φ.toFun x.val).snd b ≤ K + η := by
  have hx : x.val ∈ ball p δ⁻¹ := x.property.trans_lt (by linarith)
  have hr := (abs_le.mp (φ.radial_error x.val hx)).2
  have hs := WithLp.dist_snd_le (φ.toFun x.val) (WithLp.toLp 2 (a, b))
  change dist (φ.toFun x.val).snd b ≤ _ at hs
  linarith [x.property]

theorem KleinerLottApprox.productLimitApprox_apply
    (φ : KleinerLottApprox p (WithLp.toLp 2 (a, b)) δ)
    (g : PointedBallApprox b w (K + η) (η / 24))
    (hη : 0 < η) (hηK : η < K) (hδ : δ < η / 24) (hK : K + η < δ⁻¹)
    (x : BallCarrier p K)
    (hx : dist (φ.toFun x.val).snd b ≤ K + η) :
    (φ.productLimitApprox g hη hηK hδ hK).toFun x =
      WithLp.toLp 2 ((φ.toFun x.val).fst, g.toFun ⟨(φ.toFun x.val).snd, hx⟩) := rfl

end GC.MetricGeometry
