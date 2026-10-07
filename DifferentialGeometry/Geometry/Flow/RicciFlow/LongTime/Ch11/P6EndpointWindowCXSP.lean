import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WindowScalarCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BallGradientCXSP

set_option autoImplicit false

/-!
# CX-SPINE G6：局部时间与局部空间控制给端点小球标量界

终端中心 R≤M，阈值 q≤M。只需中心在 Ioo v t 上的时间导数界，及每个时刻
两倍小球上的阈值梯度界，即得内层小球 R≤8M。没有全空间梯度或全历史导数前提。
时间端点的中心界来自实际 clipped-reciprocal ODE；空间测试只需开时间窗。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

/-- 短窗口内，仅局部导数和梯度控制即给每个端点小球的统一标量界。 -/
theorem scalar_le_eight_mul_on_window_ball_CXSP
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    {Ctime Cgrad : ℝ≥0} {q M v t ℓ : ℝ} (x : P.Carrier)
    (hav : a ≤ v) (hvt : v ≤ t) (hts : t < s)
    (hderiv : ∀ w ∈ Ioo v t, q < G.flow.scalar w x →
      |derivWithin (fun z => G.flow.scalar z x) (Iic w) w| ≤
        Ctime * G.flow.scalar w x ^ 2)
    (hgrad : ∀ w ∈ Ioo v t,
      ∀ z ∈ riemannianBallOf (G.flow.base.metric w) x (2 * ℓ), q < G.flow.scalar w z →
      ∀ ξ : TangentSpace ThreeModel z,
        |scalarDifferential G.flow w z ξ| ≤
          Cgrad * G.flow.scalar w z * Real.sqrt (G.flow.scalar w z) *
            Real.sqrt ((G.flow.base.metric w).inner z ξ ξ))
    (hM : 0 < M) (hqM : q ≤ M) (hscalar : G.flow.scalar t x ≤ M)
    (htime : Ctime * M * (t - v) ≤ 1 / 2) (hℓ : 0 < ℓ)
    (hspace : (Cgrad : ℝ) * ℓ * Real.sqrt (2 * M) ≤ 1 / 4) :
    ∀ w ∈ Ioo v t, ∀ z ∈ riemannianClosedBallOf (G.flow.base.metric w) x ℓ,
      G.flow.scalar w z ≤ 8 * M := by
  have hcenter := G.scalar_le_two_mul_on_window_CXSP x hav hvt hts hderiv
    hM hqM hscalar htime
  let : IsManifold ThreeModel 1 P.Carrier := IsManifold.of_le (n := ∞) (by decide)
  intro w hw z hz
  have hmax : max (G.flow.scalar w x) (2 * M) = 2 * M :=
    max_eq_right (hcenter w ⟨hw.1.le, hw.2.le⟩)
  have hbound := scalar_le_four_mul_max_of_ball_gradient_CXSP G.flow
    (qcan := 2 * M) (t := w) (x := x) (y := z)
    (fun y hy hR ξ => hgrad w hw y hy (by linarith) ξ)
    hℓ (by rw [hmax]; positivity) (by simpa only [hmax] using hspace) hz
  rw [hmax] at hbound
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
