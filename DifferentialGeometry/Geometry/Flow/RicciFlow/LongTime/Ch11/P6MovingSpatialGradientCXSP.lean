import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceAnalyticFirstExitCXSP

set_option autoImplicit false

/-!
# CX-SPINE G22：同一 moving 球的空间 witness 支付局部梯度

当前 d(p,x)<B 与 B+2ℓ≤ρ 将两端2ℓ球放入原p中心ρ球；边界等号允许。
只读取同一 SpatialCanonicalWitness.gradient，不索取时间导数或扩大 canonical 常数。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 同一 metric 上的 spatial 供给与真实三角包含给两端球的阈值梯度。 -/
theorem pair_ball_gradient_of_spatial_CXSP
    {P : OrientedThreeStage.{u}} (g : P.Metric) (p x : P.Carrier)
    {ε C1 C2 q B ℓ ρ : ℝ} (hℓ : 0 < ℓ)
    (hd : riemannianEDistOf g p x < ENNReal.ofReal B) (hregion : B + 2 * ℓ ≤ ρ)
    (hspatial : ∀ z ∈ riemannianBallOf g p ρ, q ≤ metricScalarAt g z →
      Nonempty (SpatialCanonicalWitness g ε C1 C2 z))
    (z : P.Carrier)
    (hz : z ∈ riemannianBallOf g p (2 * ℓ) ∨ z ∈ riemannianBallOf g x (2 * ℓ))
    (hR : q < metricScalarAt g z) (ξ : TangentSpace ThreeModel z) :
    |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt g) z ξ)| ≤
      C2.toNNReal * metricScalarAt g z * Real.sqrt (metricScalarAt g z) *
        Real.sqrt (g.inner z ξ ξ) := by
  have hB : 0 < B := ENNReal.ofReal_pos.mp (bot_le.trans_lt hd)
  have hzρ : z ∈ riemannianBallOf g p ρ := by
    rcases hz with hz | hz
    · exact riemannianBallOf_mono g p (by linarith) hz
    · have hsum : ENNReal.ofReal B + ENNReal.ofReal (2 * ℓ) ≤ ENNReal.ofReal ρ := by
        rw [← ENNReal.ofReal_add hB.le (by positivity)]
        exact ENNReal.ofReal_le_ofReal hregion
      exact (riemannianEDistOf_triangle g p x z).trans_lt
        ((ENNReal.add_lt_add hd hz).trans_le hsum)
  obtain ⟨W⟩ := hspatial z hzρ hR.le
  refine (W.gradient ξ).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C2) W.Q_pos.le

end GC.LongTime.Ch11
