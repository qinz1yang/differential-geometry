import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceGoodSuffixCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BallGradientCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointCurvatureC11G

set_option autoImplicit false

/-!
# CX-SPINE G20：实际 trace 的局部端点球 Ricci producer

只在测试时刻的两倍球消费梯度；同一 Good 后缀给中心 R≤2M，再得内球 R≤8M。
实际 Hamilton–Ivey 与数值 ℓ 预算给 Ricci≤3/ℓ²。此处不假设全空间曲率控制。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 实际 regular stage 的时间界识别 activeStage，包括末 stage。 -/
theorem ObservedHistory.activeStage_eq_of_regular_stage_CXSP
    (H : ObservedHistory.{u}) (w : Icc (0 : ℝ) H.horizon)
    (j : Fin (H.eventCount + 1)) (hleft : H.time j ≤ w)
    (hright : ∀ e : Fin H.eventCount, j = e.castSucc → (w : ℝ) < H.time e.succ) :
    H.activeStage w = j := by
  cases j using Fin.lastCases with
  | last => exact H.activeStage_eq_of_maximal w _ hleft (fun k _ => Fin.le_last k)
  | cast e => exact H.activeStage_eq_castSucc_C11G e w hleft (hright e rfl)

/-- 正 stage-age 的实际度量上，中心 R≤2M 与两倍球梯度给内球 R≤8M。 -/
theorem ObservedHistory.scalar_ball_le_eight_mul_CXSP
    (H : ObservedHistory.{u}) (w : Icc (0 : ℝ) H.horizon)
    (hage : H.time (H.activeStage w) < (w : ℝ)) (x : (H.stageAt w).Carrier)
    {M q ℓ : ℝ} {Cgrad : ℝ≥0} (hM : 0 < M) (hqM : q ≤ M)
    (hcenter : metricScalarAt (H.stageMetric (H.activeStage w) w) x ≤ 2 * M)
    (hℓ : 0 < ℓ) (hspace : (Cgrad : ℝ) * ℓ * Real.sqrt (2 * M) ≤ 1 / 4)
    (hgrad : ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w) x (2 * ℓ),
      q < metricScalarAt (H.stageMetric (H.activeStage w) w) z →
      ∀ ξ : TangentSpace ThreeModel z,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
          (metricScalarAt (H.stageMetric (H.activeStage w) w)) z ξ)| ≤
          Cgrad * metricScalarAt (H.stageMetric (H.activeStage w) w) z *
            Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage w) w) z) *
            Real.sqrt ((H.stageMetric (H.activeStage w) w).inner z ξ ξ))
    (z : (H.stageAt w).Carrier)
    (hz : z ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage w) w) x ℓ) :
    metricScalarAt (H.stageMetric (H.activeStage w) w) z ≤ 8 * M := by
  let G := H.closedPrefixAt w hage
  let : IsManifold ThreeModel 1 (H.stageAt w).Carrier := IsManifold.of_le (n := ∞) (by decide)
  have hg : G.flow.base.metric (w : ℝ) = H.stageMetric (H.activeStage w) w :=
    H.closedPrefixAt_metric w hage w
  have hmax : max (G.flow.scalar w x) (2 * M) = 2 * M := by
    apply max_eq_right
    change metricScalarAt (G.flow.base.metric w) x ≤ 2 * M
    rwa [hg]
  have hbound := scalar_le_four_mul_max_of_ball_gradient_CXSP G.flow
    (qcan := 2 * M) (t := w) (x := x) (y := z)
    (Cgrad := Cgrad) (r := ℓ) (fun y hy hR ξ => by
      change y ∈ riemannianBallOf (G.flow.base.metric w) x (2 * ℓ) at hy
      change 2 * M < metricScalarAt (G.flow.base.metric w) y at hR
      change |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
        (metricScalarAt (G.flow.base.metric w)) y ξ)| ≤
        Cgrad * metricScalarAt (G.flow.base.metric w) y *
          Real.sqrt (metricScalarAt (G.flow.base.metric w) y) *
          Real.sqrt ((G.flow.base.metric w).inner y ξ ξ)
      rw [hg] at hy hR ⊢
      exact hgrad y hy (by linarith) ξ)
    hℓ (by rw [hmax]; positivity) (by simpa only [hmax] using hspace)
    (by rwa [hg])
  rw [hmax] at hbound
  change metricScalarAt (G.flow.base.metric w) z ≤ 4 * (2 * M) at hbound
  rw [hg] at hbound
  linarith

namespace BackwardPointTrace

/-- 同一 trace 的 Good 后缀与局部梯度、HI 数据给 regular 时刻的端点球 Ricci 界。 -/
theorem ricci_on_ball_of_good_suffix_CXSP
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {p : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {ε C1 C2 q M Q s a₀ K ℓ : ℝ} {Ctime Cgrad : ℝ≥0}
    (hM : 0 < M) (hqM : q ≤ M)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      s < (v : ℝ) → (v : ℝ) < t →
      q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)))
    (hscalar : metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - s) ≤ 1 / 2)
    (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hsw : s < (w : ℝ)) (hwt : w ≤ t)
    (hage : H.time (H.activeStage w) < (w : ℝ))
    (hgrad : ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
      (A.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) (2 * ℓ),
      q < metricScalarAt (H.stageMetric (H.activeStage w) w) z →
      ∀ ξ : TangentSpace ThreeModel z,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
          (metricScalarAt (H.stageMetric (H.activeStage w) w)) z ξ)| ≤
          Cgrad * metricScalarAt (H.stageMetric (H.activeStage w) w) z *
            Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage w) w) z) *
            Real.sqrt ((H.stageMetric (H.activeStage w) w).inner z ξ ξ))
    (ha₀ : 0 ≤ a₀) (hQ : 0 < Q) (hlate : 1 ≤ Q * (w : ℝ))
    (hℓ : 0 < ℓ) (hspace : (Cgrad : ℝ) * ℓ * Real.sqrt (2 * M) ≤ 1 / 4)
    (hKℓ : K * ℓ ^ 2 ≤ 1)
    (hK : 2 * Real.sqrt 3 * (4 * M / Q + max (8 * M / Q) (2 * Real.exp 4)) * Q ≤ K)
    (z : (H.stageAt w).Carrier)
    (hpin : InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage w) w) (a₀ + w) z)
    (hz : riemannianEDistOf (H.stageMetric (H.activeStage w) w)
      (A.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) z <
        ENNReal.ofReal ℓ) (ξ : TangentSpace ThreeModel z) :
    ricciTensor (H.stageMetric (H.activeStage w) w) z ξ ξ ≤
      (3 / ℓ ^ 2) * (H.stageMetric (H.activeStage w) w).inner z ξ ξ := by
  have hcenter := A.scalar_le_two_mul_of_good_suffix_CXSP hat hM hqM hgood hscalar htime
    w haw hsw hwt
  have hball := H.scalar_ball_le_eight_mul_CXSP w hage _ hM hqM hcenter hℓ hspace
    hgrad z hz.le
  have hwpos : 0 < (w : ℝ) := (H.time_nonneg _).trans_lt hage
  have hC : (0 : ℝ) ≤ 8 * M / Q := by positivity
  have hscal : metricScalarAt (H.stageMetric (H.activeStage w) w) z ≤ (8 * M / Q) * Q := by
    simpa only [div_mul_cancel₀ _ hQ.ne'] using hball
  have hRm := ObservedHistory.sqrt_rmNormSq_le_of_HI_scalar_C11G
    (H.stageMetric (H.activeStage w) w) z ha₀ hwpos hQ hlate hC hpin hscal
  have hRmK : Real.sqrt (normSq0S (H.stageMetric (H.activeStage w) w) z 4
      (metricRm04At (H.stageMetric (H.activeStage w) w) z)) ≤ K := by
    exact hRm.trans (by simpa only [show 8 * M / Q / 2 = 4 * M / Q by ring] using hK)
  have hRic := ObservedHistory.ricciTensor_le_of_sqrt_rmNormSq_le_C11D _ z hRmK ξ
  have hKdiv : K ≤ 1 / ℓ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hℓ)).mpr hKℓ
  have hinner := metric_inner_self_nonneg (H.stageMetric (H.activeStage w) w) z ξ
  refine hRic.trans ?_
  apply mul_le_mul_of_nonneg_right _ hinner
  calc 3 * K ≤ 3 * (1 / ℓ ^ 2) := mul_le_mul_of_nonneg_left hKdiv (by norm_num)
    _ = 3 / ℓ ^ 2 := by ring

end BackwardPointTrace
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
