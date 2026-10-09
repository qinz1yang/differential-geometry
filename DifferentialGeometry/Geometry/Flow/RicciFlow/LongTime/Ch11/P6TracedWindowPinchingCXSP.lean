import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedRecordsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HistoryPinchingCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PinchingP6A
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.ClosedWindow
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling
import DifferentialGeometry.Geometry.Metric.PullbackScaling

set_option autoImplicit false

/-!
# CX-SPINE：原 history 的实际 traced window 给统一 age-normalized pinching

由同一 prepared chain 的实际 records 取 HI。
真实 traced region 产生共同 flow，按 R*g(t+s/R) 归一化；全窗共用
a_min=a0+t-theta/R 与 Lambda=a_min*R。a_min=a0+a>0 来自真实起点 a。
同一个 normalized flow 同时保留 Rm bound 与 pinching，不增加 hpinch 输入。
末叶只支付显式数值下界，不假定物理曲率尺度 R 本身趋于无穷。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 同源 records 与 traced region 实际生产共用 Lambda 的 normalized window。 -/
theorem exists_prepared_traced_window_pinching_CXSP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (a₀ : ℝ) (Phi : ℝ → ℝ), 0 < a₀ ∧ AdmissiblePinchingFunction Phi ∧
      ∀ {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
        (chain : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g),
        F.tower = chain.tower → ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
        (R ρ θ K : ℝ) (hR : 0 < R) (hθ : 0 < θ),
        H.isTracedRegion t p ρ (θ / R) (K * R) →
      let aMin := a₀ + (t : ℝ) - θ / R
      let Lambda := aMin * R
      0 < aMin ∧ 0 < Lambda ∧
        ∃ U : TopologicalSpace.Opens (H.stageAt t).Carrier,
          (U : Set (H.stageAt t).Carrier) =
            riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ ∧
        ∃ B : SolutionOn (I := ThreeModel) (M := U)
            (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)),
          IsSolutionOn B ∧
          B.base.metric 0 =
            (scaleMetric R hR (H.stageMetric (H.activeStage t) t)).restrictOpen U ∧
          ∀ s ∈ Icc (-θ) 0, ∀ x : U,
            curvDerivNormSq 0 (B.base.metric s) x ≤ K ^ 2 ∧
            curvatureOperatorLowerBoundAt (B.base.metric s) x
              (metricAlgebraicCurvatureTensorAt (B.base.metric s) x)
              (rescalePinchingFunction Lambda Phi (metricScalarAt (B.base.metric s) x)) := by
  obtain ⟨a₀, ha₀, hHI⟩ := exists_history_pinching_of_records_CXSP P g
  obtain ⟨Phi, hPhi, hpin⟩ := exists_age_normalized_pinching_P6A.{u}
  refine ⟨a₀, Phi, ha₀, hPhi, ?_⟩
  intro pBase Γ chain F hTower
  obtain ⟨params, records, _⟩ := exists_records_of_prepared_chain_CXSP
    chain F hTower (chainDiagonal_C11A chain) (fun _ _ => ⟨rfl, rfl⟩)
  intro n H t p R ρ θ K hR hθ htraced aMin Lambda
  obtain ⟨a, hat, ha, U, hU, f, hf, _hinj, _hcross, _hlast, S, hS,
    hmetric, hRm, hcurrent, _hcompact⟩ :=
    H.exists_common_flow_with_compact_neighborhood_of_isTracedRegion t p htraced
  have haMin : aMin = a₀ + (a : ℝ) := by
    change a₀ + (t : ℝ) - θ / R = a₀ + (a : ℝ)
    rw [ha]
    ring
  have hMin : 0 < aMin := by
    rw [haMin]
    exact add_pos_of_pos_of_nonneg ha₀ a.property.1
  have hwindow (s : ℝ) (hs : s ∈ Icc (-θ) 0) :
      (t : ℝ) + s / R ∈ Icc (a : ℝ) t := by
    have hlo := div_le_div_of_nonneg_right hs.1 hR.le
    have hhi := div_le_div_of_nonneg_right hs.2 hR.le
    simp only [neg_div, zero_div] at hlo hhi
    constructor <;> linarith
  let B := S.parabolicClosedWindow t R θ hR hθ.le
  have hB : IsSolutionOn B :=
    isSolutionOn_parabolicClosedWindow S hS (T := (t : ℝ)) hR hθ.le
      (fun v hv => ⟨by linarith [hv.1], hv.2⟩)
      (fun v hv => ⟨by linarith [hv.1], hv.2⟩)
  refine ⟨hMin, mul_pos hMin hR, U, hU, B, hB, ?_, ?_⟩
  · change scaleMetric R hR (S.base.metric ((t : ℝ) + 0 / R)) = _
    rw [zero_div, add_zero, hcurrent t ⟨hat, le_rfl⟩ (H.activeStage_mem t)]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rfl
  · intro s hs x
    have hv := hwindow s hs
    refine ⟨?_, ?_⟩
    · change curvDerivNormSq 0
        (scaleMetric R hR (S.base.metric ((t : ℝ) + s / R))) x ≤ K ^ 2
      rw [curvDerivNormSq_scaleMetric]
      have hb : curvDerivNormSq 0 (S.base.metric ((t : ℝ) + s / R)) x ≤ (K * R) ^ 2 :=
        hRm _ hv x
      calc
        _ ≤ R⁻¹ ^ (0 + 2) * (K * R) ^ 2 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = K ^ 2 := by rw [zero_add]; field_simp [hR.ne']
    · let v : Icc (0 : ℝ) H.horizon :=
        ⟨(t : ℝ) + s / R, a.property.1.trans hv.1, hv.2.trans t.property.2⟩
      have hav : a ≤ v := hv.1
      have hvt : v ≤ t := hv.2
      let j : H.StageInterval (H.activeStage a) (H.activeStage t) :=
        ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩
      have hscaled : B.base.metric s =
          localPullMetric (scaleMetric R hR (H.stageMetric j.val v)) (f j) (hf j) := by
        change scaleMetric R hR (S.base.metric ((t : ℝ) + s / R)) = _
        rw [hmetric j _ hv (H.activeStage_mem v), localPullMetric_scaleMetric]
      have hage : aMin ≤ a₀ + (v : ℝ) := by
        rw [haMin]
        linarith only [show (a : ℝ) ≤ v from hav]
      have hfixed : InFixedHamiltonIveyRegion (H.stageMetric j.val v) aMin (f j x) := by
        apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ aMin _).mpr
        exact fixedHamiltonIveyRegion_antitoneOn hMin
          (add_pos_of_pos_of_nonneg ha₀ v.property.1) hage
          ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ (a₀ + v) _).mp
            (hHI F n (records n) v (f j x)))
      have hp := hpin (H.stage j.val).Carrier (H.stageMetric j.val v)
        aMin R hR (f j x) hMin hfixed
      rw [hscaled, metricScalarAt_localPull]
      exact (curvatureOperatorLowerBoundAt_localPullMetric_iff
        (scaleMetric R hR (H.stageMetric j.val v)) (f j) (hf j) x _).mpr hp

/-- 实际 lower scalar band 与 seed 时间余量给 Lambda 的数值增长下界。 -/
theorem traced_window_pinching_parameter_lower_CXSP
    {a₀ t θ H0 r R L : ℝ} (ha₀ : 0 ≤ a₀) (hr : 0 < r) (hR : 0 < R)
    (htime : 2 * r ^ 2 < t)
    (hlower : H0 * (r ^ 2)⁻¹ * (L - 1) < R) :
    2 * H0 * (L - 1) - θ ≤ (a₀ + t - θ / R) * R := by
  have hl : H0 * (L - 1) < R * r ^ 2 := by
    calc
      _ = (H0 * (r ^ 2)⁻¹ * (L - 1)) * r ^ 2 := by field_simp [hr.ne']
      _ < _ := mul_lt_mul_of_pos_right hlower (sq_pos_of_pos hr)
  have ht := mul_lt_mul_of_pos_left htime hR
  have ha := mul_nonneg ha₀ hR.le
  have heq : (a₀ + t - θ / R) * R = a₀ * R + t * R - θ := by
    field_simp [hR.ne']
  rw [heq]
  nlinarith only [hl, ht, ha]

end GC.LongTime.Ch11

end
