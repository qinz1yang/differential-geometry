import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceProtectionCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceDistanceRicciCXSP

set_option autoImplicit false

/-!
# CX-SPINE G19：实际 Good 后缀支付保护后消费整史 first-exit

cap accuracy 在 history 之前选取；对同一 trace pair 逐一调用实际 scalar-to-protection。
结论含全部闭窗时刻，包括 candidate birth 与终端 birth。此处不新增顶层 hspine 前提；
局部 consumer 的 full Good、record scale gap、trace 和 Ricci 输入仍列明。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u

/-- 以实际 Good 和 scale gap 消去 G18 endpoint-protection binder 的 first-exit consumer。 -/
theorem exists_pair_firstExit_of_good_ricci_CXSP :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
        {p q : (H.stageAt t).Carrier}
        (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) p)
        (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) q)
        {params : CutoffParameters}
        (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
        (_hOld : ∀ e : Fin H.eventCount,
          (H.event e).old = (H.event e).transition.trace.retainedCore)
        (_hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
        (_hacc : params.modelAccuracy ≤ ε₀) (_hm : 2 ≤ params.modelOrder)
        (_hD : StandardCap.transitionEnd + 10 < params.modelRadius)
        {ε C1 C2 qcan M : ℝ} {Ctime : ℝ≥0} (_hM : 0 < M) (_hqM : qcan ≤ M)
        (_hscalarA : metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M)
        (_hscalarB : metricScalarAt (H.stageMetric (H.activeStage t) t) q ≤ M)
        (_htime : Ctime * M * ((t : ℝ) - a) ≤ 1 / 2)
        (_hscale : ∀ (e : Fin H.eventCount), H.activeStage a ≤ e.castSucc →
          e.succ ≤ H.activeStage t → ∀ b, 4 * M < ((records e).static b).neck.scale)
        {ℓ : ℝ} (_hℓ : 0 < ℓ) {X : ℝ≥0∞}
        (_hmargin : A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - a)) < X)
        (_hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
          (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
          ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → ∀ z : (H.stageAt w).Carrier,
            (z = A.point (H.activeStage w) (H.activeStage_mono haw)
                (H.activeStage_mono hwt) ∨
              z = B.point (H.activeStage w) (H.activeStage_mono haw)
                (H.activeStage_mono hwt)) →
            qcan ≤ metricScalarAt (H.stageMetric (H.activeStage w) w) z →
            H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime w z)
        (_hRic : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
          (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
          ∀ (j : Fin (H.eventCount + 1)) (hf : H.activeStage a ≤ j)
            (hl : j ≤ H.activeStage t) (s : ℝ),
            (v : ℝ) < s → H.time j < s → s < t →
            (∀ e : Fin H.eventCount, j = e.castSucc → s < H.time e.succ) →
            ∀ z : (H.stage j).Carrier, ∀ ξ : TangentSpace ThreeModel z,
            (riemannianEDistOf (H.stageMetric j s) (A.point j hf hl) z < ENNReal.ofReal ℓ ∨
              riemannianEDistOf (H.stageMetric j s) (B.point j hf hl) z < ENNReal.ofReal ℓ) →
            ricciTensor (H.stageMetric j s) z ξ ξ ≤
              (3 / ℓ ^ 2) * (H.stageMetric j s).inner z ξ ξ),
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          A.pairEDist_CXSP (hat := hat) B v hav hvt < X ∧
            A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
              A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) := by
  obtain ⟨εcap, hεcap, hprotect⟩ := exists_trace_protection_of_good_suffix_CXSP.{u}
  refine ⟨min εcap (1 / 2), lt_min hεcap (by norm_num), ?_⟩
  intro H a t hat p q A B params records hOld hcan hacc hm hD ε C1 C2 qcan M Ctime
    hM hqM hscalarA hscalarB htime hscale ℓ hℓ X hmargin hgood hRic
  have haccCap : params.modelAccuracy ≤ εcap := hacc.trans (min_le_left _ _)
  have haccHalf : params.modelAccuracy ≤ 1 / 2 := hacc.trans (min_le_right _ _)
  refine A.pair_firstExit_of_window_ricci_CXSP hat B records hOld hcan haccHalf hD hℓ
    hmargin ?_ hRic
  intro v hav hvt hstay e hf hl hve b
  have htimeV : Ctime * M * ((t : ℝ) - v) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_left (show (a : ℝ) ≤ v from hav) (t : ℝ))
      (mul_nonneg Ctime.coe_nonneg hM.le)).trans htime
  constructor
  · refine hprotect hat A records haccCap hm hcan hD (ε := ε) (C1 := C1) (C2 := C2)
      hM hqM ?_ hscalarA htimeV e hf hl hve b (hscale e hf hl b)
    intro w haw hwt hvw hwtlt hR
    exact hgood v hav hvt hstay w haw hwt hvw hwtlt _ (Or.inl rfl) hR
  · refine hprotect hat B records haccCap hm hcan hD (ε := ε) (C1 := C1) (C2 := C2)
      hM hqM ?_ hscalarB htimeV e hf hl hve b (hscale e hf hl b)
    intro w haw hwt hvw hwtlt hR
    exact hgood v hav hvt hstay w haw hwt hvw hwtlt _ (Or.inr rfl) hR

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
