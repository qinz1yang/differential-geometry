import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceFirstExitCXSP

set_option autoImplicit false

/-!
# CX-SPINE G18：实际 stage Ricci 与 protected crossings 支付整史距离估计

每个 smooth stage 用公开 I.8.3(b)，每个实际 event 用公开 no-shortcut；
有限 stage 链相加，误差仅为一次 (8/ℓ)(t-v)。不假设整窗已在 seed footprint 中。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u

/-- 同一对 trace 上的实际 Ricci 与 crossing 保护生产定量整史距离界。 -/
theorem pair_distance_le_of_stage_ricci_CXSP
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {p q : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {params : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
    (hOld : ∀ e : Fin H.eventCount,
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
    (hacc : params.modelAccuracy ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < params.modelRadius)
    (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
    (hprot : ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
      (hl : e.succ ≤ H.activeStage t), (v : ℝ) < H.time e.succ → ∀ b,
      A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
            {z : standardCapWindow params.modelRadius |
              ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
        B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
            {z : standardCapWindow params.modelRadius |
              ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hRic : ∀ (j : Fin (H.eventCount + 1)) (hf : H.activeStage a ≤ j)
      (hl : j ≤ H.activeStage t) (s : ℝ),
      (v : ℝ) < s → H.time j < s → s < t →
      (∀ e : Fin H.eventCount, j = e.castSucc → s < H.time e.succ) →
      ∀ z : (H.stage j).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf (H.stageMetric j s) (A.point j hf hl) z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (H.stageMetric j s) (B.point j hf hl) z < ENNReal.ofReal ℓ) →
      ricciTensor (H.stageMetric j s) z ξ ξ ≤
        (3 / ℓ ^ 2) * (H.stageMetric j s).inner z ξ ξ) :
    A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
      A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
        ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) := by
  have hchain := H.edist_le_of_stage_bounds_C11D (H.activeStage_mono hvt)
    (fun j hj1 hj2 => A.point j ((H.activeStage_mono hav).trans hj1) hj2)
    (fun j hj1 hj2 => B.point j ((H.activeStage_mono hav).trans hj1) hj2)
    (div_nonneg (by norm_num) hℓ.le) (H.activeStage_time_le v)
    (H.lt_time_succ_of_activeStage_eq_C11D v) hvt (H.activeStage_time_le t) (Λ := 8 / ℓ)
    (fun s hvs hjs hst => by
      apply H.smooth_distance_distortion_C11D (H.activeStage t) hℓ hst hjs
        (H.lt_time_succ_of_activeStage_eq_C11D t) t.2.2
      intro w hw z ξ hz
      exact hRic _ _ _ w (hvs.trans_lt hw.1) (hjs.trans_lt hw.1) hw.2
        (fun e he => hw.2.trans (H.lt_time_succ_of_activeStage_eq_C11D t e he)) z ξ hz)
    (fun e he1 he2 s hvs hjs hsτ => by
      let hf := (H.activeStage_mono hav).trans he1
      have hprotE := hprot e hf he2 (hvs.trans_lt hsτ)
      apply H.event_crossing_bound_C11D e (records e).static (hOld e) (hcan e) hacc hD
        (A.crossing e hf he2) (B.crossing e hf he2)
        (fun b => (hprotE b).1) (fun b => (hprotE b).2) hℓ hjs hsτ
      intro w hw z ξ hz
      have hwtop : w < (t : ℝ) := hw.2.trans_le
        ((H.time_strictMono.monotone he2).trans (H.activeStage_time_le t))
      apply hRic _ _ _ w (hvs.trans_lt hw.1) (hjs.trans_lt hw.1) hwtop ?_ z ξ hz
      intro e' he'
      obtain rfl : e = e' := Fin.castSucc_injective _ he'
      exact hw.2)
  exact hchain

/-- 全史 first-exit 的实际 Ricci consumer：保护与曲率只在未退出后缀的条件下要求。 -/
theorem pair_firstExit_of_window_ricci_CXSP
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {p q : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {params : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
    (hOld : ∀ e : Fin H.eventCount,
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
    (hacc : params.modelAccuracy ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < params.modelRadius)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {X : ℝ≥0∞}
    (hmargin : A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
      ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - a)) < X)
    (hprot : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
      (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
      ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t), (v : ℝ) ≤ H.time e.succ → ∀ b,
      A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
            {z : standardCapWindow params.modelRadius |
              ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
        B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
            {z : standardCapWindow params.modelRadius |
              ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    (hRic : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
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
        (3 / ℓ ^ 2) * (H.stageMetric j s).inner z ξ ξ) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      A.pairEDist_CXSP (hat := hat) B v hav hvt < X ∧
        A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
          A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
            ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) := by
  refine A.pair_distance_of_unexited_suffix_CXSP hat B records hOld hcan hacc hD
    (div_nonneg (by norm_num) hℓ.le) ?_ hmargin ?_
  · intro v hav hvt hstay e hf hl htime b
    exact hprot v hav.le hvt hstay e hf hl htime.ge b
  · intro v hav hvt hstay
    exact A.pair_distance_le_of_stage_ricci_CXSP hat B records hOld hcan hacc hD v hav hvt
      (fun e hf hl he b => hprot v hav hvt hstay e hf hl he.le b) hℓ
      (hRic v hav hvt hstay)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
