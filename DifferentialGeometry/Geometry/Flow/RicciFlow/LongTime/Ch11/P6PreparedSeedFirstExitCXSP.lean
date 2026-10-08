import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HistoryPinchingCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedRecordsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedRecordScaleCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingC11GT6

set_option autoImplicit false

/-!
# CX-SPINE G21：任意 prepared chain 的 guarded seed first-exit 消费

同一 S/F 上实际选择 records，支付 model/old/windows、统一 HI 及固定种子尺度的 late scale gap。
用户 q 只用于 terminal nr guard；不假定其 model 字段等于实际 params。
C1/C2 固定为标准 C1P6/C2P6；仅中心 Good、局部梯度、traces 与短窗数值预算仍待生产。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 任意 S 的实际 geometry 支付 G20：外部仅保留同窗 analytic 数据和 trace 输入。 -/
theorem exists_prepared_seed_firstExit_CXSP (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
      ∀ L : ℝ, ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        let C1 := C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ
        let C2 := C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ
        ∀ {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t) {r M : ℝ},
        T₀ ≤ (t : ℝ) → (t : ℝ) / 2 ≤ a → 0 < r → q.neckRadius t ≤ r →
        M * r ^ 2 ≤ L →
        ∀ {p x : (H.stageAt t).Carrier}
          (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) p)
          (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x)
          {qcan Q K ℓ : ℝ} {X : ℝ≥0∞},
        0 < M → qcan ≤ M →
        metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M →
        metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ M →
        Γ.Ctime * M * ((t : ℝ) - a) ≤ 1 / 2 →
        0 < ℓ → 0 < Q → 1 ≤ Q * (a : ℝ) →
        (C2.toNNReal : ℝ) * ℓ * Real.sqrt (2 * M) ≤ 1 / 4 → K * ℓ ^ 2 ≤ 1 →
        2 * Real.sqrt 3 * (4 * M / Q + max (8 * M / Q) (2 * Real.exp 4)) * Q ≤ K →
        A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - a)) < X →
        ∀ (_hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
          (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
          ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → ∀ z : (H.stageAt w).Carrier,
            (z = A.point (H.activeStage w) (H.activeStage_mono haw)
                (H.activeStage_mono hwt) ∨
              z = B.point (H.activeStage w) (H.activeStage_mono haw)
                (H.activeStage_mono hwt)) →
            qcan ≤ metricScalarAt (H.stageMetric (H.activeStage w) w) z →
            H.HasSpatialCanonicalTimeControl Γ.epsilon C1 C2 Γ.Ctime w z)
        (_hgrad : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
          (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
          ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → H.time (H.activeStage w) < (w : ℝ) →
            ∀ z : (H.stageAt w).Carrier,
            (z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
                (A.point (H.activeStage w) (H.activeStage_mono haw)
                  (H.activeStage_mono hwt)) (2 * ℓ) ∨
              z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
                (B.point (H.activeStage w) (H.activeStage_mono haw)
                  (H.activeStage_mono hwt)) (2 * ℓ)) →
            qcan < metricScalarAt (H.stageMetric (H.activeStage w) w) z →
            ∀ ξ : TangentSpace ThreeModel z,
              |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
                (metricScalarAt (H.stageMetric (H.activeStage w) w)) z ξ)| ≤
                C2.toNNReal * metricScalarAt (H.stageMetric (H.activeStage w) w) z *
                  Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage w) w) z) *
                  Real.sqrt ((H.stageMetric (H.activeStage w) w).inner z ξ ξ)),
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          A.pairEDist_CXSP (hat := hat) B v hav hvt < X ∧
            A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
              A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) := by
  obtain ⟨ε₀, hε₀, hfirst⟩ := BackwardPointTrace.exists_pair_firstExit_of_local_analytic_CXSP.{u}
  obtain ⟨a₀, ha₀, hHI⟩ := exists_history_pinching_of_records_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γ S F q hTower hdiag hacc hrad hord
  obtain ⟨params, records, hmodelR, hmodelO, hmodelA, hparams, hcan, hOld, hdecay, hrecent⟩ :=
    exists_records_of_prepared_chain_CXSP S F hTower q hdiag
  have hacc' : params.modelAccuracy ≤ ε₀ := by rwa [hmodelA]
  have hord' : 2 ≤ params.modelOrder := by rwa [hmodelO]
  have hrad' : StandardCap.transitionEnd + 10 < params.modelRadius := by
    rw [hmodelR]
    unfold capWindowRadius_C11E at hrad
    linarith [StandardCap.transitionEnd_pos]
  intro L
  obtain ⟨T₀, hT₀, hscale⟩ := exists_late_seed_record_scale_CXSP
    (fun n => (F.tower.history n).toHistory) params records hdecay hrecent L
  refine ⟨T₀, hT₀, ?_⟩
  intro n H C1 C2 a t hat r M ht hhalf hr hguard hML p x A B qcan Q K ℓ X
    hM hqM hscalarA hscalarB htime hℓ hQ hlate hspace hKℓ hK hmargin hgood hgrad
  have hguard' : params.neckRadius t ≤ r := by
    rw [(hparams t t.2.1).2]
    exact hguard
  refine hfirst hat A B (records n) (hOld n) (hcan n) hacc' hord' hrad'
    hM hqM hscalarA hscalarB htime ?_ hℓ ha₀.le hQ hlate hspace hKℓ hK hmargin
    hgood hgrad ?_
  · intro e hf hl b
    exact hscale t ht n e (crossed_event_mem_half_window_CXSP H hhalf e hf hl)
      r M hr hguard' hML b
  · intro _v _hav _hvt _hstay w _haw _hwt _hvw _hwtlt _hage z _hz
    exact hHI F n (records n) w z

end GC.LongTime.Ch11
