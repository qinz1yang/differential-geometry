import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LargeCapCrossingC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapWindowDisjC11SP

set_option autoImplicit false

/-!
# Window 孪生第二行 ⇐ CC（records 情形，`hdisj` 消去；O-CH11-NATIVE-CC G1b，后缀 `_C11SP`）

G1 `P6LargeCapCrossingC11SP` 的两个 consumer 余 binder [CC, hdisj]；records 情形 `hdisj` 由
NATIVE-SHORT G3 `GeometricCutoffRecord.hdisj_C11SP`（PROVED）逐字填，`hOld` 由
`GeometricCutoffRecord.old_eq_retained` 填 ⇒ **唯一合同 binder = CC**。
每个非保护 crossing 的 (D4′) 因子与 NATIVE-SHORT record consumer
`surgery_no_shortcut_buffer_of_record_C11SP` 同一个 `C_buf`（文件末 `example` 把它直接喂进
G1 的单 crossing 跳跃 `jump_of_eventually_C11SP`）。
**关于 hshort**：G1 交付版（sha256 64968c85…）的 `pairEDist_window_of_largeCap_count_C11SP` 与
`pairEDist_window_of_CC_C11SP` **都没有 hshort 槽**（交付前已改接 NATIVE-SHORT twin）；带 A2 原形 `hshort`
槽的是 G1 未交付的草稿 v1（`build-logs/scratch/O-CH11-NATIVE-CC/wip/G1_v1_A2hshort.lean`），不在树内。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

variable {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
  {p q : (H.stageAt t).Carrier}

/-- **G1b history 层（PROVISIONAL[CC 计数 hCCA/hCCB]）**：G1 `pairEDist_window_of_largeCap_count_C11SP`
在 records 情形，`hOld := old_eq_retained`、`hdisj := hdisj_C11SP`（NATIVE-SHORT G3）。 -/
theorem pairEDist_window_of_largeCap_count_record_C11SP
    {params : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
    (hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
    (hε : params.modelAccuracy ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < params.modelRadius)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {X : ℝ≥0∞} {M : ℝ} (n₀ : ℕ)
    (hclassA : ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
      (hl : e.succ ≤ H.activeStage t),
      (∀ b, A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉ ((records e).static b).window ''
        {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b).window z = A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
        ((records e).static b).neck.scale ≤ M)
    (hclassB : ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
      (hl : e.succ ≤ H.activeStage t),
      (∀ b, B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉ ((records e).static b).window ''
        {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b).window z = B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
        ((records e).static b).neck.scale ≤ M)
    (hCCA : Set.ncard {e : Fin H.eventCount | ∃ (hf : H.activeStage a ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t) (b : (H.event e).RetainedBoundaryIndex)
        (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b).window z = A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
        ((records e).static b).neck.scale ≤ M} ≤ n₀)
    (hCCB : Set.ncard {e : Fin H.eventCount | ∃ (hf : H.activeStage a ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t) (b : (H.event e).RetainedBoundaryIndex)
        (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b).window z = B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
        ((records e).static b).neck.scale ≤ M} ≤ n₀)
    (hslab : ∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (haw : a ≤ w)
      (hwt : w ≤ t), v ≤ w → H.activeStage v = H.activeStage w →
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        A.pairEDist_CXSP (hat := hat) B w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v))) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        ENNReal.ofReal (max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
            ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
              (StandardCap.transitionEnd + 11) ^ 2)))
            (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))) ^ (2 * n₀) *
          (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
            ENNReal.ofReal (Λ * ((t : ℝ) - v))) :=
  pairEDist_window_of_largeCap_count_C11SP records (fun e => (records e).old_eq_retained) hcan hε hD
    (fun e => (records e).hdisj_C11SP) A B hΛ n₀ hclassA hclassB hCCA hCCB hslab

/-- **G1b（PROVISIONAL[CC] 唯一 binder）**：CC 合同（统一形）⇒ Window 孪生第二行，records 情形，
`hdisj` 已由 `hdisj_C11SP` 消去。 -/
theorem pairEDist_window_of_CC_record_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hCC : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ (θbar : ℝ) (n₀ : ℕ), 0 < θbar ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ θbar →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
        Set.ncard {e : Fin H.eventCount |
          ∃ (hf : H.activeStage a ≤ e.castSucc)
            (hl : e.succ ≤ H.activeStage t)
            (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            ((records n e).static b).window z =
              A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)} ≤ n₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ (θbar : ℝ) (n₀ : ℕ), 0 < θbar ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ θbar →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y x : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y)
        (A' : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A'.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
        params.modelAccuracy ≤ 1 / 2 → StandardCap.transitionEnd + 10 < params.modelRadius →
      ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ {X : ℝ≥0∞},
        (∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
          (hl : e.succ ≤ H.activeStage t),
          (∀ b, A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
            ((records n e).static b).window ''
              {y : standardCapWindow params.modelRadius |
                ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
          ∃ (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            ((records n e).static b).window z =
              A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)) →
        (∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
          (hl : e.succ ≤ H.activeStage t),
          (∀ b, A'.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
            ((records n e).static b).window ''
              {y : standardCapWindow params.modelRadius |
                ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
          ∃ (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            ((records n e).static b).window z =
              A'.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)) →
        (∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (haw : a ≤ w)
          (hwt : w ≤ t), v ≤ w → H.activeStage v = H.activeStage w →
          (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
            A.pairEDist_CXSP (hat := hat) A' s has hst < X) →
          A.pairEDist_CXSP (hat := hat) A' v hav hvt ≤
            A.pairEDist_CXSP (hat := hat) A' w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v))) →
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
          A.pairEDist_CXSP (hat := hat) A' s has hst < X) →
        A.pairEDist_CXSP (hat := hat) A' v hav hvt ≤
          ENNReal.ofReal (max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
              ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
                (StandardCap.transitionEnd + 11) ^ 2)))
              (4 * (StandardCap.transitionEnd + 11) *
                (StandardCap.transitionEnd + 13))) ^ (2 * n₀) *
            (A.pairEDist_CXSP (hat := hat) A' t hat le_rfl +
              ENNReal.ofReal (Λ * ((t : ℝ) - v))) := by
  have h := pairEDist_window_of_CC_C11SP P g hCC
  obtain ⟨ε₀, hε₀, θbar, n₀, hθbar, h⟩ := h
  refine ⟨ε₀, hε₀, θbar, n₀, hθbar, ?_⟩
  intro pBase Γf S F hT q hdiag hacc hrad hord params records h1 h2 h3 h4 h5 h6 h7 h8 B hB
  have hm := h S F hT q hdiag hacc hrad hord params records h1 h2 h3 h4 h5 h6 h7 h8 B hB
  obtain ⟨T₀, hT₀, hmain⟩ := hm
  refine ⟨T₀, hT₀, ?_⟩
  intro n θ hθ hθB H t ht Q hQ a hat hwin y x A A' hRA hRA' hε hD
  exact hmain n θ hθ hθB t ht Q hQ a hat hwin y x A A' hRA hRA' hε hD
    (fun e => (records n e).hdisj_C11SP)

/-- consumer：NATIVE-SHORT record consumer `surgery_no_shortcut_buffer_of_record_C11SP` 直接喂
G1 的单 crossing 跳跃（非保护 crossing 的 `C_buf` 因子，0 合同 binder）。 -/
example {params : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
    (hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
    (hε : params.modelAccuracy ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < params.modelRadius)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {X : ℝ≥0∞}
    (hslab : ∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (haw : a ≤ w)
      (hwt : w ≤ t), v ≤ w → H.activeStage v = H.activeStage w →
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        A.pairEDist_CXSP (hat := hat) B w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v)))
    (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc) (hl : e.succ ≤ H.activeStage t)
    (hpb : (∀ b, A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
        {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b₀ : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b₀).window x = A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl)
    (hqb : (∀ b, B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
        {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b₀ : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b₀).window x = B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl) :=
  jump_of_eventually_C11SP A B hΛ hslab e hf hl
    (fun _ hδ => ObservedHistory.surgery_no_shortcut_buffer_of_record_C11SP H e (records e)
      (hcan e) hε hD (A.crossing e hf hl) (B.crossing e hf hl) hpb hqb hδ)

end GC.LongTime.Ch11
