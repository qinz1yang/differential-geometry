import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeWindowPairC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedTimeWindowCXSP

set_option autoImplicit false

/-!
# WindowNative：hSL1 rev2 ⇐ CC ∧ CE（O-CH11-NATIVE-WINDOW G1c，后缀 `_C11SP`）

R-C11-19 D-19-2 第一箭头 (D4′) + CC ⇒ WindowNative 的 tower 层装配。结论**逐字** = NATIVE-NJ G1 rev2
`P6NativeJetsV2C11SP.lean:45–118` 的 `hSL1` binder（生成器断言 `SL1body_rev2.txt` 逐行相等）。
**块状态 BLOCKED[CE]**（不是 PROVISIONAL）：
* `hCC` = NATIVE-CC 统一形（逐字 = `pairEDist_window_of_CC_record_C11SP` 的 binder，生成器断言）；
* `hCE`（core exclusion）：regular-crossing 像不落在 `window '' {‖z‖ ≤ TE}`。树内**推不出**：
  records 合取只有 `hasCanonicalWindow`（cap ⊆ window(‖x‖ ≤ TE)，单向），反向需
  `StaticCapWitness.HasRadialCoordinates`（StaticCapCoordinates:20），而 `PreparedSpatialState.records`
  不带径向坐标字段（`PreparedSpatialStep` 只把它存进 `nativeRecordHyp`）。repair target 见 state。
装配相对 Window:30 / HANDOVER v3 草案的三处偏离（lead 01:4x 批准）：
1. 乘性 first-exit（G1a/G1b），stay 半径 `X = C_buf^{2n₀+1}(d0+Δ)r`，TimeCore footprint
   `A′ = C_buf^{2n₀+1}·Afac`；
2. `β0 := min β0 θ̄`（CC 窗深 `θ·B ≤ θ̄`，取 `θ := β`、`B := m`）；
3. CC 只在子窗 `[v', t]` 上用，R ≤ 2mQ 与 crossing 分类都条件化在 stay 上。
trace 二分：`Nonempty` trace ⇒ alive；否则 `exists_cap_capture` 给 born event（`‖z‖ ≤ TE`），
born scale `≤ 4mQ` = 出生点 `R ≤ 2mQ`（`scalar_at_stage_time_le_two_mul_CXSP`）+ cap 标量下界。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- `C^k·y < ofReal (C^k·z)`（`C ≥ 1`，`y < ofReal z`）。 -/
theorem pow_mul_lt_ofReal_C11SP {C : ℝ} (hC : 1 ≤ C) (k : ℕ) {y : ℝ≥0∞} {z : ℝ}
    (h : y < ENNReal.ofReal z) :
    ENNReal.ofReal C ^ k * y < ENNReal.ofReal (C ^ k * z) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  rw [ENNReal.ofReal_mul (pow_nonneg hC0 k), ENNReal.ofReal_pow hC0]
  have h0 : ENNReal.ofReal C ^ k ≠ 0 :=
    pow_ne_zero _ (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hC)).ne'
  have hinf : ENNReal.ofReal C ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have h' := ENNReal.mul_lt_mul_left h0 hinf h
  rwa [mul_comm y, mul_comm (ENNReal.ofReal z)] at h'

/-- HEq 沿 stage 指标相等搬运 trace 点。 -/
theorem point_heq_of_eq_C11SP {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {y : (H.stage last).Carrier} (B : BackwardPointTrace H first last hle y)
    {j k : Fin (H.eventCount + 1)} (hjk : j = k) (h1 : first ≤ j) (h2 : j ≤ last)
    (h1' : first ≤ k) (h2' : k ≤ last) : HEq (B.point j h1 h2) (B.point k h1' h2') := by
  subst hjk
  rfl

/-- **G1c（BLOCKED[CE]）**：`hSL1 rev2`（NATIVE-NJ V2 binder 逐字）⇐ CC（统一形）∧ CE。 -/
theorem native_trace_window_of_CC_CE_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
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
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)} ≤ n₀)
    (hCE : ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        ∀ (n : ℕ) (e : Fin (F.tower.history n).eventCount)
          (pm : ((F.tower.history n).toHistory.stage e.castSucc).Carrier)
          (pp : ((F.tower.history n).toHistory.stage e.succ).Carrier),
          ((F.tower.history n).toHistory.event e).RegularCrossing pm pp →
          ∀ (b : ((F.tower.history n).toHistory.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd → ((records n e).static b).window z ≠ pp) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ,
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
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
      let Cbuf : ℝ := max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
            (StandardCap.transitionEnd + 11) ^ 2)))
        (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 : ℝ, 4 ≤ H0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ m : ℝ, 1 / 2 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (m + 1)) / Real.sqrt Q
        let β := β0 / (m + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r < q.neckRadius t →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ x : (H.stageAt t).Carrier,
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) →
        (∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt <
                ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r)) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                ENNReal.ofReal Cbuf ^ (2 * n₀) *
                  (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                    ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)))) ∨
        ∃ (u : Icc (0 : ℝ) H.horizon) (hau : aSeed ≤ u) (hut : u ≤ t),
          (t : ℝ) - β / Q < u ∧
          ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
          ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
            (H.activeStage_mono hut) x,
          (let A := seedTrace.restrictFirst (H.activeStage_mono hau) (H.activeStage_mono hut)
           ∀ (v : Icc (0 : ℝ) H.horizon) (huv : u ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hut) B v huv hvt <
              ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r))) ∧
          ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            HEq (((records n e).static b).window z)
              (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
            ((records n e).static b).neck.scale ≤ 4 * (m * Q) := by
  obtain ⟨εC, hεC, θbar, n₀, hθbar, hCCm⟩ := hCC
  obtain ⟨εF, hεF, hfirst⟩ := exists_pair_firstExit_native_C11SP.{u}
  obtain ⟨εL, hεL, hlow⟩ := exists_capWindow_scalar_lower_C11G.{u}
  obtain ⟨a₀, ha₀, hHI⟩ := exists_history_pinching_of_records_CXSP P g
  refine ⟨min εC (min εF εL), lt_min hεC (lt_min hεF hεL), n₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb params records hmR hmO hmA
    hpar hcan hOld hdecay hrecent Cbuf Afac hA
  have haccC : pBase.modelAccuracy ≤ εC := hacc.trans (min_le_left _ _)
  have haccF : params.modelAccuracy ≤ εF := by
    rw [hmA]
    exact hacc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have haccL : params.modelAccuracy ≤ εL := by
    rw [hmA]
    exact hacc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hord' : 2 ≤ params.modelOrder := by rwa [hmO]
  have hrad' : StandardCap.transitionEnd + 10 < params.modelRadius := by
    rw [hmR]
    unfold capWindowRadius_C11E at hrad
    linarith only [hrad, StandardCap.transitionEnd_pos]
  have hCb1 : (1 : ℝ) ≤ Cbuf := one_le_cbuf_C11SP params.modelRadius
  have hCb0 : (0 : ℝ) < Cbuf := zero_lt_one.trans_le hCb1
  have hCN1 : (1 : ℝ) ≤ Cbuf ^ (2 * n₀ + 1) := one_le_pow₀ hCb1
  have hA0 : 0 < Afac := zero_lt_one.trans hA
  have hA' : 0 < Cbuf ^ (2 * n₀ + 1) * Afac := mul_pos (by positivity) hA0
  obtain ⟨KG, TG, _hKG, hTG, hGood⟩ := seedGoodWindow_of_timeCore_P6TC hb hA'
  let Kwin := max 4 (10000 * KG)
  let H0 := max 4 (2 * Kwin)
  have hH0 : 4 ≤ H0 := le_max_left _ _
  have hKw : 2 * Kwin ≤ H0 := le_max_right _ _
  refine ⟨H0, hH0, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨k0, lam0, β0, _hk0, hlam0, hβ0, hscale⟩ :=
    exists_uniform_seed_window_scale_CXSP hH0 Ctime C2.toNNReal hΔ hγ
  refine ⟨lam0, min β0 θbar, hlam0, lt_min hβ0 hθbar, ?_⟩
  intro m hm
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  obtain ⟨TC, hTC, hcc⟩ := hCCm S F hTower q hdiag haccC hrad hord params records hmR hmO hmA
    hpar hcan hOld hdecay hrecent m hmpos
  refine ⟨max (2 * TG) TC, (mul_pos (by norm_num) hTG).trans_le (le_max_left _ _), ?_⟩
  intro n H t p r Q ell β ht htime hsmall hvol hguard aSeed haT hclock seedTrace x
    hscalar hdist
  have hr : 0 < r := hsmall.1
  have hi : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hr)
  obtain ⟨hQ, _hML, hqlo, hqM, hHIeq⟩ := seed_survival_thresholds_CXSP hH0 hKw hm hr
  obtain ⟨hell, htau0, htauR0, hage0, _hellR, hellγ, hgrad, hKell, _hKr, hHI0, hbudget0,
    hdrift0⟩ := hscale m hm r t hr htime
  -- β0 收缩：tau' = β/Q ≤ tau
  have hm1 : 0 < m + 1 := by linarith only [hmpos]
  have hβ : 0 < β := div_pos (lt_min hβ0 hθbar) hm1
  have hββ : β ≤ β0 / (m + 1) := div_le_div_of_nonneg_right (min_le_left _ _) hm1.le
  have hβθ : β * m ≤ θbar := by
    have h1 : β * m ≤ min β0 θbar := by
      change min β0 θbar / (m + 1) * m ≤ min β0 θbar
      rw [div_mul_eq_mul_div, div_le_iff₀ hm1]
      exact mul_le_mul_of_nonneg_left (lt_add_one m).le (lt_min hβ0 hθbar).le
    exact h1.trans (min_le_right _ _)
  let tau := β / Q
  have htau : 0 < tau := div_pos hβ hQ
  have htt : tau ≤ (β0 / (m + 1)) / Q := div_le_div_of_nonneg_right hββ hQ.le
  have htauR : tau ≤ r ^ 2 / 4 := htt.trans htauR0
  have hbudget : (Ctime : ℝ) * (m * Q) * tau ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left htt (mul_nonneg Ctime.coe_nonneg (by positivity))).trans hbudget0
  have hdrift : 8 * tau / ell < Δ * r :=
    (div_le_div_of_nonneg_right (by linarith only [htt]) hell.le).trans_lt hdrift0
  let a : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) - tau,
    ⟨by nlinarith only [htime, htauR, sq_nonneg r],
      (sub_le_self _ htau.le).trans t.2.2⟩⟩
  have hage : 1 ≤ Q * (a : ℝ) :=
    hage0.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left htt _) hQ.le)
  have haa : aSeed ≤ a := by
    change (aSeed : ℝ) ≤ (t : ℝ) - tau
    rw [hclock]
    nlinarith only [htauR, sq_nonneg r]
  have hat : a ≤ t := sub_le_self _ htau.le
  have hhalf : (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) := by
    change (t : ℝ) - r ^ 2 / 2 ≤ (t : ℝ) - tau
    nlinarith only [htauR, sq_nonneg r]
  have hta : (t : ℝ) - a = tau := sub_sub_cancel _ _
  have hdepth : Q * ((t : ℝ) - a) = β := by
    rw [hta]
    exact mul_div_cancel₀ _ hQ.ne'
  obtain ⟨hregion, hmargin⟩ := seed_survival_margin_CXSP hd0 hΔ hr hell htau.le
    hbuffer hellγ hdrift hdist
  have hregion' : Cbuf ^ (2 * n₀ + 1) * ((d0 + Δ) * r) + 2 * ell ≤
      Cbuf ^ (2 * n₀ + 1) * Afac * r := by
    have h1 : Cbuf ^ (2 * n₀ + 1) * ((d0 + Δ) * r) + 2 * ell ≤
        Cbuf ^ (2 * n₀ + 1) * ((d0 + Δ) * r + 2 * ell) := by nlinarith only [hCN1, hell]
    have h2 := mul_le_mul_of_nonneg_left hregion (zero_le_one.trans hCN1)
    linarith only [h1, h2]
  have hQnr : (q.neckRadius t ^ 2)⁻¹ < Q := by
    have hnr : 0 < q.neckRadius t := hr.trans hguard
    have h1 : (q.neckRadius t ^ 2)⁻¹ < (r ^ 2)⁻¹ :=
      inv_strictAnti₀ (sq_pos_of_pos hr) (pow_lt_pow_left₀ hguard hr.le two_ne_zero)
    exact h1.trans_le (le_mul_of_one_le_left hi.le (by linarith only [hH0]))
  have hseedQ : 3 / r ^ 2 < Q / 2 := by
    have h4 : 4 * (r ^ 2)⁻¹ ≤ Q / 2 :=
      (mul_le_mul_of_nonneg_right (le_max_left 4 (10000 * KG)) hi.le).trans hqlo
    rw [div_eq_mul_inv]
    exact (mul_lt_mul_of_pos_right (by norm_num : (3 : ℝ) < 4) hi).trans_le h4
  have hqG : (10000 * KG) * (r ^ 2)⁻¹ ≤ Q / 2 :=
    (mul_le_mul_of_nonneg_right (le_max_right 4 (10000 * KG)) hi.le).trans hqlo
  have hMpos : 0 < m * Q := mul_pos hmpos hQ
  have hvol' : ENNReal.ofReal ((Cbuf ^ (2 * n₀ + 1) * Afac)⁻¹ * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) p r := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvol
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact inv_anti₀ hA0 (le_mul_of_one_le_left hA0.le hCN1)
  have hTGt : 2 * TG ≤ (t : ℝ) := (le_max_left _ _).trans ht
  have hTCt : TC ≤ (t : ℝ) := (le_max_right _ _).trans ht
  -- 窗 [u, t] 上的 native first-exit（alive：u = a；born：u = 出生时刻）
  have hwin (u : Icc (0 : ℝ) H.horizon) (hau : a ≤ u) (hut : u ≤ t)
      (B : BackwardPointTrace H (H.activeStage u) (H.activeStage t) (H.activeStage_mono hut) x) :
      let A := seedTrace.restrictFirst (H.activeStage_mono (haa.trans hau))
        (H.activeStage_mono hut)
      ∀ (v : Icc (0 : ℝ) H.horizon) (huv : u ≤ v) (hvt : v ≤ t),
        A.pairEDist_CXSP (hat := hut) B v huv hvt <
            ENNReal.ofReal (Cbuf ^ (2 * n₀ + 1) * ((d0 + Δ) * r)) ∧
          A.pairEDist_CXSP (hat := hut) B v huv hvt ≤
            ENNReal.ofReal Cbuf ^ (2 * n₀) * (A.pairEDist_CXSP (hat := hut) B t hut le_rfl +
              ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v))) := by
    intro A
    have hseed (w : Icc (0 : ℝ) H.horizon) (huw : u ≤ w) (hwt : w ≤ t) :
        metricScalarAt (H.stageMetric (H.activeStage w) w)
          (A.point (H.activeStage w) (H.activeStage_mono huw) (H.activeStage_mono hwt)) ≤
            3 / r ^ 2 :=
      H.seed_scalar_le_of_smallParabolic_C11G haT hsmall hclock seedTrace w
        (haa.trans (hau.trans huw)) hwt _ rfl _ _
    have hscalarA : metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ m * Q := by
      have hs := hseed t hut le_rfl
      rw [A.endpoint_eq] at hs
      exact hs.trans (hseedQ.le.trans hqM)
    have hdt : A.pairEDist_CXSP (hat := hut) B t hut le_rfl =
        riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x := by
      unfold BackwardPointTrace.pairEDist_CXSP
      rw [A.endpoint_eq, B.endpoint_eq]
    have hmarginU : A.pairEDist_CXSP (hat := hut) B t hut le_rfl +
        ENNReal.ofReal ((8 / ell) * ((t : ℝ) - u)) < ENNReal.ofReal ((d0 + Δ) * r) := by
      rw [hdt]
      refine lt_of_le_of_lt (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)) hmargin
      rw [← hta]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left (show (a : ℝ) ≤ u from hau) _)
        (div_nonneg (by norm_num) hell.le)
    have hgoodAt (w : Icc (0 : ℝ) H.horizon) (huw : u ≤ w) (hwt : w ≤ t)
        (z : (H.stageAt w).Carrier)
        (hz : z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
          (A.point (H.activeStage w) (H.activeStage_mono huw) (H.activeStage_mono hwt))
          (Cbuf ^ (2 * n₀ + 1) * Afac * r))
        (hR : Q / 2 ≤ metricScalarAt (H.stageMetric (H.activeStage w) w) z) :
        H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime w z :=
      hGood n t p r hTGt htime hsmall hvol' aSeed haT hclock seedTrace w
        (haa.trans (hau.trans huw)) hwt (hhalf.trans (hau.trans huw)) z hz (hqG.trans hR)
    have hXle : ENNReal.ofReal (Cbuf ^ (2 * n₀ + 1) * ((d0 + Δ) * r)) ≤
        ENNReal.ofReal (Cbuf ^ (2 * n₀ + 1) * Afac * r) :=
      ENNReal.ofReal_le_ofReal (by linarith only [hregion', hell])
    have hres := hfirst hut A B (records n) (hcan n) haccF hord' hrad'
      (hCE S F hTower params records hcan n) n₀ (Cb := Cbuf) rfl
      (qcan := Q / 2) (M := m * Q) (Q := Q) (a₀ := a₀) (K := (k0 * (m + 1)) * Q)
      (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime) (Cgrad := C2.toNNReal)
      hMpos hqM hscalarA hscalar
      ((mul_le_mul_of_nonneg_left (sub_le_sub_left (show (a : ℝ) ≤ u from hau) _)
        (mul_nonneg Ctime.coe_nonneg hMpos.le)).trans (hta ▸ hbudget))
      (fun a' hua' ha't y A' hR => hcc n β hβ hβθ t hTCt Q hQnr a' ha't
        (by
          have h1 : (t : ℝ) - a' ≤ (t : ℝ) - a :=
            sub_le_sub_left (show (a : ℝ) ≤ a' from hau.trans hua') _
          rw [hta] at h1
          exact h1)
        y A' (fun v hav hvt => (hR v hav hvt).trans_eq (by ring)))
      hell (X := ENNReal.ofReal (Cbuf ^ (2 * n₀ + 1) * ((d0 + Δ) * r))) ha₀.le hQ
      (hage.trans (mul_le_mul_of_nonneg_left hau hQ.le)) hgrad hKell
      (hHIeq.trans_le hHI0)
      (by
        have h := pow_mul_lt_ofReal_C11SP hCb1 (2 * n₀ + 1) hmarginU
        refine lt_of_eq_of_lt ?_ h
        rw [pow_succ' (ENNReal.ofReal Cbuf) (2 * n₀), mul_assoc])
      (fun v _ _ hstay w haw hwt hvw hwtlt z hz hR => by
        rcases hz with rfl | rfl
        · exact False.elim ((not_le_of_gt ((hseed w haw hwt).trans_lt hseedQ)) hR)
        · exact hgoodAt w haw hwt _ ((hstay w haw hwt hvw hwtlt).trans_le hXle) hR)
      (fun v _ _ hstay w haw hwt hvw hwtlt _hage z hz hR ξ =>
        pair_ball_gradient_of_spatial_CXSP (H.stageMetric (H.activeStage w) w) _ _ hell
          (hstay w haw hwt hvw hwtlt) hregion'
          (fun y hy hyR => by
            obtain ⟨W, _hchart⟩ := (hgoodAt w haw hwt y hy hyR).1
            exact ⟨W⟩) z hz hR ξ)
      (fun _v _ _ _ w _ _ _ _ _ z _ => hHI F n (records n) w z)
    exact hres
  -- 第一行 ⇐ 第二行 + 余量
  have hline1 (u : Icc (0 : ℝ) H.horizon) (hau : a ≤ u) (hut : u ≤ t)
      (B : BackwardPointTrace H (H.activeStage u) (H.activeStage t) (H.activeStage_mono hut) x)
      (v : Icc (0 : ℝ) H.horizon) (huv : u ≤ v) (hvt : v ≤ t) :
      (seedTrace.restrictFirst (H.activeStage_mono (haa.trans hau))
        (H.activeStage_mono hut)).pairEDist_CXSP (hat := hut) B v huv hvt <
        ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r)) := by
    let A := seedTrace.restrictFirst (H.activeStage_mono (haa.trans hau)) (H.activeStage_mono hut)
    have h2 := (hwin u hau hut B v huv hvt).2
    have hdt : A.pairEDist_CXSP (hat := hut) B t hut le_rfl =
        riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x := by
      unfold BackwardPointTrace.pairEDist_CXSP
      rw [A.endpoint_eq, B.endpoint_eq]
    have hy : A.pairEDist_CXSP (hat := hut) B t hut le_rfl +
        ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)) < ENNReal.ofReal ((d0 + Δ) * r) := by
      rw [hdt]
      refine lt_of_le_of_lt (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)) hmargin
      rw [← hta]
      exact mul_le_mul_of_nonneg_left
        (sub_le_sub_left ((show (a : ℝ) ≤ u from hau).trans huv) _)
        (div_nonneg (by norm_num) hell.le)
    exact h2.trans_lt (pow_mul_lt_ofReal_C11SP hCb1 (2 * n₀) hy)
  by_cases hex : Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) x)
  · obtain ⟨B⟩ := hex
    refine Or.inl ⟨a, haa, hat, rfl, hdepth, B, ?_⟩
    intro _A v hav hvt
    exact ⟨hline1 a le_rfl hat B v hav hvt, (hwin a le_rfl hat B v hav hvt).2⟩
  · have hempty := not_nonempty_iff.mp hex
    obtain ⟨j, hf, hl, Bj, b, _z0, z, _hno, _hcap, hnorm, hpoint⟩ :=
      H.exists_cap_capture (records n) (hcan n) (H.activeStage_mono hat) x hempty
    let u := H.stageTime j.succ
    have hact : H.activeStage u = j.succ := H.activeStage_stageTime _
    have hau : a ≤ u := (lt_time_succ_of_activeStage_le_C11SP a j hf).le
    have hut : u ≤ t :=
      (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)
    let B' := Bj.restrictFirst (le_of_eq hact.symm) (H.activeStage_mono hut)
    have hwinU := hwin u hau hut B'
    refine Or.inr ⟨u, haa.trans hau, hut, ?_, j, rfl, hact.symm, B', ?_, b, z,
      hnorm.trans (le_add_of_nonneg_right (by norm_num)), ?_, ?_⟩
    · have h1 := lt_time_succ_of_activeStage_le_C11SP a j hf
      change (t : ℝ) - β / Q < H.time j.succ
      have h2 : (a : ℝ) = (t : ℝ) - β / Q := rfl
      linarith only [h1, h2]
    · intro _A v huv hvt
      exact hline1 u hau hut B' v huv hvt
    · exact (heq_of_eq hpoint.symm).trans
        (point_heq_of_eq_C11SP Bj hact.symm le_rfl hl _ _)
    · -- born scale：出生点 R ≤ 2mQ + cap 标量下界
      have hRb := B'.scalar_at_stage_time_le_two_mul_CXSP (s := (u : ℝ)) hut hMpos hqM
        (fun w huw hwt _huwl _hwtl hR =>
          hGood n t p r hTGt htime hsmall hvol' aSeed haT hclock seedTrace w
            (haa.trans (hau.trans huw)) hwt (hhalf.trans (hau.trans huw))
            (B'.point (H.activeStage w) (H.activeStage_mono huw) (H.activeStage_mono hwt))
            (((hwinU w huw hwt).1).trans_le
              (ENNReal.ofReal_le_ofReal (by linarith only [hregion', hell])))
            (hqG.trans hR)) hscalar
        ((mul_le_mul_of_nonneg_left (sub_le_sub_left (show (a : ℝ) ≤ u from hau) _)
          (mul_nonneg Ctime.coe_nonneg hMpos.le)).trans (hta ▸ hbudget))
        j.succ hact.le hl le_rfl le_rfl
      have hR2 : metricScalarAt (H.stageMetric j.succ (H.time j.succ))
          (Bj.point j.succ le_rfl hl) ≤ 2 * (m * Q) := hRb
      rw [H.stageMetric_succ_time_C11G, hpoint] at hR2
      have hRlow := hlow (H.event j) haccL hord' ((records n j).static b) (hcan n j b) z
        (hnorm.trans_lt (by linarith only [hrad']))
      linarith only [hR2, hRlow]

end GC.LongTime.Ch11
