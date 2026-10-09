import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TimeBoundedBallCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScalarAnchorCXSP

set_option autoImplicit false

/-!
# native bounded ball rev2（O-CH11-NATIVE-NJ G1 rev2，后缀 `_C11SP`；取代 G1 的 hSL1 形）

**`hSL1`**（native trace window；lead 批准形 + NATIVE-CC 对齐）= CXSP
`exists_prepared_time_trace_window_CXSP`（`P6PreparedTimeWindowCXSP:30`）的孪生：
* 删 `q.neckRadius t ≤ r`，换成 native `r < q.neckRadius t`；
* `∃ n₀ : ℕ` 紧跟 `∃ ε₀`（在 S 之前，与 NATIVE-CC CC 统一形同序）；records / params 块逐字取
  `exists_records_of_prepared_chain_CXSP`（同 NATIVE-CC `pairEDist_window_of_CC_C11SP`）；
* pair 距离第二行：`d_v ≤ C_buf^{2n₀} · (d_t + (8/ℓ)(t − v))`，`C_buf` 逐字 = NATIVE-CC
  `pairEDist_window_of_CC_C11SP` 结论里的显式常数（两条 trace ⇒ 指数 `2n₀`），`Λ = 8/ℓ`；
* 第一行（footprint）改为 `d_v < C_buf^{2n₀}·(d0+Δ)·r`（乘性 crossing 损失也作用在 `d_t`）；
  消费端用 TimeCore `∀A` 取 `A′ = C_buf^{2n₀}·Afac`（NATIVE-CC `timeCore_absorb_C11SP` 同款）；
* **born 分支**：trace 起于窗内某 event `e` 的 birth 时刻 `u`（`t − β/Q < u`），起点落在 `e` 某 static
  cap 的内窗 `‖z‖ ≤ transitionEnd + 10`，且 `neck.scale ≤ 4·(m·Q)`（G1b
  `exists_bornCap_scale_le_four_mul_C11SP` 的结论形）；第一行在 `[u, t]` 上成立。

**`native_boundedBall_of_SL1_v2_C11SP`**（PROVISIONAL[hSL1 rev2]）= G46
`exists_prepared_time_bounded_ball_CXSP` 的 native 孪生：footprint + G19 型 first-exit
（TimeCore good window，不含 nr）+ pinching 给 Rm 界，
结论是逐点二分：从 `a = t − β/Q` 活到底的 Rm-bounded trace，或 born 于 `a < u` 的 Rm-bounded trace
（带 cap 数据）。`u ≤ a` 的 born trace 截到 `a` 归入 alive。NJ 的余下装配（patch 不 straddle、
alive patch 用 TracedInnerJets、born patch 用 G3/G7 reset Shi + G63/G1b 初始 jets）见 state §G1。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **G1 rev2（PROVISIONAL[hSL1 rev2]）**：native bounded ball 逐点 alive / born 二分；footprint 乘性。 -/
theorem native_boundedBall_of_SL1_v2_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hSL1 :
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
            ((records n e).static b).neck.scale ≤ 4 * (m * Q)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
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
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 m0 : ℝ, 4 ≤ H0 ∧ 1 / 2 ≤ m0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ β0 : ℝ, 0 < β0 ∧
        ∀ m : ℝ, m0 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let Km := 2 * Real.sqrt 3 * ((2 * m) / 2 + max (2 * m) (2 * Real.exp 4))
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r < q.neckRadius t →
        ∀ (y : (H.stageAt t).Carrier) (Rad dCenter : ℝ), 0 < Rad → 0 ≤ dCenter →
          dCenter + Rad / Real.sqrt H0 ≤ d0 →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y ≤
            ENNReal.ofReal (dCenter * r) →
        let U := riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rad / Real.sqrt Q)
        (∀ x ∈ U, metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q) →
        0 < Rad / Real.sqrt Q ∧ 0 < (β0 / (m + 1)) / Q ∧
        ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), (a : ℝ) = (t : ℝ) - (β0 / (m + 1)) / Q ∧
          ∀ x ∈ U,
            (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
                (H.activeStage_mono hat) x, B.isRmBoundedBy (hat := hat) (Km * Q)) ∨
            ∃ (u : Icc (0 : ℝ) H.horizon) (hut : u ≤ t), a < u ∧
              ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
              ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
                  (H.activeStage_mono hut) x,
                B.isRmBoundedBy (hat := hut) (Km * Q) ∧
                ∃ (b : (H.event e).RetainedBoundaryIndex)
                  (z : standardCapWindow params.modelRadius),
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
                  HEq (((records n e).static b).window z)
                    (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
                  ((records n e).static b).neck.scale ≤ 4 * (m * Q) := by
  obtain ⟨ε₀, hε₀, n₀, hpoint⟩ := hSL1
  obtain ⟨a₀, ha₀, hHI⟩ := exists_history_pinching_of_records_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb params records hmR hmO hmA
    hpar hcanW hold hdel hrec Afac hA
  let Cb : ℝ := max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
      ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
        (StandardCap.transitionEnd + 11) ^ 2)))
    (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))
  have hCb1 : 1 ≤ Cb := by
    have hTE := StandardCap.transitionEnd_pos
    exact le_trans (by nlinarith only [hTE]) (le_max_right _ _)
  have hCpow1 : 1 ≤ Cb ^ (2 * n₀) := one_le_pow₀ hCb1
  let Awide : ℝ := Cb ^ (2 * n₀) * Afac
  have hAwide : Afac ≤ Awide := le_mul_of_one_le_left (zero_lt_one.trans hA).le hCpow1
  obtain ⟨KG, TG, _hKG, _hTG, hGood⟩ :=
    seedGoodWindow_of_timeCore_P6TC hb (zero_lt_one.trans (hA.trans_le hAwide))
  obtain ⟨H0, hH0, hpointA⟩ := hpoint S F q hTower hdiag hacc hrad hord hb params records hmR
    hmO hmA hpar hcanW hold hdel hrec Afac hA
  have hHpos : 0 < H0 := by linarith only [hH0]
  let m0 : ℝ := max (1 / 2) (1 + 10000 * KG / H0)
  refine ⟨H0, m0, hH0, le_max_left _ _, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨lam0, βold, _hlam0, hβold, hpointM⟩ := hpointA d0 Δ γ hd0 hΔ hγ hbuffer
  let β0 : ℝ := min βold (min (H0 / 4) (1 / (4 * ((Ctime : ℝ) + 1))))
  have hβ0 : 0 < β0 := by dsimp [β0]; positivity
  have hβoldle : β0 ≤ βold := min_le_left _ _
  have hβH : β0 ≤ H0 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hβtime : (Ctime : ℝ) * β0 ≤ 1 / 4 := by
    have h := (min_le_right βold _).trans
      (min_le_right (H0 / 4) (1 / (4 * ((Ctime : ℝ) + 1))))
    have hmul := (le_div_iff₀ (by positivity : 0 < 4 * ((Ctime : ℝ) + 1))).mp h
    nlinarith only [hmul, hβ0]
  refine ⟨β0, hβ0, ?_⟩
  intro m hm0
  have hm : 1 / 2 ≤ m := (le_max_left _ _).trans hm0
  have hmp : 0 < m := by linarith only [hm]
  have hden : 0 < m + 1 := by linarith only [hm]
  have hGoodCoef : 10000 * KG ≤ H0 * m := by
    have h := (le_max_right (1 / 2) (1 + 10000 * KG / H0)).trans hm0
    have hratio : 10000 * KG / H0 ≤ m := by linarith only [h]
    have hh := (div_le_iff₀ hHpos).mp hratio
    nlinarith only [hh]
  obtain ⟨TS, hTS, hpointN⟩ := hpointM m hm
  refine ⟨max (2 * TG) TS, hTS.trans_le (le_max_right _ _), ?_⟩
  intro n H t p r Q Km ht htime hsmall hvol hnat y Rad dCenter hRad hdCenter hfit hcenter
    U hscalar
  have hr : 0 < r := hsmall.1
  have hQ : 0 < Q := mul_pos hHpos (inv_pos.mpr (sq_pos_of_pos hr))
  have hM : 0 < m * Q := mul_pos hmp hQ
  have hsmallCopy := hsmall
  obtain ⟨_hr, aSeed, haT, hclock, hseed⟩ := hsmallCopy
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨seedTrace, _hcontrolled⟩ := hseed p hp
  have hdist (x : (H.stageAt t).Carrier) (hx : x ∈ U) :
      riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) := by
    have hx' : riemannianEDistOf (H.stageMetric (H.activeStage t) t) y x <
        ENNReal.ofReal (Rad / Real.sqrt Q) := hx
    exact seed_closedBall_distance_CXSP (H.stageMetric (H.activeStage t) t)
      hHpos hr hRad.le hdCenter hfit hcenter x hx'.le
  have hpointX (x : (H.stageAt t).Carrier) (hx : x ∈ U) :=
    hpointN n t p r ((le_max_right _ _).trans ht) htime hsmall hvol hnat
      aSeed haT hclock seedTrace x (hscalar x hx) (hdist x hx)
  let β : ℝ := β0 / (m + 1)
  have hβ : 0 < β := div_pos hβ0 hden
  have hβle : β ≤ βold / (m + 1) := div_le_div_of_nonneg_right hβoldle hden.le
  have hβH' : β ≤ H0 / 4 :=
    (div_le_self hβ0.le (by linarith only [hm] : 1 ≤ m + 1)).trans hβH
  have htau : 0 < β / Q := div_pos hβ hQ
  have htauR : β / Q ≤ r ^ 2 / 4 := calc
    β / Q ≤ (H0 / 4) / Q := div_le_div_of_nonneg_right hβH' hQ.le
    _ = r ^ 2 / 4 := by dsimp only [Q]; field_simp [hHpos.ne', hr.ne']
  let a : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) - β / Q,
    ⟨by nlinarith only [htime, htauR, sq_nonneg r], (sub_le_self _ htau.le).trans t.2.2⟩⟩
  have haa : aSeed ≤ a := by
    change (aSeed : ℝ) ≤ (t : ℝ) - β / Q
    rw [hclock]
    nlinarith only [htauR, sq_nonneg r]
  have hat : a ≤ t := sub_le_self _ htau.le
  have hhalf : (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) := by
    change (t : ℝ) - r ^ 2 / 2 ≤ (t : ℝ) - β / Q
    nlinarith only [htauR, sq_nonneg r]
  have haClock : (a : ℝ) = (t : ℝ) - β / Q := rfl
  have hQa : 1 ≤ Q * (a : ℝ) := by
    have hra : r ^ 2 ≤ (a : ℝ) := by
      rw [haClock]
      nlinarith only [htime, htauR, sq_nonneg r]
    have hmul := mul_le_mul_of_nonneg_left hra hQ.le
    have hQr : Q * r ^ 2 = H0 := by dsimp only [Q]; field_simp [hr.ne']
    rw [hQr] at hmul
    linarith only [hmul, hH0]
  have hbudget : Ctime * (m * Q) * ((t : ℝ) - a) ≤ 1 / 2 := by
    have heq : (m + 1) * β = β0 := mul_div_cancel₀ _ hden.ne'
    have hmb : m * β ≤ β0 := by nlinarith only [heq, hβ]
    have htb := (mul_le_mul_of_nonneg_left hmb Ctime.coe_nonneg).trans hβtime
    have hc : Ctime * (m * Q) * ((t : ℝ) - a) = Ctime * (m * β) := by
      rw [haClock, sub_sub_cancel]
      field_simp [hQ.ne']
    rw [hc]
    linarith only [htb]
  have hGoodThreshold : (10000 * KG) * (r ^ 2)⁻¹ ≤ m * Q := by
    have hmul := mul_le_mul_of_nonneg_right hGoodCoef (inv_nonneg.mpr (sq_nonneg r))
    dsimp only [Q]
    nlinarith only [hmul]
  have key : ∀ (c : Icc (0 : ℝ) H.horizon) (hac : a ≤ c) (hct : c ≤ t)
      (x : (H.stageAt t).Carrier), x ∈ U →
      ∀ Bc : BackwardPointTrace H (H.activeStage c) (H.activeStage t)
        (H.activeStage_mono hct) x,
      (∀ (v : Icc (0 : ℝ) H.horizon) (hcv : c ≤ v) (hvt : v ≤ t),
        (seedTrace.restrictFirst (H.activeStage_mono (haa.trans hac))
          (H.activeStage_mono hct)).pairEDist_CXSP (hat := hct) Bc v hcv hvt <
            ENNReal.ofReal (Cb ^ (2 * n₀) * ((d0 + Δ) * r))) →
      Bc.isRmBoundedBy (hat := hct) (Km * Q) := by
    intro c hac hct x hx Bc hrow
    have hca : (a : ℝ) ≤ c := hac
    have hbudgetc : Ctime * (m * Q) * ((t : ℝ) - c) ≤ 1 / 2 := by
      have hle : (t : ℝ) - c ≤ (t : ℝ) - a := sub_le_sub_left hca _
      have hnn : 0 ≤ (Ctime : ℝ) * (m * Q) := by positivity
      exact (mul_le_mul_of_nonneg_left hle hnn).trans hbudget
    have hQc : 1 ≤ Q * (c : ℝ) := hQa.trans (mul_le_mul_of_nonneg_left hca hQ.le)
    have hcontrol := Bc.scalar_le_two_mul_of_time_local_derivative_control hct hM
      (fun v hcv hvt hage htop hRv => by
        have hfoot : Bc.point (H.activeStage v) (H.activeStage_mono hcv)
            (H.activeStage_mono hvt) ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono ((haa.trans hac).trans hcv))
              (H.activeStage_mono hvt)) (Awide * r) := by
          refine (hrow v hcv hvt).trans_le (ENNReal.ofReal_le_ofReal ?_)
          have hdA : d0 + Δ ≤ Afac := by linarith only [hbuffer, hγ]
          have h1 := mul_le_mul_of_nonneg_right hdA hr.le
          have h2 := mul_le_mul_of_nonneg_left h1 (zero_le_one.trans hCpow1)
          calc Cb ^ (2 * n₀) * ((d0 + Δ) * r) ≤ Cb ^ (2 * n₀) * (Afac * r) := h2
            _ = Awide * r := by ring
        have hGoodV := hGood n t p r ((le_max_left _ _).trans ht)
          htime hsmall (seed_volume_of_parameter_le_CXSP hsmall (zero_lt_one.trans hA) hAwide hvol)
          aSeed haT hclock seedTrace v ((haa.trans hac).trans hcv) hvt
          (hhalf.trans (hca.trans (show (c : ℝ) ≤ v from hcv))) _ hfoot
          (hGoodThreshold.trans_lt hRv).le
        exact hGoodV.2 hage htop) (hscalar x hx) hbudgetc
    exact Bc.isRmBoundedBy_of_scalar_and_HI_CXSP ha₀.le hQ (by positivity) hQc
      (fun v z => hHI F n (records n) v z)
      (fun v hcv hvt => by simpa only [mul_assoc] using hcontrol v hcv hvt)
  refine ⟨div_pos hRad (Real.sqrt_pos.mpr hQ), htau, a, hat, rfl, ?_⟩
  intro x hx
  rcases hpointX x hx with ⟨ax, _haxSeed, _haxt, hxClock, _hxDepth, Bold, hBold⟩ |
    ⟨u, hau, hut, _hlt, e, he1, he2, Bu, hrow, b, z, hz, hw, hsc⟩
  · have haxa : ax ≤ a := by
      change (ax : ℝ) ≤ (t : ℝ) - β / Q
      rw [hxClock]
      exact sub_le_sub_left (div_le_div_of_nonneg_right hβle hQ.le) _
    exact Or.inl ⟨Bold.restrictFirst (H.activeStage_mono haxa) (H.activeStage_mono hat),
      key a le_rfl hat x hx _ (fun v hav hvt => (hBold v (haxa.trans hav) hvt).1)⟩
  · by_cases hua : u ≤ a
    · exact Or.inl ⟨Bu.restrictFirst (H.activeStage_mono hua) (H.activeStage_mono hat),
        key a le_rfl hat x hx _ (fun v hav hvt => hrow v (hua.trans hav) hvt)⟩
    · have hau' : a < u := lt_of_not_ge hua
      exact Or.inr ⟨u, hut, hau', e, he1, he2, Bu,
        key u hau'.le hut x hx Bu (fun v huv hvt => hrow v huv hvt), b, z, hz, hw, hsc⟩

end GC.LongTime.Ch11
