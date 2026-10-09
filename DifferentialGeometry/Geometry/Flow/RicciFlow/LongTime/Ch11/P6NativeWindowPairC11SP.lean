import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeWindowExitC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceAnalyticFirstExitCXSP

set_option autoImplicit false

/-!
# native pair first-exit（history 层；O-CH11-NATIVE-WINDOW G1b，后缀 `_C11SP`）

CXSP G20 `exists_pair_firstExit_of_local_analytic_CXSP` 的 native 孪生：删 `hscale`
（全部 crossed cap `scale > 4M`，来自 `nr ≤ r`），换成
* **crossing 分类**（条件化在 stay 上）：`scale > 4M` 的 cap 由 G19 保护
  `exists_trace_protection_of_good_suffix_CXSP` 排除；`scale ≤ 4M` 的 cap 内窗点由 `hCE`（core exclusion：
  regular-crossing 像不在 `window '' {‖z‖ ≤ TE}`）落进 buffer `TE < ‖z‖ ≤ TE + 10`；
* **CC 计数** `hcount`（= CC 合同结论在本 history、本窗的特化；子窗 `[v', t]` 上用）；
* **乘性链**：子窗 `[v', t]`（`v'` 与 `v` 同 stage，严格在 `v` 右侧，使 R ≤ 2M 在整个子窗成立）上
  NATIVE-CC `pairEDist_window_of_largeCap_count_record_C11SP`，再加 `[v, v']` 的 slab drift；
* first-exit = G1a `pair_distance_of_unexited_suffix_mul_C11SP`（buffer crossing 左延拓用
  NATIVE-SHORT `surgery_no_shortcut_buffer_of_record_C11SP`）。
**PROVED**（`hCE`、`hcount` 是本 history 层引理的前提，由 tower 层装配供给）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- `activeStage w ≤ e⁻` ⇒ `w < time e⁺`。 -/
theorem lt_time_succ_of_activeStage_le_C11SP {H : ObservedHistory.{u}}
    (w : Icc (0 : ℝ) H.horizon) (e : Fin H.eventCount) (hf : H.activeStage w ≤ e.castSucc) :
    (w : ℝ) < H.time e.succ := by
  by_contra h
  have he := H.le_activeStage w e.succ (le_of_not_gt h)
  exact (not_le_of_gt e.castSucc_lt_succ) (he.trans hf)

/-- 同 stage 的严格右点：`v < t` ⇒ `∃ v' ∈ (v, t)`，`activeStage v' = activeStage v`。 -/
theorem exists_right_sameStage_C11SP {H : ObservedHistory.{u}}
    (v t : Icc (0 : ℝ) H.horizon) (hvt : v < t) :
    ∃ v' : Icc (0 : ℝ) H.horizon, v < v' ∧ v' < t ∧ H.activeStage v' = H.activeStage v := by
  have hnext : ∃ τ : ℝ, (v : ℝ) < τ ∧ τ ≤ t ∧
      ∀ e : Fin H.eventCount, H.activeStage v = e.castSucc → τ ≤ H.time e.succ := by
    by_cases hc : ∃ e : Fin H.eventCount, H.activeStage v = e.castSucc
    · obtain ⟨e, he⟩ := hc
      refine ⟨min (t : ℝ) (H.time e.succ),
        lt_min hvt (H.lt_time_succ_of_activeStage_eq_C11D v e he), min_le_left _ _, ?_⟩
      intro e' he'
      obtain rfl : e = e' := Fin.castSucc_injective _ (he.symm.trans he')
      exact min_le_right _ _
    · exact ⟨t, hvt, le_rfl, fun e he => absurd ⟨e, he⟩ hc⟩
  obtain ⟨τ, hvτ, hτt, hτ⟩ := hnext
  let v' : Icc (0 : ℝ) H.horizon :=
    ⟨((v : ℝ) + τ) / 2, by linarith [v.2.1], by linarith [t.2.2]⟩
  have h1 : (v : ℝ) < v' := by change (v : ℝ) < ((v : ℝ) + τ) / 2; linarith
  have h2 : ((v' : ℝ)) < τ := by change ((v : ℝ) + τ) / 2 < τ; linarith
  refine ⟨v', h1, h2.trans_le hτt, ?_⟩
  exact H.activeStage_eq_of_regular_stage_CXSP v' (H.activeStage v)
    ((H.activeStage_time_le v).trans h1.le) (fun e he => h2.trans_le (hτ e he))

/-- `C_buf ≥ 1`。 -/
theorem one_le_cbuf_C11SP (D : ℝ) :
    (1 : ℝ) ≤ max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((D - (StandardCap.transitionEnd + 10)) /
            (StandardCap.transitionEnd + 11) ^ 2)))
        (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13)) := by
  have hte := StandardCap.transitionEnd_pos
  refine le_max_of_le_right ?_
  nlinarith

/-- crossing 分类（PROVED）：stay 后缀上的 Good（`s ≤ τ_e`）+ G19 保护 + `hCE` ⇒ 每个 crossed
端点受保护，或在某 `scale ≤ 4M` 的 cap buffer `TE < ‖z‖ ≤ TE + 10`。 -/
theorem crossing_class_of_good_suffix_C11SP {ε₀ : ℝ}
    (hprotect : ∀ {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
        {p : (H.stageAt t).Carrier}
        (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) p)
        {params : CutoffParameters}
        (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params),
        params.modelAccuracy ≤ ε₀ → 2 ≤ params.modelOrder →
        (∀ e b, ((records e).static b).hasCanonicalWindow) →
        StandardCap.transitionEnd + 10 < params.modelRadius →
        ∀ {ε C1 C2 q M s : ℝ} {Ctime : ℝ≥0}, 0 < M → q ≤ M →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          s < (v : ℝ) → (v : ℝ) < t →
          q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
          H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) →
        metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M →
        Ctime * M * ((t : ℝ) - s) ≤ 1 / 2 →
        ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
          (hl : e.succ ≤ H.activeStage t), s ≤ H.time e.succ →
          ∀ b, 4 * M < ((records e).static b).neck.scale →
          A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
            ((records e).static b).window ''
              {z : standardCapWindow params.modelRadius |
                ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {p : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {params : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
    (hacc : params.modelAccuracy ≤ ε₀) (hm : 2 ≤ params.modelOrder)
    (hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
    (hD : StandardCap.transitionEnd + 10 < params.modelRadius)
    (hCE : ∀ (e : Fin H.eventCount) (pm : (H.stage e.castSucc).Carrier)
      (pp : (H.stage e.succ).Carrier), (H.event e).RegularCrossing pm pp →
      ∀ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        ‖z.val‖ ≤ StandardCap.transitionEnd → ((records e).static b).window z ≠ pp)
    {ε C1 C2 q M s : ℝ} {Ctime : ℝ≥0} (hM : 0 < M) (hqM : q ≤ M)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      s < (v : ℝ) → (v : ℝ) < t →
      q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)))
    (hscalar : metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - s) ≤ 1 / 2)
    (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
    (hl : e.succ ≤ H.activeStage t) (hse : s ≤ H.time e.succ) :
    (∀ b, A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉ ((records e).static b).window ''
      {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
    ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
      StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
      ((records e).static b).window z = A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
      ((records e).static b).neck.scale ≤ 4 * M := by
  by_cases hin : ∃ b, A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∈
      ((records e).static b).window ''
        {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}
  · obtain ⟨b, z, hz, hzeq⟩ := hin
    refine Or.inr ⟨b, z, ?_, hz, hzeq, ?_⟩
    · by_contra hle
      exact hCE e _ _ (A.crossing e hf hl) b z (le_of_not_gt hle) hzeq
    · by_contra hlt
      exact hprotect hat A records hacc hm hcan hD hM hqM hgood hscalar htime e hf hl hse b
        (lt_of_not_ge hlt) ⟨z, hz, hzeq⟩
  · exact Or.inl fun b hb => hin ⟨b, hb⟩

/-- **G1b（PROVED）native pair first-exit**：G20 孪生，`hscale` 换成 crossing 分类（G19 保护 + `hCE`）
+ CC 计数 `hcount` + 乘性 first-exit；结论 `d_v < X` 且 `d_v ≤ C_buf^{2n₀}(d_t + (8/ℓ)(t − v))`。 -/
theorem exists_pair_firstExit_native_C11SP :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
        {p q : (H.stageAt t).Carrier}
        (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) p)
        (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) q)
        {params : CutoffParameters}
        (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
        (_hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
        (_hacc : params.modelAccuracy ≤ ε₀) (_hm : 2 ≤ params.modelOrder)
        (_hD : StandardCap.transitionEnd + 10 < params.modelRadius)
        (_hCE : ∀ (e : Fin H.eventCount) (pm : (H.stage e.castSucc).Carrier)
          (pp : (H.stage e.succ).Carrier), (H.event e).RegularCrossing pm pp →
          ∀ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd → ((records e).static b).window z ≠ pp)
        (n₀ : ℕ) {Cb : ℝ}
        (_hCb : Cb = max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
            (StandardCap.transitionEnd + 11) ^ 2)))
          (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13)))
        {ε C1 C2 qcan M Q a₀ K : ℝ} {Ctime Cgrad : ℝ≥0} (_hM : 0 < M) (_hqM : qcan ≤ M)
        (_hscalarA : metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M)
        (_hscalarB : metricScalarAt (H.stageMetric (H.activeStage t) t) q ≤ M)
        (_htime : Ctime * M * ((t : ℝ) - a) ≤ 1 / 2)
        (_hcount : ∀ (a' : Icc (0 : ℝ) H.horizon) (_haa' : a ≤ a') (ha't : a' ≤ t)
          (y : (H.stageAt t).Carrier)
          (A' : BackwardPointTrace H (H.activeStage a') (H.activeStage t)
            (H.activeStage_mono ha't) y),
          (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a' ≤ v) (hvt : v ≤ t),
            metricScalarAt (H.stageMetric (H.activeStage v) v)
              (A'.point (H.activeStage v) (H.activeStage_mono hav)
                (H.activeStage_mono hvt)) ≤ 2 * M) →
          Set.ncard {e : Fin H.eventCount | ∃ (hf : H.activeStage a' ≤ e.castSucc)
            (hl : e.succ ≤ H.activeStage t) (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            ((records e).static b).window z =
              A'.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
            ((records e).static b).neck.scale ≤ 4 * M} ≤ n₀)
        {ℓ : ℝ} (_hℓ : 0 < ℓ) {X : ℝ≥0∞}
        (_ha₀ : 0 ≤ a₀) (_hQ : 0 < Q) (_hlate : 1 ≤ Q * (a : ℝ))
        (_hspace : (Cgrad : ℝ) * ℓ * Real.sqrt (2 * M) ≤ 1 / 4)
        (_hKℓ : K * ℓ ^ 2 ≤ 1)
        (_hK : 2 * Real.sqrt 3 * (4 * M / Q + max (8 * M / Q) (2 * Real.exp 4)) * Q ≤ K)
        (_hmargin : ENNReal.ofReal Cb * (ENNReal.ofReal Cb ^ (2 * n₀) *
          (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
            ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - a)))) < X)
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
                Cgrad * metricScalarAt (H.stageMetric (H.activeStage w) w) z *
                  Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage w) w) z) *
                  Real.sqrt ((H.stageMetric (H.activeStage w) w).inner z ξ ξ))
        (_hpin : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
          (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
          ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → H.time (H.activeStage w) < (w : ℝ) →
            ∀ z : (H.stageAt w).Carrier,
            (z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
                (A.point (H.activeStage w) (H.activeStage_mono haw)
                  (H.activeStage_mono hwt)) ℓ ∨
              z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
                (B.point (H.activeStage w) (H.activeStage_mono haw)
                  (H.activeStage_mono hwt)) ℓ) →
            InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage w) w) (a₀ + w) z),
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          A.pairEDist_CXSP (hat := hat) B v hav hvt < X ∧
            A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
              ENNReal.ofReal Cb ^ (2 * n₀) * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v))) := by
  obtain ⟨εcap, hεcap, hprotect⟩ :=
    BackwardPointTrace.exists_trace_protection_of_good_suffix_CXSP.{u}
  refine ⟨min εcap (1 / 2), lt_min hεcap (by norm_num), ?_⟩
  intro H a t hat p q A B params records hcan hacc hm hD hCE n₀ Cb hCb ε C1 C2 qcan M Q a₀ K
    Ctime Cgrad hM hqM hscalarA hscalarB htime hcount ℓ hℓ X ha₀ hQ hlate hspace hKℓ hK
    hmargin hgood hgrad hpin
  have haccCap : params.modelAccuracy ≤ εcap := hacc.trans (min_le_left _ _)
  have haccHalf : params.modelAccuracy ≤ 1 / 2 := hacc.trans (min_le_right _ _)
  have hCb1 : (1 : ℝ) ≤ Cb := hCb ▸ one_le_cbuf_C11SP params.modelRadius
  have hc : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Cb := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hCb1
  have hK1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Cb ^ (2 * n₀) := one_le_pow₀ hc
  have hΛ : (0 : ℝ) ≤ 8 / ℓ := div_nonneg (by norm_num) hℓ.le
  have htimeV (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) :
      Ctime * M * ((t : ℝ) - v) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_left (show (a : ℝ) ≤ v from hav) (t : ℝ))
      (mul_nonneg Ctime.coe_nonneg hM.le)).trans htime
  -- d_t < X
  have hdt : A.pairEDist_CXSP (hat := hat) B t hat le_rfl < X := by
    refine lt_of_le_of_lt ?_ hmargin
    exact le_self_add.trans ((le_mul_of_one_le_left zero_le hK1).trans
      (le_mul_of_one_le_left zero_le hc))
  -- Ricci（stay 条件化）：原 G20 证明体逐字
  have hRicJ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (hstay : ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X)
      (j : Fin (H.eventCount + 1)) (hf : H.activeStage a ≤ j)
      (hl : j ≤ H.activeStage t) (s : ℝ) (hvs : (v : ℝ) < s) (hjs : H.time j < s)
      (hst : s < t) (hnext : ∀ e : Fin H.eventCount, j = e.castSucc → s < H.time e.succ)
      (z : (H.stage j).Carrier) (ξ : TangentSpace ThreeModel z)
      (hz : riemannianEDistOf (H.stageMetric j s) (A.point j hf hl) z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (H.stageMetric j s) (B.point j hf hl) z < ENNReal.ofReal ℓ) :
      ricciTensor (H.stageMetric j s) z ξ ξ ≤ (3 / ℓ ^ 2) * (H.stageMetric j s).inner z ξ ξ := by
    let w : Icc (0 : ℝ) H.horizon := ⟨s, v.2.1.trans hvs.le, hst.le.trans t.2.2⟩
    have haw : a ≤ w := (show (a : ℝ) ≤ v from hav).trans hvs.le
    have hwt : w ≤ t := hst.le
    have hact : H.activeStage w = j :=
      H.activeStage_eq_of_regular_stage_CXSP w j hjs.le hnext
    subst j
    have hlateW : 1 ≤ Q * (w : ℝ) :=
      hlate.trans (mul_le_mul_of_nonneg_left (show (a : ℝ) ≤ w from haw) hQ.le)
    rcases hz with hz | hz
    · exact A.ricci_on_ball_of_good_suffix_CXSP hat hM hqM
        (fun u hau hut hvu hutlt hR =>
          hgood v hav hvt hstay u hau hut hvu hutlt _ (Or.inl rfl) hR)
        hscalarA (htimeV v hav) w haw hvs hwt hjs
        (fun y hy hR η => hgrad v hav hvt hstay w haw hwt hvs hst hjs y (Or.inl hy) hR η)
        ha₀ hQ hlateW hℓ hspace hKℓ hK z
        (hpin v hav hvt hstay w haw hwt hvs hst hjs z (Or.inl hz)) hz ξ
    · exact B.ricci_on_ball_of_good_suffix_CXSP hat hM hqM
        (fun u hau hut hvu hutlt hR =>
          hgood v hav hvt hstay u hau hut hvu hutlt _ (Or.inr rfl) hR)
        hscalarB (htimeV v hav) w haw hvs hwt hjs
        (fun y hy hR η => hgrad v hav hvt hstay w haw hwt hvs hst hjs y (Or.inr hy) hR η)
        ha₀ hQ hlateW hℓ hspace hKℓ hK z
        (hpin v hav hvt hstay w haw hwt hvs hst hjs z (Or.inr hz)) hz ξ
  -- slab drift（同 stage，stay 条件化）
  have hslabAB (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (hstay : ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X)
      (v₁ w : Icc (0 : ℝ) H.horizon) (hav₁ : a ≤ v₁) (hv₁t : v₁ ≤ t) (haw : a ≤ w)
      (hwt : w ≤ t) (hvv₁ : v ≤ v₁) (hv₁w : v₁ ≤ w)
      (hsame : H.activeStage v₁ = H.activeStage w) :
      A.pairEDist_CXSP (hat := hat) B v₁ hav₁ hv₁t ≤
        A.pairEDist_CXSP (hat := hat) B w haw hwt +
          ENNReal.ofReal ((8 / ℓ) * ((w : ℝ) - v₁)) := by
    rw [pairEDist_eq_of_activeStage_C11SP A B v₁ hav₁ hv₁t (H.activeStage w) hsame
      (H.activeStage_mono haw) (H.activeStage_mono hwt)]
    have hk : H.time (H.activeStage w) ≤ v₁ := hsame ▸ H.activeStage_time_le v₁
    exact H.smooth_distance_distortion_C11D (H.activeStage w) hℓ hv₁w hk
      (H.lt_time_succ_of_activeStage_eq_C11D w) w.2.2 _ _
      (fun s hs z ξ hz => hRicJ v hav hvt hstay (H.activeStage w)
        (H.activeStage_mono haw) (H.activeStage_mono hwt) s
        ((show (v : ℝ) ≤ v₁ from hvv₁).trans_lt hs.1) (hk.trans_lt hs.1)
        (hs.2.trans_le hwt)
        (fun e he => hs.2.trans (H.lt_time_succ_of_activeStage_eq_C11D w e he)) z ξ hz)
  -- crossing 分类（两条 trace）
  have hgoodA (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (hstay : ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) :
      ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        (v : ℝ) < w → (w : ℝ) < t →
        qcan ≤ metricScalarAt (H.stageMetric (H.activeStage w) w)
          (A.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) →
        H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime w
          (A.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) :=
    fun w haw hwt hvw hwtlt hR => hgood v hav hvt hstay w haw hwt hvw hwtlt _ (Or.inl rfl) hR
  have hgoodB (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (hstay : ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) :
      ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        (v : ℝ) < w → (w : ℝ) < t →
        qcan ≤ metricScalarAt (H.stageMetric (H.activeStage w) w)
          (B.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) →
        H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime w
          (B.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) :=
    fun w haw hwt hvw hwtlt hR => hgood v hav hvt hstay w haw hwt hvw hwtlt _ (Or.inr rfl) hR
  -- (D4′) 左极限（stay 条件化）
  have hev : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a < v) (_hvt : v ≤ t),
      (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
      ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t), H.time e.succ = (v : ℝ) →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ s in 𝓝[<] H.time e.succ,
        riemannianEDistOf (H.stageMetric e.castSucc s)
            (A.point e.castSucc hf (e.castSucc_lt_succ.le.trans hl))
            (B.point e.castSucc hf (e.castSucc_lt_succ.le.trans hl)) ≤
          ENNReal.ofReal Cb * riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
            (A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl)
            (B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl) + ENNReal.ofReal δ := by
    intro v hav hvt hstay e hf hl he δ hδ
    have hclA := crossing_class_of_good_suffix_C11SP hprotect hat A records haccCap hm hcan hD
      hCE hM hqM (hgoodA v hav.le hvt hstay) hscalarA (htimeV v hav.le) e hf hl he.ge
    have hclB := crossing_class_of_good_suffix_C11SP hprotect hat B records haccCap hm hcan hD
      hCE hM hqM (hgoodB v hav.le hvt hstay) hscalarB (htimeV v hav.le) e hf hl he.ge
    have hpb : (∀ b, A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
        {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
        ∃ (b₀ : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow params.modelRadius),
          StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
          ((records e).static b₀).window x = A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl :=
      hclA.imp id fun ⟨b, z, h1, h2, h3, _⟩ => ⟨b, z, h1, h2, h3⟩
    have hqb : (∀ b, B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
        {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
        ∃ (b₀ : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow params.modelRadius),
          StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
          ((records e).static b₀).window x = B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl :=
      hclB.imp id fun ⟨b, z, h1, h2, h3, _⟩ => ⟨b, z, h1, h2, h3⟩
    have h := ObservedHistory.surgery_no_shortcut_buffer_of_record_C11SP H e (records e)
      (hcan e) haccHalf hD (A.crossing e hf hl) (B.crossing e hf hl) hpb hqb hδ
    rw [← hCb] at h
    exact h
  -- 条件乘性链
  have hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        ENNReal.ofReal Cb ^ (2 * n₀) * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v))) := by
    intro v hav hvt hstay
    rcases eq_or_lt_of_le hvt with hveq | hvlt
    · have hv : v = t := hveq
      subst hv
      exact le_self_add.trans (le_mul_of_one_le_left zero_le hK1)
    obtain ⟨v', hvv', hv't, hstage⟩ := exists_right_sameStage_C11SP v t hvlt
    have hav' : a ≤ v' := hav.trans hvv'.le
    let A' := A.restrictFirst (H.activeStage_mono hav') (H.activeStage_mono hv't.le)
    let B' := B.restrictFirst (H.activeStage_mono hav') (H.activeStage_mono hv't.le)
    have hRA : ∀ (w : Icc (0 : ℝ) H.horizon) (hv'w : v' ≤ w) (hwt : w ≤ t),
        metricScalarAt (H.stageMetric (H.activeStage w) w)
          (A'.point (H.activeStage w) (H.activeStage_mono hv'w) (H.activeStage_mono hwt)) ≤
            2 * M := fun w hv'w hwt =>
      A.scalar_le_two_mul_of_good_suffix_CXSP hat hM hqM (hgoodA v hav hvt hstay) hscalarA
        (htimeV v hav) w (hav'.trans hv'w) (hvv'.trans_le hv'w) hwt
    have hRB : ∀ (w : Icc (0 : ℝ) H.horizon) (hv'w : v' ≤ w) (hwt : w ≤ t),
        metricScalarAt (H.stageMetric (H.activeStage w) w)
          (B'.point (H.activeStage w) (H.activeStage_mono hv'w) (H.activeStage_mono hwt)) ≤
            2 * M := fun w hv'w hwt =>
      B.scalar_le_two_mul_of_good_suffix_CXSP hat hM hqM (hgoodB v hav hvt hstay) hscalarB
        (htimeV v hav) w (hav'.trans hv'w) (hvv'.trans_le hv'w) hwt
    have hclassA : ∀ (e : Fin H.eventCount) (hf : H.activeStage v' ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t),
        (∀ b, A'.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
          {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
        ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
          StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
          ((records e).static b).window z = A'.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
          ((records e).static b).neck.scale ≤ 4 * M := fun e hf hl =>
      crossing_class_of_good_suffix_C11SP hprotect hat A records haccCap hm hcan hD hCE hM hqM
        (hgoodA v hav hvt hstay) hscalarA (htimeV v hav) e
        ((H.activeStage_mono hav').trans hf) hl
        ((show (v : ℝ) ≤ v' from hvv'.le).trans
          (lt_time_succ_of_activeStage_le_C11SP v' e hf).le)
    have hclassB : ∀ (e : Fin H.eventCount) (hf : H.activeStage v' ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t),
        (∀ b, B'.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
          {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
        ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
          StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
          ((records e).static b).window z = B'.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
          ((records e).static b).neck.scale ≤ 4 * M := fun e hf hl =>
      crossing_class_of_good_suffix_C11SP hprotect hat B records haccCap hm hcan hD hCE hM hqM
        (hgoodB v hav hvt hstay) hscalarB (htimeV v hav) e
        ((H.activeStage_mono hav').trans hf) hl
        ((show (v : ℝ) ≤ v' from hvv'.le).trans
          (lt_time_succ_of_activeStage_le_C11SP v' e hf).le)
    have hstay' : ∀ (s : Icc (0 : ℝ) H.horizon) (has : v' ≤ s) (hst : s ≤ t), v' < s →
        A'.pairEDist_CXSP (hat := hv't.le) B' s has hst < X := by
      intro s has hst hvs
      rcases eq_or_lt_of_le hst with hseq | hslt
      · have hs : s = t := hseq
        subst hs
        exact hdt
      · exact hstay s (hav'.trans has) hst (hvv'.trans hvs) hslt
    have hchain := pairEDist_window_of_largeCap_count_record_C11SP records hcan haccHalf hD
      A' B' hΛ n₀ hclassA hclassB (hcount v' hav' hv't.le p A' hRA)
      (hcount v' hav' hv't.le q B' hRB)
      (fun v₁ w hv'v₁ hv₁t hv'w hwt hv₁w hsame _ =>
        hslabAB v hav hvt hstay v₁ w (hav'.trans hv'v₁) hv₁t (hav'.trans hv'w) hwt
          (hvv'.le.trans hv'v₁) hv₁w hsame)
      v' le_rfl hv't.le hstay'
    rw [← hCb] at hchain
    have hstep := hslabAB v hav hvt hstay v v' hav hvt hav' hv't.le le_rfl hvv'.le
      hstage.symm
    have hsplit : ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) =
        ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v')) +
          ENNReal.ofReal ((8 / ℓ) * ((v' : ℝ) - v)) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hΛ (sub_nonneg.mpr hv't.le))
        (mul_nonneg hΛ (sub_nonneg.mpr hvv'.le))]
      congr 1
      ring
    calc A.pairEDist_CXSP (hat := hat) B v hav hvt
        ≤ A.pairEDist_CXSP (hat := hat) B v' hav' hv't.le +
            ENNReal.ofReal ((8 / ℓ) * ((v' : ℝ) - v)) := hstep
      _ ≤ ENNReal.ofReal Cb ^ (2 * n₀) * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
            ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v'))) +
            ENNReal.ofReal Cb ^ (2 * n₀) * ENNReal.ofReal ((8 / ℓ) * ((v' : ℝ) - v)) :=
          add_le_add hchain (le_mul_of_one_le_left zero_le hK1)
      _ = ENNReal.ofReal Cb ^ (2 * n₀) * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
            ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v))) := by
          rw [hsplit, ← mul_add, add_assoc]
  exact pair_distance_of_unexited_suffix_mul_C11SP A B hc hΛ hev hmargin hbound

end GC.LongTime.Ch11
