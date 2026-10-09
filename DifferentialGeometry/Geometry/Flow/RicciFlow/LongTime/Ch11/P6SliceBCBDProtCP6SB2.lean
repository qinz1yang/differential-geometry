import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDCeilP6SB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10CrossSlabProtCXJD

/-!
# `hprotC` 去 ∀ 化：guarded producer + cap 出生 ceiling 的保护由树内 producer 付
（O-CH11-SLICE-BCBD2 G1，后缀 `_P6SB2`）

SLICE-BCBD 主定理（G7 / G8）的 CXJD binder `hprotC`（`∀ v' ≥ aSeed, ∀ z'', ∀ trace`）有两个消费点：
(i) G6 `capCeiling_of_firstExit_P6SB`（`z = y`、`v' = time i⁺`）；(ii) G5 经 SLTPROD G3c
`hstayLocStar_of_firstExit_P6SP`（`z` 取遍球，c⋆ guard）。本文件：
* `ObservedHistory.hprotC_of_ceiling_guarded_P6SB2`（PROVED）：树内 `hprotC_of_ceiling_CXJD` 的 guarded
  孪生——  scale 分离只对被跨越的 record（`a < time e⁺ ≤ σ`）要求；
* `exists_hnc_of_records_P6SB2`（PROVED ⇐ `exists_not_ageZeroCapPoint_of_scalar_lt_C11G`）：`hnc` 前提；
* `lt_scale_of_age_dichotomy_P6SB2`（PROVED，纯实数）：年龄二分；
* **`ObservedHistory.capCeiling_of_firstExit_sep_P6SB2`**（PROVED ⇐ CXJD 结构输入族 + (SEP′) 型
  `hsepT` / `hsep4` + kernel records 参数）：G6 结论逐字，**无 `hprotC`**——消费点 (i) 付清。
消费点 (ii) 的残余（年轻 cap、`scale ∈ (4Qb′R, 4R(t,z)]`、`R(t,z) > Cg·R` 的高曲率球点）见 DELIVERIES BLOCKED 块：
R-相对的 (SEP′) 推不出 `scale > 4R(t,z)`，且 KX 链在 `R(t,z)/R` 无界的点（T4/TC → Cone3 第二层 blow-up 中心）
用 `hslabs`，故不能加 Λ guard。生成器 `build-logs/scratch/O-CH11-SLICE-BCBD2/gen/gen1.py`
（CXJD / G6 源切片 + assert 替换）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- `activeStage v ≤ e⁻` ⇒ `v < time e⁺`（CXJD 私有引理的公开孪生，`_P6SB2`）。 -/
theorem ObservedHistory.lt_time_succ_of_le_castSucc_P6SB2 (H : ObservedHistory.{u})
    (v : Icc (0 : ℝ) H.horizon) (e : Fin H.eventCount) (h : H.activeStage v ≤ e.castSucc) :
    (v : ℝ) < H.time e.succ := by
  have hlt : (H.activeStage v : ℕ) < H.eventCount :=
    lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) e.isLt
  have h1 := H.activeStage_before_next v hlt
  refine h1.trans_le (H.time_strictMono.monotone ?_)
  rw [Fin.le_iff_val_le_val]
  simp only [Fin.val_succ]
  have := Fin.le_iff_val_le_val.mp h
  simp only [Fin.val_castSucc] at this
  omega

/-- `v ∈ [time e⁻, time e⁺)` ⇒ `activeStage v = e⁻`（CXJD 私有引理的公开孪生，`_P6SB2`）。 -/
theorem ObservedHistory.activeStage_eq_of_mem_P6SB2 (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    (v : Icc (0 : ℝ) H.horizon) (h1 : H.time e.castSucc ≤ v) (h2 : (v : ℝ) < H.time e.succ) :
    H.activeStage v = e.castSucc :=
  (H.mem_stageDomain_iff v e.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (v : ℝ) ∈ Ico (H.time e.castSucc) (H.time e.succ) from ⟨h1, h2⟩))

/-- **guarded 条件保护 producer（`_P6SB2`，PROVED）**：树内 `hprotC_of_ceiling_CXJD` 逐字，唯一改动——
scale 分离 `hscale` 只对**真正被跨越**的 record（`a < time e⁺` 且 `e⁺ ≤ activeStage σ`）要求（原证明只在
`h4 : e.succ ≤ activeStage σ` 下用 `hscale`）。结论 = CXJD 条件保护（c⋆ 深度形：`σ − a ≤ T/R`、
`R_σ(z) ≤ Cball·R`）。 -/
theorem ObservedHistory.hprotC_of_ceiling_guarded_P6SB2
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T : ℝ} (H : ObservedHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR : 0 < R)
    (hL : 0 ≤ L)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hQb : max (max Cball Cg) 1 ≤ Qb) (hstep : 2 * Ctime' * Qb * T ≤ 1) (haS : aSeed ≤ a)
    (haσ : a ≤ σ) (hσlast : H.activeStage σ < Fin.last H.eventCount)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (σ : ℝ) - a ≤ T / R) {z : (H.stageAt σ).Carrier}
    (hz : metricScalarAt (H.stageMetric (H.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    {q : CutoffParameters} {T₀ : ℝ}
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hnc : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) (w : (H.stage e.succ).Carrier),
      (∀ b, metricScalarAt (H.event e).outputMetric w < ((records e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow q.modelRadius),
        w = ((records e he).static b).window x ∧ ‖x.val‖ < q.modelRadius)
    (hscale : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, (a : ℝ) < H.time e.succ →
      e.succ ≤ H.activeStage σ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale) :
    ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage Tn) (h3 : H.activeStage a ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage σ) (he : T₀ ≤ H.time e.succ),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), H.time e.succ ≤ (v : ℝ) →
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
              (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
                (H.activeStage_mono (hvσ.trans hσT)))
              (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvσ)) <
            riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
                (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                  (H.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) → ∀ b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} := by
  intro e h1 h2 h3 h4 he hgoodE b
  have hτσ : H.time e.succ ≤ σ :=
    (H.time_strictMono.monotone h4).trans (H.activeStage_time_le σ)
  have haτ : (a : ℝ) < H.time e.succ := ObservedHistory.lt_time_succ_of_le_castSucc_P6SB2 H a e h3
  let τI : Icc (0 : ℝ) H.horizon := ⟨H.time e.succ, H.time_nonneg _, hτσ.trans σ.2.2⟩
  have haτI : a ≤ τI := haτ.le
  have hτIσ : τI ≤ σ := hτσ
  obtain ⟨e2, he2⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt (h4.trans_lt hσlast))
  have hlt : H.time e.succ < H.time e2.succ := by
    rw [← he2]
    exact H.time_strictMono e2.castSucc_lt_succ
  have hact : H.activeStage τI = e.succ :=
    (ObservedHistory.activeStage_eq_of_mem_P6SB2 H e2 τI (by rw [he2]) hlt).trans he2
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hXle : ∀ X : ℝ≥0∞, X + ENNReal.ofReal (L / 2 / Real.sqrt R) ≤
      X + ENNReal.ofReal (L / Real.sqrt R) := fun X =>
    add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by linarith) hsR.le))
  let A' := A.restrictFirst (H.activeStage_mono haτI) (H.activeStage_mono hτIσ)
  have hceil := ObservedHistory.scalar_le_two_mul_stopped_ceiling_CXJT0
    H haT hσT has seedTrace y L hR hgood hQb
    hstep hτIσ le_rfl (haS.trans haτI) (haL.trans haτ.le) (by
      change (σ : ℝ) - H.time e.succ ≤ T / R
      linarith) hz A' (fun v hav hvt => (hgoodE v (haτI.trans hav) hvt hav).le.trans (hXle _))
  have key : ∀ (m : Fin (H.eventCount + 1)) (hm : H.activeStage τI = m)
      (h3' : H.activeStage a ≤ m) (h4' : m ≤ H.activeStage σ),
      metricScalarAt (H.stageMetric m (H.time e.succ)) (A.point m h3' h4') ≤ 2 * (Qb * R) := by
    intro m hm h3' h4'
    subst hm
    exact hceil τI le_rfl hτIσ
  have hA := key e.succ hact (h3.trans e.castSucc_lt_succ.le) h4
  rw [ObservedHistory.stageMetric_succ_time_C11G] at hA
  have hS := H.seed_scalar_le_of_smallParabolic_C11G haT hsmall hclock seedTrace τI
    (haS.trans haτI) (hτIσ.trans hσT) e.succ hact (h1.trans e.castSucc_lt_succ.le) h2
  change metricScalarAt (H.stageMetric e.succ (H.time e.succ)) _ ≤ _ at hS
  rw [ObservedHistory.stageMetric_succ_time_C11G] at hS
  have hsc := fun b' => hscale e he b' haτ h4
  have hm1 : 3 / r ^ 2 ≤ max (3 / r ^ 2) (2 * (Qb * R)) := le_max_left _ _
  have hm2 : 2 * (Qb * R) ≤ max (3 / r ^ 2) (2 * (Qb * R)) := le_max_right _ _
  have hn1 := hnc e he (seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
    fun b' => by linarith [hsc b']
  have hn2 := hnc e he (A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4)
    fun b' => by linarith [hsc b']
  refine ⟨fun ⟨x, hx, hzx⟩ => hn1 ⟨b, x, hzx.symm, ?_⟩,
    fun ⟨x, hx, hzx⟩ => hn2 ⟨b, x, hzx.symm, ?_⟩⟩
  · have hx' : ‖x.val‖ ≤ StandardCap.transitionEnd + 10 := hx
    linarith
  · have hx' : ‖x.val‖ ≤ StandardCap.transitionEnd + 10 := hx
    linarith

/-- **单 record 族的 cap window 排除（`_P6SB2`，PROVED ⇐ 树内
`exists_not_ageZeroCapPoint_of_scalar_lt_C11G`）**：
存在绝对常数 `ε₀ > 0`，records 精度 `≤ ε₀`、阶 `≥ 2`、canonical windows ⇒ `hprotC_of_ceiling_CXJD` 的 `hnc`
前提逐字（`R_out(w) < scale_b/2` ∀b ⇒ `w` 不是任何 window 点 `‖x‖ < modelRadius`）。 -/
theorem exists_hnc_of_records_P6SB2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {H : ObservedHistory.{u}} {q : CutoffParameters} {T₀ : ℝ}
        (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q),
        q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
        (∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
          ((records e he).static b).hasCanonicalWindow) →
        ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) (w : (H.stage e.succ).Carrier),
          (∀ b, metricScalarAt (H.event e).outputMetric w <
            ((records e he).static b).neck.scale / 2) →
          ¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow q.modelRadius),
            w = ((records e he).static b).window x ∧ ‖x.val‖ < q.modelRadius := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_not_ageZeroCapPoint_of_scalar_lt_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro H q T₀ records hacc hm hcan e he w hw
  have h := hnc0 (records e he) hacc hm (hcan e he) (Dcap := q.modelRadius - 1) (by linarith) w hw
  simpa only [sub_add_cancel] using h

/-- **年龄二分（`_P6SB2`，PROVED，纯实数）**：cap `i` 年轻（`aᵢ ≤ θ₀/sᵢ`）且 `M < sᵢ`；cap `e` 更晚出生
（`aₑ ≤ aᵢ`）；若 `e` 年轻则 `M < sₑ`（(SEP′) 型 `hsep4`）⇒ 无论 `e` 年轻与否都有 `M < sₑ`
（`e` 老：`θ₀/sₑ < aₑ ≤ aᵢ ≤ θ₀/sᵢ` ⇒ `sᵢ < sₑ`）。 -/
theorem lt_scale_of_age_dichotomy_P6SB2 {θ₀ M si se ai ae : ℝ} (hθ₀ : 0 < θ₀) (hsi : 0 < si)
    (hse : 0 < se) (haei : ae ≤ ai) (hai : ai ≤ θ₀ * si⁻¹) (hMi : M < si)
    (hMe : ae ≤ θ₀ * se⁻¹ → M < se) : M < se := by
  by_cases h : ae ≤ θ₀ * se⁻¹
  · exact hMe h
  · have h1 : θ₀ * se⁻¹ < θ₀ * si⁻¹ := (not_le.mp h).trans_le (haei.trans hai)
    have h2 : se⁻¹ < si⁻¹ := lt_of_mul_lt_mul_left h1 hθ₀.le
    have h3 : si < se := (inv_lt_inv₀ hse hsi).mp h2
    linarith

/-- **cap 出生时刻 ceiling，无 `hprotC`（`_P6SB2`，PROVED ⇐ CXJD 结构输入族 + `hwin` + (SEP′) 型
`hsepT` / `hsep4` + kernel records 参数）**：G6 `capCeiling_of_firstExit_P6SB` 结论逐字。与 G6 的差别：
CXJD 跨 slab ceiling 用 kernel `recordsK` 限制到 `time i⁺` 之后（`T₀ := time i⁺`），条件保护由
`hprotC_of_ceiling_guarded_P6SB2` 生产：`hnc` ⇐ `exists_hnc_of_records_P6SB2`（kernel 精度
`≤ 1/(n+1) → 0`、阶 `≥ n + 2`），被跨越 cap `e`（`time i⁺ < time e⁺ ≤ t`）的 scale 分离 ⇐ `hsep4` +
年龄二分 `lt_scale_of_age_dichotomy_P6SB2`（`i` 年轻 ⇒ `e` 年轻或 `sₑ > sᵢ`），`6/r² ≤ n + 1 < R`
eventually。X-records 族只剩 `hOld`（`T₀ ≤ aSeed`）。 -/
theorem ObservedHistory.capCeiling_of_firstExit_sep_P6SB2
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, 1 ≤ R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀ : ℕ → ℝ) (hT₀ : ∀ n, T₀ n ≤ aSeed n)
    (hOld : ∀ n (e : Fin (K n).eventCount), T₀ n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {θ₀ : ℝ} {T₀K : ℕ → ℝ} {pK : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (pK n))
    (hsepT : ∀ n (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
        ((recordsK n i hi).static b).neck.scale)
    (hθ₀ : 0 < θ₀) (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (haccK : ∀ n : ℕ, (pK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hradK : ∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (pK n).modelRadius)
    (hordK : ∀ n : ℕ, n + 2 ≤ (pK n).modelOrder)
    (hsep4 : ∀ n (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale) :
    ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      metricScalarAt ((K n).toHistory.event i).outputMetric (A.point i.succ le_rfl hl) ≤
        2 * (max (max 1 Cg) 1 * R n) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_hnc_of_records_P6SB2.{u}
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min (min (r / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hm0 : (0 : ℝ) < max (Ctime' : ℝ) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith [le_max_right (Ctime' : ℝ) 1]
  set Qb : ℝ := max (max 1 Cg) 1 with hQbdef
  have hQb1 : 1 ≤ Qb := le_max_right _ _
  have hQb0 : 0 < Qb := by linarith
  set T : ℝ := 1 / (2 * max (Ctime' : ℝ) 1) / Qb with hTdef
  have hT0 : 0 < T := div_pos (by positivity) hQb0
  have hT1 : T ≤ 1 := (div_le_one hQb0).2 (hc1.trans hQb1)
  have hstep : 2 * (Ctime' : ℝ) * Qb * T ≤ 1 := by
    have h1 : 2 * (Ctime' : ℝ) * Qb * T = (Ctime' : ℝ) / max (Ctime' : ℝ) 1 := by
      rw [hTdef]
      field_simp
    rw [h1]
    exact (div_le_one hm0).2 (le_max_left _ _)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hTE := hnat.eventually_gt_atTop (StandardCap.transitionEnd + 10)
  have hr6 := hnat.eventually_ge_atTop (6 / r ^ 2)
  have hacE : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ min ε₀ (1 / 2) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds (lt_min hε₀ (by norm_num)))
  filter_upwards [hwin T hT0, hL.eventually_ge_atTop (max (max (4 * localPropagationRadius C2')
    (2 * (1 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2)) 1), hTE, hr6, hacE]
    with n hwn hLn hTEn hr6n hacn
  intro i hi hl A b hage
  have hsc : 0 < ((recordsK n i hi).static b).neck.scale :=
    ((recordsK n i hi).static b).neck.scale_pos
  have hL4 : 4 * localPropagationRadius C2' ≤ L n :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hLn
  have hL5 : 2 * (1 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2 ≤ L n :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hLn
  have hL6 : (1 : ℝ) ≤ L n := (le_max_right _ _).trans hLn
  -- 深度：年龄 ≤ θ₀/scale 且 θ₀·R ≤ T·scale ⇒ σ − time i⁺ ≤ T/R
  have hsep := hsepT n i hi b hl hage
  have hdep : t n - (K n).time i.succ ≤ T / R n := by
    rw [le_div_iff₀ (hR n)]
    have h1 := mul_le_mul_of_nonneg_right hage (hR n).le
    have h2 : θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ * R n =
        θ₀ * R n / ((recordsK n i hi).static b).neck.scale := by
      field_simp
    have h3 : θ₀ * R n / ((recordsK n i hi).static b).neck.scale ≤ T := by
      rw [div_le_iff₀ hsc]
      exact hsep
    linarith
  have htle : (K n).time i.succ ≤ (K n).time (j n).castSucc :=
    (K n).time_strictMono.monotone hl
  have hσt : (σ n : ℝ) = t n := hσ n
  have hjσ : (K n).time (j n).castSucc < (σ n : ℝ) := by rw [hσt]; exact hjt n
  have hTR : T / R n ≤ 1 / R n := div_le_div_of_nonneg_right hT1 (hR n).le
  have haSr : (aSeed n : ℝ) ≤ (K n).time i.succ := by linarith
  let a : Icc (0 : ℝ) (K n).toHistory.horizon :=
    ⟨(K n).time i.succ, (aSeed n).2.1.trans haSr,
      (by linarith : (K n).time i.succ ≤ (σ n : ℝ)).trans (σ n).2.2⟩
  have haval : (a : ℝ) = (K n).time i.succ := rfl
  have haS : aSeed n ≤ a := haSr
  have haσ : a ≤ σ n := show ((K n).time i.succ : ℝ) ≤ σ n by linarith
  have hdepth : (σ n : ℝ) - a ≤ T / R n := by rw [haval, hσt]; exact hdep
  have hLR : 1 / R n ≤ L n ^ 2 / R n :=
    div_le_div_of_nonneg_right (by nlinarith) (hR n).le
  have haL : (σ n : ℝ) - L n ^ 2 / R n ≤ a := by linarith
  have hRa' : 1 ≤ R n * a := by
    have := mul_le_mul_of_nonneg_left haSr (hR n).le
    rw [haval]
    linarith [hRa n]
  have hact_a : (K n).toHistory.activeStage a = i.succ :=
    (K n).activeStage_eq_succ_P6SB i (j n) hl a haval
  have hact_σ : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6SB (j n) (σ n) hjσ.le (by rw [hσt]; exact htj n)
  have hσlast : (K n).toHistory.activeStage (σ n) < Fin.last (K n).eventCount := by
    rw [hact_σ]
    exact Fin.castSucc_lt_last (j n)
  obtain ⟨A', hA'⟩ := trace_transport_both_P6SB ((K n).toHistory.activeStage_mono haσ) (y n)
    hact_a.symm hact_σ.symm (hyG n).symm A
  have hz : metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
      (y n) ≤ 1 * R n := by
    rw [(K n).scalar_of_incoming_P6X (j n) hact_σ.symm (σ n) (yG n) (y n) (hyG n), hσt, ← hRn n,
      one_mul]
  have hzy : y n ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (1 / Real.sqrt (R n)) := by
    change riemannianEDistOf _ (y n) (y n) < ENNReal.ofReal (1 / Real.sqrt (R n))
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos one_pos (Real.sqrt_pos.mpr (hR n)))
  obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP
    (Qb := Qb) (R := R n) (Rad := 1) (L := L n) hr hρ hc0 hQb1 (hR1 n) hκdef (by linarith)
    (by linarith)
  have hQb : max (max 1 Cg) 1 ≤ Qb := le_rfl
  -- kernel records 限制到 `time i⁺` 之后
  let rec' : ∀ e : Fin (K n).eventCount, (a : ℝ) ≤ (K n).toHistory.time e.succ →
      GeometricCutoffRecord (K n).toHistory e (pK n) := fun e he => recordsK n e (hi.trans he)
  have hOld' : ∀ e : Fin (K n).eventCount, (a : ℝ) ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore :=
    fun e he => hOld n e ((hT₀ n).trans (haSr.trans he))
  have hcan' : ∀ (e : Fin (K n).eventCount) (he : (a : ℝ) ≤ (K n).toHistory.time e.succ) b,
      ((rec' e he).static b).hasCanonicalWindow := fun e he b => hcanK n e (hi.trans he) b
  have hacc1 : (pK n).modelAccuracy ≤ min ε₀ (1 / 2) := (haccK n).trans hacn
  have hDm' : StandardCap.transitionEnd + 10 < (pK n).modelRadius := by linarith [hradK n]
  have hnc' := hnc0 (H := (K n).toHistory) (q := pK n) (T₀ := (a : ℝ)) rec'
    (hacc1.trans (min_le_left _ _)) (le_trans (by omega) (hordK n)) hcan'
  have hact_j : ∀ e : Fin (K n).eventCount, e.succ ≤ (K n).toHistory.activeStage (σ n) →
      e.succ ≤ (j n).castSucc := fun e he => hact_σ ▸ he
  have hscale' : ∀ (e : Fin (K n).eventCount) (he : (a : ℝ) ≤ (K n).toHistory.time e.succ) b,
      (a : ℝ) < (K n).toHistory.time e.succ → e.succ ≤ (K n).toHistory.activeStage (σ n) →
      2 * max (3 / r ^ 2) (2 * (Qb * R n)) < ((rec' e he).static b).neck.scale := by
    intro e he b' hae he4
    have hej := hact_j e he4
    have hse : 0 < ((rec' e he).static b').neck.scale := ((rec' e he).static b').neck.scale_pos
    have hM : 2 * (2 * (Qb * R n)) < ((rec' e he).static b').neck.scale :=
      lt_scale_of_age_dichotomy_P6SB2 hθ₀ hsc hse (by linarith) hage
        (hsep4 n i hi b hl hage) (hsep4 n e (hi.trans he) b' hej)
    have hRQ : R n ≤ Qb * R n := le_mul_of_one_le_left (hR n).le hQb1
    have h6 : 2 * (3 / r ^ 2) < ((rec' e he).static b').neck.scale := by
      have := hRlt n
      have h63 : 2 * (3 / r ^ 2) = 6 / r ^ 2 := by ring
      linarith
    have hmx : max (3 / r ^ 2) (2 * (Qb * R n)) < ((rec' e he).static b').neck.scale / 2 :=
      max_lt (by linarith) (by linarith)
    linarith
  have hL0 : 0 ≤ L n := by linarith
  have hprotC' := ObservedHistory.hprotC_of_ceiling_guarded_P6SB2 (K n).toHistory (haT n)
    (hsmall n) (hclock n) (seedTrace n) (hsT n) (has n) (y n) (L n) (hR n) hL0 (hgood n) hQb hstep
    haS haσ hσlast haL hdepth hz A' rec' hDm' hnc' hscale'
  have hceil := ObservedHistory.scalar_le_two_mul_crossSlab_ceiling_CXJD (Cball := 1) (Qb := Qb)
    (T := T) (K := Qb * R n / κ ^ 2) (ℓ := κ / Real.sqrt (Qb * R n)) (D := 1) hC2
    (K n).toHistory (haT n) (hsmall n) (hclock n) (seedTrace n) (ha₀ n) (hpin n) (hsT n) (has n)
    (y n) (L n) (hR n) (hgood n) hQb hstep haS haσ hσlast haL hdepth hRa' hz A' hℓ hKℓ hℓr hKr
    hKC hℓρ hρL le_rfl rec' hOld' hcan' (hacc1.trans (min_le_right _ _)) hDm' hprotC' hzy
    (hdσ n) hnum a le_rfl haσ
  have hpt := hA' i.succ ((K n).toHistory.activeStage a) hact_a.symm le_rfl hl
    ((K n).toHistory.activeStage_mono (le_refl a)) ((K n).toHistory.activeStage_mono haσ)
  rw [scalar_output_of_stage_P6SB (K n).toHistory i hact_a _ _ hpt] at hceil
  exact hceil


/-- **consumer（`_P6SB2`，PROVED，同上前提）**：G5 `sliceBCBD_kernel_fresh_theta_ev_P6SB` 的 kernel 帧 `hnotK`
槽（eventually 形，窗口 `‖x‖ < n + 2`、年龄 `≤ θ₀/scale`）⇐ `capCeiling_of_firstExit_sep_P6SB2` + 树内
`exists_capWindow_scalar_lower_C11G` + `hsep4`（G7 `hnotKev` 段的孪生，**不经 `hprotC`**）。 -/
theorem ObservedHistory.hnotKev_of_firstExit_sep_P6SB2
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, 1 ≤ R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀ : ℕ → ℝ) (hT₀ : ∀ n, T₀ n ≤ aSeed n)
    (hOld : ∀ n (e : Fin (K n).eventCount), T₀ n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {θ₀ : ℝ} {T₀K : ℕ → ℝ} {pK : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (pK n))
    (hsepT : ∀ n (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
        ((recordsK n i hi).static b).neck.scale)
    (hθ₀ : 0 < θ₀) (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (haccK : ∀ n : ℕ, (pK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hradK : ∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (pK n).modelRadius)
    (hordK : ∀ n : ℕ, n + 2 ≤ (pK n).modelOrder)
    (hsep4 : ∀ n (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale) :
    ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (pK n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨ε₀, hε₀, hlow⟩ := exists_capWindow_scalar_lower_C11G.{u}
  have hceil := ObservedHistory.capCeiling_of_firstExit_sep_P6SB2
    hC2 hjt htj σ hσ y yG hyG R hR hR1 hRn Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall
    hclock a₀ ha₀ hpin hRa T₀ hT₀ hOld hdσ hwin recordsK hsepT hθ₀ hRlt hcanK haccK hradK hordK
    hsep4
  have haccE : ∀ᶠ n in atTop, (pK n).modelAccuracy ≤ ε₀ := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hε₀)] with n hn
    exact (haccK n).trans hn
  filter_upwards [hceil, haccE] with n hc ha
  rintro ⟨i, hi, hl, A, b, x, h1, h2, h3⟩
  have hx : ‖x.val‖ < (pK n).modelRadius := lt_of_lt_of_le h2 (hradK n)
  have hS := hlow ((K n).toHistory.event i) ha (le_trans (by omega) (hordK n))
    ((recordsK n i hi).static b) (hcanK n i hi b) x hx
  rw [← h1] at hS
  have hC := hc i hi hl A b h3
  have hP := hsep4 n i hi b hl h3
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
