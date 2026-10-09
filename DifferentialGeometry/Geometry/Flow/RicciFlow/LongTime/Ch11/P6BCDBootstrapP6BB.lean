import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10DepthScalCXJP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireStayProdP6JW

/-!
# BCD 时间 bootstrap：深窗格点 anchor ⇒ 深窗 first-exit（O-CH11-BCDBOOT，后缀 `_P6BB`）

J10WIRE2 勘误 / FOOT4 G3 BLOCKED 的 repair target：深窗（`T = 3·B_w`）的 `hstopE` / `hderivL` 不能由单一
anchor 的 ODE ceiling 给（每段 ceiling 翻倍，`ode_budget_geometric_P6F4`：总深度 `< 2β`）。
**口径修正**：只给 base `hballσ`（`t ↑ σ` 的端点球控制）的“深度归纳”**不闭合**——若第 `j+1` 格 anchor 取
第 `j` 段 ceiling 的输出，常数逐段翻倍；CX-J10DEPTH 的“独立 anchor”`hanc`（`crossingDepthHI_extend_noJ10_CXJP`
的前提）同样是外给的。故每个格点 `s_j = t − j·β/R`（`j ≥ 1`）需要**独立的固定常数 anchor** `hballGrid`。
* **G1 `hballT_grid_of_depthInduction_P6BB`**（PROVED）：格点 anchor 族（trace 形，`R(s_j, A(s_j)) ≤ M·R`，
  所有 `j`）+ Good 前提 ⇒ CXJT0 `scalar_le_two_mul_stopped_ceiling_CXJT0` 在每段 `[v, s_j]`（`s_j − v ≤ β/R`）
  上从**本段** anchor 起算 ⇒ 整个深窗的条件形 `hscalC`（常数 `2·Q_b` 与 `j` 无关；无几何收缩）。
* **G2a `ObservedHistory.hstopE_body_deep_P6BB`**（PROVISIONAL：J10WIRE G4 族 + `hball` + 格点 anchor）：
  J10WIRE G4 `hstopE_body_of_firstExit_P6JW` 的结论逐字，**无 `2·Ctime′·Q_b·T ≤ 1`**（换成网格步长
  `2·Ctime′·Q_b·β ≤ 1`）；CXJD `hstop_of_firstExit_CXJD` / `hprotC_of_ceiling_CXJD` 换成 CXJP
  `hgoodV_scalC_CXJP` / `hprotC_scalC_CXJP`，`hscalC` 由 G1 付（`j = 0` 的 anchor = `hball`，`j ≥ 1` =
  `hgrid`）；深度只受 `L → ∞` 的数值约束（`ρ_b/√R + 8/ℓ·T/R < L/(4√R)`）。`hUSCtop` 空真（`tt < time i⁺ ≤
  horizon`）。
**owner（`hballGrid`）**：BCD 时间 bootstrap 本体 = DepthExtendable 深度 `T` 的 maximal-depth 极限论证
（`depthExtendable_add_of_windowAnchorBound` +
`exists_uniform_scalar_bound_of_local_flow_limit_on_window`），
adapter `isRmBoundedBy (K·R) ⇒ R ≤ 9K·R`（`scalar_le_of_isRmBounded_CXJP`）。这与 CXJP 的 `hanc`、
KRouteHICond 的 `hextend` 是**同一义务**（都由 driver 的 maximal-depth 极限论证提供）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- **格点下标（`_P6BB`，PROVED，算术）**：`v ≤ σ`、`0 < β`、`0 < R` ⇒ 存在 `j` 使
`v ≤ σ − j·β/R` 且 `(σ − j·β/R) − v ≤ β/R`（`j = ⌊(σ − v)·R/β⌋₊`）。 -/
theorem exists_grid_le_P6BB {σ v β R : ℝ} (hβ : 0 < β) (hR : 0 < R) (hvσ : v ≤ σ) :
    ∃ j : ℕ, v ≤ σ - j * β / R ∧ σ - j * β / R - v ≤ β / R := by
  have h0 : 0 ≤ (σ - v) * R / β := div_nonneg (mul_nonneg (by linarith) hR.le) hβ.le
  refine ⟨⌊(σ - v) * R / β⌋₊, ?_, ?_⟩
  · have h := Nat.floor_le h0
    have h1 : (⌊(σ - v) * R / β⌋₊ : ℝ) * β ≤ (σ - v) * R := by rwa [le_div_iff₀ hβ] at h
    have h2 : (⌊(σ - v) * R / β⌋₊ : ℝ) * β / R ≤ σ - v := by
      rw [div_le_iff₀ hR]
      linarith
    linarith
  · have h := Nat.lt_floor_add_one ((σ - v) * R / β)
    have h1 : (σ - v) * R < (⌊(σ - v) * R / β⌋₊ + 1) * β := by rwa [div_lt_iff₀ hβ] at h
    have h2 : σ - v < (⌊(σ - v) * R / β⌋₊ + 1) * β / R := by
      rw [lt_div_iff₀ hR]
      linarith
    have h3 : ((⌊(σ - v) * R / β⌋₊ : ℝ) + 1) * β / R =
        (⌊(σ - v) * R / β⌋₊ : ℝ) * β / R + β / R := by ring
    linarith

/-- **G1（`_P6BB`，PROVED）格点 anchor ⇒ 深窗条件标量界 `hscalC`**：trace `A`（`a → σ`），格点
`w = σ − j·β/R`（`a ≤ w`）上 `R(w, A(w)) ≤ M·R`（**每格独立**，同一常数 `M`），网格步长
`2·Ctime′·Q_b·β ≤ 1`，`max(M, Cg, 1) ≤ Q_b`。对 `v ∈ [a, σ]`：取 `j = ⌊(σ − v)R/β⌋₊`，在 `[v, s_j]` 上从
`s_j` 的 anchor 跑 CXJT0 stopped ceiling（Good 前提由 `hscalC` 的条件给）⇒ `R(v, A(v)) ≤ 2·Q_b·R`。
不读上一段的 ODE 输出 ⇒ 无翻倍；深度 `σ − a` 不受 `β` 限制。 -/
theorem hballT_grid_of_depthInduction_P6BB {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg M Qb β : ℝ}
    (H : ObservedHistory.{u}) {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR : 0 < R)
    (hL0 : 0 ≤ L)
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
    (hβ : 0 < β) (hstep : 2 * Ctime' * Qb * β ≤ 1) (hQb : max (max M Cg) 1 ≤ Qb)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) (haL : (σ : ℝ) - L ^ 2 / R ≤ a)
    {z : (H.stageAt σ).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    (hgrid : ∀ (j : ℕ) (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwσ : w ≤ σ),
      (w : ℝ) = σ - j * β / R →
      metricScalarAt (H.stageMetric (H.activeStage w) w)
        (A.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwσ)) ≤ M * R) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ),
      (∀ (v' : Icc (0 : ℝ) H.horizon) (hav' : a ≤ v') (hv'σ : v' ≤ σ), (v : ℝ) ≤ v' →
        riemannianEDistOf (H.stageMetric (H.activeStage v') v')
            (seedTrace.point (H.activeStage v')
              (H.activeStage_mono (haS.trans hav'))
              (H.activeStage_mono (hv'σ.trans hσT)))
            (A.point (H.activeStage v') (H.activeStage_mono hav')
              (H.activeStage_mono hv'σ)) <
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / 2 / Real.sqrt R)) →
      metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvσ)) ≤ 2 * (Qb * R) := by
  intro v hav hvσ hgoodV
  obtain ⟨j, hj1, hj2⟩ := exists_grid_le_P6BB hβ hR (show (v : ℝ) ≤ σ from hvσ)
  have hv0 : (0 : ℝ) ≤ v := v.2.1
  have hjnn : 0 ≤ (j : ℝ) * β / R := by positivity
  let w : Icc (0 : ℝ) H.horizon := ⟨(σ : ℝ) - j * β / R, hv0.trans hj1, by linarith [σ.2.2]⟩
  have hvw : v ≤ w := hj1
  have hwσ : w ≤ σ := by
    change (σ : ℝ) - j * β / R ≤ σ
    linarith
  have haw : a ≤ w := hav.trans hvw
  have hanc := hgrid j w haw hwσ rfl
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  let A'' := (A.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvσ)).restrictLast
    (H.activeStage_mono hvw) (H.activeStage_mono hwσ)
  have hceil := scalar_le_two_mul_stopped_ceiling_CXJT0 (Cball := M) H haT hσT has seedTrace y L
    hR hgood hQb hstep hvw hwσ
    (haS.trans hav) (haL.trans hav) hj2 hanc A'' ?_ v le_rfl hvw
  · exact hceil
  · intro u hvu huw
    have hg := hgoodV u (hav.trans hvu) (huw.trans hwσ) hvu
    refine hg.le.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
    exact div_le_div_of_nonneg_right (by linarith) hsR.le

/-- **G2a（`_P6BB`，PROVISIONAL：J10WIRE G4 族 + `hball` + 格点 anchor `hgrid`）**：J10WIRE G4
`hstopE_body_of_firstExit_P6JW` 的结论**逐字**，去掉深度条件 `2·Ctime′·Q_b·T ≤ 1`（换成网格步长
`2·Ctime′·Q_b·β ≤ 1`）。`KH.toHistory = H` 只为调用 CXJP（`RetainedCoreHistory` 形）。证明 = G4 的
crossing 平移 / hgood 迁移逐字 + CXJP `hgoodV_scalC_CXJP`（first-exit 整窗严格定位）、`hprotC_scalC_CXJP`，
`hscalC` 由 G1 付（`M := Q_b`；`j = 0`：`hball` + `endpoint_eq`，`Cball ≤ Q_b`；
`j ≥ 1`：`hgrid`，常数 `Q_b`）。 -/
theorem hstopE_body_deep_P6BB :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T K ℓ ρb β : ℝ} (_ : 0 ≤ C2')
    (KH : RetainedCoreHistory.{u}) (H : ObservedHistory.{u}) (_ : KH.toHistory = H)
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (_ : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (_ : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (_ : 0 ≤ a₀)
    (_ : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (_ : 0 < R)
    (_ : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (_ : max (max Cball Cg) 1 ≤ Qb) (_ : 0 < β) (_ : 2 * Ctime' * Qb * β ≤ 1)
    (_ : 0 < T)
    (_ : T ≤ (L / 2) ^ 2) (_ : 0 ≤ L) (_ : 1 ≤ R * aSeed) (_ : (aSeed : ℝ) < σ)
    (_ : R = metricScalarAt (H.stageMetric (H.activeStage σ) σ) y)
    (_ : 0 < ℓ) (_ : K * ℓ ^ 2 ≤ 1) (_ : ℓ ≤ r / 50) (_ : 1 / r ^ 2 ≤ K)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / 2 / Real.sqrt R)
    (_ : ρb / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (_ : T₀ ≤ (aSeed : ℝ))
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (_ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀) (_ : 2 ≤ q.modelOrder)
    (_ : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, (aSeed : ℝ) < H.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale)
    (_ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hsT)) y ≠ ⊤)
    (i : Fin H.eventCount) (_ : (σ : ℝ) = H.time i.succ)
    (p' : (H.stage i.castSucc).Carrier) (q' : (H.stage i.succ).Carrier) (_ : HEq y q')
    (_ : (H.event i).RegularCrossing p' q')
    (_ : ∀ᶠ t in 𝓝[<] H.time i.succ,
      ∀ z ∈ riemannianBallOf ((H.event i).incoming.flow.base.metric t) p' (ρb / Real.sqrt R),
        metricScalarAt ((H.event i).incoming.flow.base.metric t) z ≤ Cball * R)
    (_ : ∀ᶠ t in 𝓝[<] H.time i.succ,
      ∀ (tt : Icc (0 : ℝ) H.horizon), (tt : ℝ) = t → tt ≤ σ →
      ∀ (a : Icc (0 : ℝ) H.horizon), aSeed ≤ a → ∀ (hat : a ≤ tt), t - T / R ≤ (a : ℝ) →
      ∀ z' : (H.stageAt tt).Carrier,
        (∀ z : (H.stage i.castSucc).Carrier, HEq z' z →
          z ∈ riemannianBallOf ((H.event i).incoming.flow.base.metric t) p'
            (ρb / Real.sqrt R)) →
      ∀ (A : BackwardPointTrace H (H.activeStage a) (H.activeStage tt) (H.activeStage_mono hat) z')
        (j : ℕ), 1 ≤ j → ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ tt),
        (w : ℝ) = t - j * β / R →
        metricScalarAt (H.stageMetric (H.activeStage w) w)
          (A.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) ≤
          Qb * R),
    ∀ᶠ t in 𝓝[<] H.time i.succ,
      ∀ (tt : Icc (0 : ℝ) H.horizon), (tt : ℝ) = t → ∀ (htσ : tt ≤ σ)
        (a : Icc (0 : ℝ) H.horizon) (haS' : aSeed ≤ a) (hat : a ≤ tt), t - T / R ≤ (a : ℝ) →
      ∀ z' : (H.stageAt tt).Carrier,
        (∀ z : (H.stage i.castSucc).Carrier, HEq z' z →
          z ∈ riemannianBallOf ((H.event i).incoming.flow.base.metric t) p'
            (ρb / Real.sqrt R)) →
      ∀ (A : BackwardPointTrace H (H.activeStage a) (H.activeStage tt) (H.activeStage_mono hat) z')
        (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ tt),
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS'.trans hav))
              (H.activeStage_mono ((hvt.trans htσ).trans hsT)))
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_not_ageZeroCapPoint_of_scalar_lt_C11G.{u}
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), ?_⟩
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ ρb β hC2 KH H hKH Tn aSeed σ haT pT r hsmall hclock
    seedTrace
    a₀ ha₀ hpin hsT has y R L hR hgood hQb hβ hβs hT hTL hL hRa haσ hRy hℓ hKℓ hℓr hKr hKC hℓρ hρL
    hnum q T₀ hT₀ records hOld hcan hDm hacc hm hscale hfin i hσi p' q' hyq hcross hball hgrid
  have hnc : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) (w : (H.stage e.succ).Carrier),
      (∀ b, metricScalarAt (H.event e).outputMetric w < ((records e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow q.modelRadius),
        w = ((records e he).static b).window x ∧ ‖x.val‖ < q.modelRadius := by
    intro e he w hw
    have h := hnc0 (records e he) (hacc.trans (min_le_left _ _)) hm (hcan e he)
      (Dcap := q.modelRadius - 1) (by linarith) w hw
    simpa only [sub_add_cancel] using h
  have hprot : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) (w : (H.stage e.succ).Carrier),
      (∀ b, metricScalarAt (H.event e).outputMetric w < ((records e he).static b).neck.scale / 2) →
      ∀ b, w ∉ ((records e he).static b).window ''
        {x : standardCapWindow q.modelRadius | ‖x.val‖ ≤ StandardCap.transitionEnd + 10} := by
    intro e he w hw b hmem
    obtain ⟨x, hx, hzx⟩ := hmem
    have hx' : ‖x.val‖ ≤ StandardCap.transitionEnd + 10 := hx
    exact hnc e he w hw ⟨b, x, hzx.symm, by linarith⟩
  -- σ = time i⁺
  have hσact : H.activeStage σ = i.succ := by
    refine le_antisymm ?_ (H.le_activeStage σ i.succ (le_of_eq hσi.symm))
    by_contra hlt
    have h1 := H.time_strictMono (not_le.mp hlt)
    have h2 := H.activeStage_time_le σ
    have h3 : (σ : ℝ) = σ.1 := rfl
    linarith
  have hiT : H.time i.succ ≤ (Tn : ℝ) := by
    rw [← hσi]
    exact hsT
  have h2i : i.succ ≤ H.activeStage Tn := H.le_activeStage Tn i.succ hiT
  have h1i : H.activeStage aSeed ≤ i.castSucc := by
    rw [Fin.le_castSucc_iff]
    by_contra hle
    have h1 := H.time_strictMono.monotone (not_lt.mp hle)
    have h2 := H.activeStage_time_le aSeed
    have h3 : (aSeed : ℝ) = aSeed.1 := rfl
    linarith
  have h1s : H.activeStage aSeed ≤ i.succ := h1i.trans i.castSucc_lt_succ.le
  have h2c : i.castSucc ≤ H.activeStage Tn := i.castSucc_lt_succ.le.trans h2i
  have hiT₀ : T₀ ≤ H.time i.succ := by linarith
  have hQ1 : 1 ≤ Qb := (le_max_right _ _).trans hQb
  have hscI := fun b => hscale i hiT₀ b (by linarith)
  -- 两点保护
  have hseedS := H.seed_scalar_le_of_smallParabolic_C11G haT hsmall hclock seedTrace σ has hsT
    i.succ hσact h1s h2i
  have hseedO : metricScalarAt (H.event i).outputMetric (seedTrace.point i.succ h1s h2i) ≤
      3 / r ^ 2 := by
    rw [← H.stageMetric_succ_time_C11G i, ← hσi]
    exact hseedS
  obtain ⟨hdσ_eq, hRσ_eq, -⟩ := H.transport_at_stage_P6JW haT seedTrace has hsT hσact hσi y q'
    hyq h1s h2i
  have hqS : metricScalarAt (H.event i).outputMetric q' = R := by
    rw [← H.stageMetric_succ_time_C11G i, ← hRσ_eq, hRy]
  have hpprot := hprot i hiT₀ (seedTrace.point i.succ h1s h2i) (fun b => by
    have := hscI b
    have hm1 : 3 / r ^ 2 ≤ max (3 / r ^ 2) (2 * (Qb * R)) := le_max_left _ _
    linarith)
  have hqprot := hprot i hiT₀ q' (fun b => by
    rw [hqS]
    have := hscI b
    have hm2 : 2 * (Qb * R) ≤ max (3 / r ^ 2) (2 * (Qb * R)) := le_max_right _ _
    nlinarith [mul_nonneg (sub_nonneg.2 hQ1) hR.le])
  have hLpos : 0 < L := by nlinarith
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hδ : 0 < L / 2 / Real.sqrt R := div_pos (div_pos hLpos two_pos) hsR
  have hhalf : ENNReal.ofReal (L / 2 / Real.sqrt R) + ENNReal.ofReal (L / 2 / Real.sqrt R) =
      ENNReal.ofReal (L / Real.sqrt R) := by
    rw [← ENNReal.ofReal_add hδ.le hδ.le]
    congr 1
    ring
  have hsum : ∀ X : ℝ≥0∞, X + ENNReal.ofReal (L / 2 / Real.sqrt R) +
      ENNReal.ofReal (L / 2 / Real.sqrt R) = X + ENNReal.ofReal (L / Real.sqrt R) := fun X => by
    rw [add_assoc, hhalf]
  have hshift := H.surgery_no_shortcut_C11D i (records i hiT₀).static (hOld i hiT₀) (hcan i hiT₀)
    (hacc.trans (min_le_right _ _)) hDm (seedTrace.crossing i h1i h2i) hcross hpprot hqprot hδ
  have hcs : H.time i.castSucc < H.time i.succ := H.time_strictMono Fin.castSucc_lt_succ
  have hLR : 0 < L ^ 2 / R := div_pos (pow_pos hLpos 2) hR
  have hq4 : (L / 2) ^ 2 / R = 1 / 4 * (L ^ 2 / R) := by ring
  filter_upwards [hshift, hball, hgrid, Ioo_mem_nhdsLT (show max (H.time i.castSucc)
      ((σ : ℝ) - 3 / 4 * (L ^ 2 / R)) < H.time i.succ from max_lt hcs (by linarith))]
    with t hsh hbt hgt hti
  intro tt htt htσ a haS' hat hlo z' hP A v hav hvt
  have ht1 : H.time i.castSucc < t := lt_of_le_of_lt (le_max_left _ _) hti.1
  have ht2 : (σ : ℝ) - 3 / 4 * (L ^ 2 / R) < t := lt_of_le_of_lt (le_max_right _ _) hti.1
  have he : H.activeStage tt = i.castSucc :=
    H.activeStage_eq_of_mem_slab_P6F3 i tt (by rw [htt]; exact ht1.le) (by rw [htt]; exact hti.2)
  have haStt : aSeed ≤ tt := haS'.trans hat
  have httT : tt ≤ Tn := htσ.trans hsT
  obtain ⟨y', hy'⟩ := H.exists_heq_stageAt_P6JW he p'
  obtain ⟨hdtt, -, hballT⟩ := H.transport_at_stage_P6JW haT seedTrace haStt httT he htt y' p' hy'
    h1i h2c
  have hdy : riemannianEDistOf (H.stageMetric (H.activeStage tt) tt)
        (seedTrace.point (H.activeStage tt) (H.activeStage_mono haStt) (H.activeStage_mono httT))
        y' ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has) (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / 2 / Real.sqrt R) := by
    rw [hdtt, hdσ_eq]
    exact hsh
  have htt' : (tt : ℝ) = t := htt
  have hgood' : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ tt),
      (tt : ℝ) - (L / 2) ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans httT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage tt) tt)
              (seedTrace.point (H.activeStage tt) (H.activeStage_mono haStt)
                (H.activeStage_mono httT)) y' +
            ENNReal.ofReal (L / 2 / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
    intro w haw hwt hwL z hz hRz
    refine hgood w haw (hwt.trans htσ) (by linarith) z (hz.trans ?_) hRz
    exact (add_le_add hdy le_rfl).trans (le_of_eq (hsum _))
  have hTR : T / R ≤ (L / 2) ^ 2 / R := (div_le_div_iff_of_pos_right hR).2 hTL
  have haL : (tt : ℝ) - (L / 2) ^ 2 / R ≤ a := by linarith
  have hdepth : (tt : ℝ) - a ≤ T / R := by linarith
  have haS'' : (aSeed : ℝ) ≤ a := haS'
  have hRa' : 1 ≤ R * a := hRa.trans (mul_le_mul_of_nonneg_left haS'' hR.le)
  obtain ⟨zc, hzc⟩ := H.exists_heq_stage_P6JW he z'
  have hzball := hP zc hzc
  obtain ⟨-, hRzeq, hballeq⟩ := H.transport_at_stage_P6JW haT seedTrace haStt httT he htt z' zc
    hzc h1i h2c
  have hzy : z' ∈ riemannianBallOf (H.stageMetric (H.activeStage tt) tt) y'
      (ρb / Real.sqrt R) := by
    rw [hballeq y' p' hy' (ρb / Real.sqrt R), stageMetric_castSucc_apply]
    exact hzball
  have hz' : metricScalarAt (H.stageMetric (H.activeStage tt) tt) z' ≤ Cball * R := by
    rw [hRzeq, stageMetric_castSucc_apply]
    exact hbt zc hzball
  have hdfin : riemannianEDistOf (H.stageMetric (H.activeStage tt) tt)
      (seedTrace.point (H.activeStage tt) (H.activeStage_mono haStt) (H.activeStage_mono httT))
      y' ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩) hdy
  have httH : (tt : ℝ) < H.horizon := by
    have h1 : (tt : ℝ) < H.time i.succ := by rw [htt]; exact hti.2
    have h2 : (σ : ℝ) ≤ H.horizon := σ.2.2
    linarith
  subst hKH
  have hgrid0 : ∀ (j : ℕ) (w : Icc (0 : ℝ) KH.toHistory.horizon) (haw : a ≤ w) (hwt : w ≤ tt),
      (w : ℝ) = tt - j * β / R →
      metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage w) w)
        (A.point (KH.toHistory.activeStage w) (KH.toHistory.activeStage_mono haw)
          (KH.toHistory.activeStage_mono hwt)) ≤ Qb * R := by
    intro j w haw hwt hw
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hwtt : w = tt := Subtype.ext (by simpa using hw)
      subst hwtt
      have hpt : A.point (KH.toHistory.activeStage w) (KH.toHistory.activeStage_mono haw)
          (KH.toHistory.activeStage_mono hwt) = z' := A.endpoint_eq
      rw [hpt]
      have hCQ : Cball ≤ Qb := (le_max_left _ _).trans ((le_max_left _ _).trans hQb)
      exact hz'.trans (mul_le_mul_of_nonneg_right hCQ hR.le)
    · exact hgt tt htt htσ a haS' hat hlo z' hP A j hj w haw hwt (by rw [hw, htt'])
  have hQb' : max Cg 1 ≤ Qb := (max_le_max (le_max_right _ _) le_rfl).trans hQb
  have hQQ : max (max Qb Cg) 1 ≤ Qb :=
    max_le (max_le le_rfl ((le_max_right _ _).trans ((le_max_left _ _).trans hQb)))
      ((le_max_right _ _).trans hQb)
  have hscalC := hballT_grid_of_depthInduction_P6BB KH.toHistory haT seedTrace httT haStt y'
    (L / 2) hR (by linarith) hgood' hβ hβs hQQ haS' hat haL A hgrid0
  have hprotC := hprotC_scalC_CXJP KH haT hsmall hclock seedTrace httT haStt y' (L / 2) haS' hat A
    hscalC records hDm hnc (fun e he' b hlt => hscale e he' b (lt_of_le_of_lt haS'' hlt))
  have hres := hgoodV_scalC_CXJP hC2 KH haT hsmall hclock seedTrace ha₀ hpin httT haStt y' (L / 2)
    hR hgood' hQb' haS' hat (fun h => absurd h (ne_of_lt httH)) haL hdepth hRa' A hscalC hℓ hKℓ hℓr
    hKr hKC hℓρ hρL (hT₀.trans haS'') records hOld hcan (hacc.trans (min_le_right _ _)) hDm hprotC
    hzy hdfin hnum v hav hvt
  have hq : L / 2 / 2 / Real.sqrt R ≤ L / 2 / Real.sqrt R :=
    div_le_div_of_nonneg_right (by linarith) hsR.le
  exact hres.le.trans ((add_le_add hdy (ENNReal.ofReal_le_ofReal hq)).trans (le_of_eq (hsum _)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
