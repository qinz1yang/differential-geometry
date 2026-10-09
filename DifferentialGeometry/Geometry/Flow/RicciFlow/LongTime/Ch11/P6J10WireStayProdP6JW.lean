import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireStayP6JW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10CrossSlabProtCXJD

/-!
# J10WIRE G2b：`hstopE` 的单 k 体 ⇐ CXJD first-exit + crossing 参考点平移（O-CH11-J10WIRE，`_P6JW`）

G2 `hstayΩ_of_hstop_P6JW` 的 binder `hstopE` 在每个 `k` 上的体（`∀ᶠ t ∈ 𝓝[<] time i⁺, …`）由 CXJD 直接产出：
* `ObservedHistory.exists_heq_stageAt_P6JW` / `exists_heq_stage_P6JW` /
  `transport_at_stage_P6JW`（PROVED）：
  `activeStage τ = k`、`τ = s`、`w ≍ w′` ⇒ seed 距离、标量、球成员关系在两种索引下相同（`subst` 型）。
* `ObservedHistory.hstopE_body_of_firstExit_P6JW`（PROVISIONAL，CXJD binder 族 + `hball`）：
  (a) **参考点跨 crossing**：`surgery_no_shortcut_C11D`（event `i`，`seedTrace.crossing i` 与
  `p′ ↦ q′ ≍ y`）给
  `∀ᶠ t ↑ σ`，`d_{i⁻,t}(seed, p′) ≤ d_{i⁺,σ}(seed, q′) + L/(2√R)`；两点保护：seed 点标量 `≤ 3/r²`
  （`seed_scalar_le_of_smallParabolic_C11G`）、`q′` 标量 `= R`（`hRy`），由 `hscale` 小于 `scale/2`，再经树内
  `exists_not_ageZeroCapPoint_of_scalar_lt_C11G`（`ε₀`）排除 cap window 内区；
  (b) **hgood 迁移**：`(σ, y, L)` ⇒ `(tt, y′ ≍ p′, L/2)`（`t > σ − ¾L²/R`，区域包含）；
  (c) **CXJD** `hstop_of_firstExit_CXJD` 在 `σ′ := tt`（`activeStage tt = i⁻ < last`）、`a`、`z′`、`A`、
  `L/2`
  处，`hprotC` 由 `hprotC_of_ceiling_CXJD` 付；预算 `d_tt(seed, y′) + L/(2√R) ≤ d_σ(seed, y) + L/√R`。
  binder：CXJD 族（K0 `hsmall`/`hclock`、HI `hpin`、`hgood`、records / `hOld` / `hcan` / `hDm` / `ε₀` /
  `hm`、
  `hscale`、数值 `ℓ, K`（`L/2` 处）、`hfin`）+ `hRy`（`R = R(σ, y)`，即 `hstayΩ` 前缀的 `hRdef`）+
  **端点球控制** `hball`（`B_t(p′, ρ_b/√R)` 上 `R ≤ Cball·R`，`t ↑ σ`；`hstayΩ` 前缀不含，PROVISIONAL）。
**R-C11-17 对账**：(1) 端点球 Ric：CXJD 内 `hRicC_of_hgood_ceiling_CXJD` 整球；本文件新增的 crossing 平移不用
Ric（terminal 极限）。(2) `E_cross`：窗口 `[a, tt]` 内的 crossing 由 CXJD 链吸收（零跳跃），`tt → σ` 的唯一一次
平移误差 `L/(2√R)` 显式记账，总预算 `L/√R`。(3) 量词：结论与 `hstopE` 体逐字同层（∀ tt a z′ A v）。
**未做（HANDOVER）**：塔层打包——把本定理的 binder 族提升到 `hstayΩ` 前缀（∀ T r ind c … i hi，逐 k），
数值由 `crossSlab_numerics_P6JW`（`L/2`）、`ε₀` 由 records 精度序列付。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- `activeStage τ = k` ⇒ `stage k` 的点在 `stageAt τ` 中有 HEq 代表（`_P6JW`）。 -/
theorem exists_heq_stageAt_P6JW (H : ObservedHistory.{u}) {τ : Icc (0 : ℝ) H.horizon}
    {k : Fin (H.eventCount + 1)} (hk : H.activeStage τ = k) (w : (H.stage k).Carrier) :
    ∃ w' : (H.stageAt τ).Carrier, HEq w' w := by
  subst hk
  exact ⟨w, HEq.rfl⟩

/-- `activeStage τ = k` ⇒ `stageAt τ` 的点在 `stage k` 中有 HEq 代表（`_P6JW`）。 -/
theorem exists_heq_stage_P6JW (H : ObservedHistory.{u}) {τ : Icc (0 : ℝ) H.horizon}
    {k : Fin (H.eventCount + 1)} (hk : H.activeStage τ = k) (w : (H.stageAt τ).Carrier) :
    ∃ w' : (H.stage k).Carrier, HEq w w' := by
  subst hk
  exact ⟨w, HEq.rfl⟩

/-- 索引迁移（`_P6JW`，PROVED）：`activeStage τ = k`、`τ = s`、`w ≍ w′` ⇒ seed 距离、标量、球成员关系相同。 -/
theorem transport_at_stage_P6JW (H : ObservedHistory.{u}) {Tn aSeed : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {τ : Icc (0 : ℝ) H.horizon} (haτ : aSeed ≤ τ) (hτT : τ ≤ Tn) {k : Fin (H.eventCount + 1)}
    (hk : H.activeStage τ = k) {s : ℝ} (hs : (τ : ℝ) = s) (w : (H.stageAt τ).Carrier)
    (w' : (H.stage k).Carrier) (hw : HEq w w') (h1 : H.activeStage aSeed ≤ k)
    (h2 : k ≤ H.activeStage Tn) :
    riemannianEDistOf (H.stageMetric (H.activeStage τ) τ)
        (seedTrace.point (H.activeStage τ) (H.activeStage_mono haτ) (H.activeStage_mono hτT)) w =
      riemannianEDistOf (H.stageMetric k s) (seedTrace.point k h1 h2) w' ∧
    metricScalarAt (H.stageMetric (H.activeStage τ) τ) w =
      metricScalarAt (H.stageMetric k s) w' ∧
    ∀ (c : (H.stageAt τ).Carrier) (c' : (H.stage k).Carrier), HEq c c' → ∀ ρ : ℝ,
      (w ∈ riemannianBallOf (H.stageMetric (H.activeStage τ) τ) c ρ ↔
        w' ∈ riemannianBallOf (H.stageMetric k s) c' ρ) := by
  subst hk
  subst hs
  obtain rfl := eq_of_heq hw
  refine ⟨rfl, rfl, fun c c' hc ρ => ?_⟩
  obtain rfl := eq_of_heq hc
  exact Iff.rfl

/-- **G2b（`_P6JW`，PROVISIONAL：CXJD binder 族 + `hRy` + `hball`）**：`hstopE` 在单个 `k` 上的体。 -/
theorem hstopE_body_of_firstExit_P6JW :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T K ℓ ρb : ℝ} (_ : 0 ≤ C2')
    (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
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
    (_ : max (max Cball Cg) 1 ≤ Qb) (_ : 2 * Ctime' * Qb * T ≤ 1) (_ : 0 < T)
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
        metricScalarAt ((H.event i).incoming.flow.base.metric t) z ≤ Cball * R),
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
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ ρb hC2 H Tn aSeed σ haT pT r hsmall hclock seedTrace
    a₀ ha₀ hpin hsT has y R L hR hgood hQb hstep hT hTL hL hRa haσ hRy hℓ hKℓ hℓr hKr hKC hℓρ hρL
    hnum q T₀ hT₀ records hOld hcan hDm hacc hm hscale hfin i hσi p' q' hyq hcross hball
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
  filter_upwards [hshift, hball, Ioo_mem_nhdsLT (show max (H.time i.castSucc)
      ((σ : ℝ) - 3 / 4 * (L ^ 2 / R)) < H.time i.succ from max_lt hcs (by linarith))]
    with t hsh hbt hti
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
  have hσl : H.activeStage tt < Fin.last H.eventCount := he ▸ Fin.castSucc_lt_last i
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
  have hprotC := hprotC_of_ceiling_CXJD H haT hsmall hclock seedTrace httT haStt y' (L / 2) hR
    (by linarith) hgood' hQb hstep haS' hat hσl haL hdepth hz' A records hDm hnc
    (fun e he' b hlt => hscale e he' b (lt_of_le_of_lt haS'' hlt))
  have hres := hstop_of_firstExit_CXJD hC2 H haT hsmall hclock seedTrace ha₀ hpin httT haStt y'
    (L / 2) hR hgood' hQb hstep haS' hat hσl haL hdepth hRa' hz' A hℓ hKℓ hℓr hKr hKC hℓρ hρL
    (hT₀.trans haS'') records hOld hcan (hacc.trans (min_le_right _ _)) hDm hprotC hzy hdfin hnum
    v hav hvt
  exact hres.trans ((add_le_add hdy le_rfl).trans (le_of_eq (hsum _)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
