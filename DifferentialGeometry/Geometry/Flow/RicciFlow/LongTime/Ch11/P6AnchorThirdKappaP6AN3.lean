import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorThirdP6AN3

/-!
# ANCHOR 第三轮 G4：top 版 κ 半 ⇐ P6CD `hkappa`、梯度半的全域背景接线（O-CH11-ANCHOR3，后缀 `_P6AN3`）

G1 的 G3 发现：top 时刻（`v = σ`、`w = y`）的 picked-ball 梯度 / κ 半若走 SEEDCL / PBKAPPA 现有 producer 会循环
（两者都要 top 点 hpick = top 球 BCBD，半径 ≥ ShortSLT 的 `Rad`，比 `hanchor0` 还强）。本文件给非循环来源：
* **κ 半（PROVED ⇐ P6CD 层已有 supply `hkappa`）**：`pickedBallKappa_top_of_hkappa_P6AN3` /
  `pickedBallKappa_top_seq_of_hkappa_P6AN3`：窗口内 `τ` 与 `σ` 同 stage（`(j n)⁻`），trace 取
  `BackwardPointTrace.singleton`（`exists_trace_of_eq_P6AN3`），`ofReal (κ r³) = ofReal κ · ofReal r ³`
  （`kappa_sameStage_of_trace_P6AN3`）。不需要 hpick / `PickedBallEndpointRicci_C11PK`。
* **梯度半（接线变体）**：`pickedBallGrad_of_gradientBound_P6AN3` ⇐ event slab 的
  `GradientBoundBefore Cgrad qg`——旧的全域梯度背景（cap-side），与导数背景同类，按 R-C11-17 登记为
  向 `q_sel` 合同迁移的义务（J10GEN）。
  局域来源（canonical neighbourhood 梯度估计：spatial canonical witness ⇒ `|∇R| ≤ C R^{3/2}`）是 repair target
  （owner 后继 ANCHOR4 / 外审 R-C11-18），本文件不做。
* 组合：`topAnchorInputs_of_hgood_hkappa_P6AN3`（picked-ball binder 全消）；全链
  `hdistW_eventSlab_of_hgood_P6AN3`（`hdistW` 槽逐字；κ 用链上同一个 `hkappa`）。
非循环：前提中无 `hdistW / HU / hgapJ / hclosG / CanonicalLateCore / hspine`，也无 hpick。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section KappaTop

/-- **同 index 的平凡 trace（`_P6AN3`）**：`a = s` ⇒ 有 `BackwardPointTrace H a s h x` 且其 `a` 点 `≅ x`
（`BackwardPointTrace.singleton` + `endpoint_eq`）。 -/
theorem exists_trace_of_eq_P6AN3 (H : ObservedHistory.{u}) {a s : Fin (H.eventCount + 1)}
    (h : a ≤ s) (has : a = s) (x : (H.stage s).Carrier) :
    ∃ tr : BackwardPointTrace H a s h x, HEq (tr.point a le_rfl h) x := by
  subst has
  exact ⟨BackwardPointTrace.singleton H a x,
    heq_of_eq (BackwardPointTrace.singleton H a x).endpoint_eq⟩

/-- **同 stage κ（`_P6AN3`）**：`activeStage τ = activeStage σ`、`τ ≤ σ` 时，trace-local κ（P6CD `hkappa` 形，
`ballVolume`、`ofReal (κ r³)`）在平凡 trace 上 ⇒ tested 形（`ofReal κ · ofReal b ³ ≤ vol`，中心 `zz ≅ x`）。 -/
theorem kappa_sameStage_of_trace_P6AN3 (H : ObservedHistory.{u}) {σ τ : Icc (0 : ℝ) H.horizon}
    (hτσ : τ ≤ σ) (hidx : H.activeStage τ = H.activeStage σ) (x : (H.stageAt σ).Carrier)
    (zz : (H.stageAt τ).Carrier) (hzz : HEq zz x) {κ ρnc b : ℝ} (hκ : 0 ≤ κ) (hb : 0 < b)
    (hbρ : b ≤ ρnc)
    (hK : ∀ tr : BackwardPointTrace H (H.activeStage τ) (H.activeStage σ)
        (H.activeStage_mono hτσ) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc →
        H.isParabolicallyRmControlledBall τ
          (tr.point (H.activeStage τ) le_rfl (H.activeStage_mono hτσ)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume (H.stageMetric (H.activeStage τ) τ)
            (tr.point (H.activeStage τ) le_rfl (H.activeStage_mono hτσ)) r'')
    (hball : H.isParabolicallyRmControlledBall τ zz b) :
    ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt τ).Carrier (H.stageMetric (H.activeStage τ) τ)
        (riemannianBallOf (H.stageMetric (H.activeStage τ) τ) zz b) := by
  obtain ⟨tr, htr⟩ := exists_trace_of_eq_P6AN3 H (H.activeStage_mono hτσ) hidx x
  have he : zz = tr.point (H.activeStage τ) le_rfl (H.activeStage_mono hτσ) :=
    eq_of_heq (hzz.trans htr.symm)
  subst he
  have h := hK tr b hb hbρ hball
  rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **top 版 κ 半 ⇐ P6CD `hkappa`（`_P6AN3`，PROVED，单个 history）**：σ 在 event slab `j` 内部、`y ≅ yG`、
`R = R(σ, yG) > 0`、`β ≤ T`、`Rad ≤ D`；P6CD 层 trace-local κ（`B_σ(y, D/√R)` 的点、`v ≥ σ − T/R` 的 trace、
半径 `≤ ρnc`）⇒ `PickedBallKappa_C11PB β Rad ρnc κ K j σ yG`。窗口内 `τ` 与 `σ` 同 stage（`(j)⁻`），trace 取
`BackwardPointTrace.singleton`；**不需要** hpick / `PickedBallEndpointRicci_C11PK`（避开 top 点循环）。 -/
theorem pickedBallKappa_top_of_hkappa_P6AN3 (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (hσ1 : K.time j.castSucc < σ)
    (hσ2 : (σ : ℝ) < K.time j.succ) (y : (K.toHistory.stageAt σ).Carrier)
    (yG : (K.stage j.castSucc).Carrier) (hyG : HEq y yG) {R κ ρnc D T β Rad : ℝ}
    (hR : R = (K.toHistory.event j).incoming.flow.scalar σ yG) (hRpos : 0 < R) (hκ : 0 ≤ κ)
    (hβT : β ≤ T) (hRadD : Rad ≤ D)
    (hK : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
          (D / Real.sqrt R),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvt : v ≤ σ), (σ : ℝ) - T / R ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
        (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc →
        K.toHistory.isParabolicallyRmControlledBall v
          (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'') :
    PickedBallKappa_C11PB β Rad ρnc κ K j σ yG := by
  subst hR
  intro τ hτ1 hτ2 hτ3 hτ4 z hz zz hzz b hb hbρ hball
  have hactσ := K.activeStage_eq_castSucc_C11PB j σ hσ1 hσ2
  have hactτ := K.activeStage_eq_castSucc_C11PB j τ hτ3 hτ4
  have hτσ : τ ≤ σ := hτ2
  have key : ∀ (k : Fin (K.eventCount + 1)) (hk : K.toHistory.activeStage σ = k)
      (y' z' : (K.toHistory.stage k).Carrier), HEq y y' →
      z' ∈ riemannianBallOf (K.toHistory.stageMetric k σ) y'
        (D / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar σ yG)) →
      ∃ x : (K.toHistory.stageAt σ).Carrier, HEq x z' ∧
        x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
          (D / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar σ yG)) := by
    intro k hk
    subst hk
    intro y' z' hy hz'
    obtain rfl := eq_of_heq hy
    exact ⟨z', HEq.rfl, hz'⟩
  have hzD : z ∈ riemannianBallOf (K.toHistory.stageMetric j.castSucc σ) yG
      (D / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar σ yG)) := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right hRadD (Real.sqrt_nonneg _)) hz
  obtain ⟨x, hxz, hxb⟩ := key j.castSucc hactσ yG z hyG hzD
  have hwin : (σ : ℝ) - T / (K.toHistory.event j).incoming.flow.scalar σ yG ≤ τ := by
    have := div_le_div_of_nonneg_right hβT hRpos.le
    linarith
  exact kappa_sameStage_of_trace_P6AN3 K.toHistory hτσ (hactτ.trans hactσ.symm) x zz
    (hzz.trans hxz.symm) hκ hb hbρ (hK x hxb τ hτσ hwin) hball

/-- **top 版 κ 半，序列形（`_P6AN3`，PROVED ⇐ P6CD `hkappa`）**：`hkappa`（K 形，`Kh = (K ·).toHistory`）+
event-slab selection（`hjt / htj`、`σ = t`、`y ≅ yG`、`R_n = R(t n, yG n) > 0`）⇒ 对每个 `Rad`，eventually
`PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n)`（取 `D := max Rad 1`、`T := max β 1`）。
= `pickedBallTopData_of_hgood_P6AN3` 的 `hκPB` 前提。 -/
theorem pickedBallKappa_top_seq_of_hkappa_P6AN3 {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier}
    {R : ℕ → ℝ} (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRpos : ∀ n, 0 < R n) {κ β : ℝ} (hκ : 0 ≤ κ) {ρnc : ℕ → ℝ}
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
        ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (K n).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((K n).toHistory.activeStage v) le_rfl
            ((K n).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) r'') :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n) := by
  intro Rad
  filter_upwards [hkappa (max Rad 1) (max β 1) (lt_max_of_lt_right one_pos)
    (lt_max_of_lt_right one_pos)] with n hn
  have h1 : (K n).time (j n).castSucc < σ n := by
    rw [hσ n]
    exact hjt n
  have h2 : ((σ n : ℝ)) < (K n).time (j n).succ := by
    rw [hσ n]
    exact htj n
  have hR' : R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) := by
    rw [hσ n]
    exact hRn n
  have h := pickedBallKappa_top_of_hkappa_P6AN3 (K n) (j n) (σ n) h1 h2 (y n) (yG n) (hyG n) hR'
    (hRpos n) hκ (le_max_left β 1) (le_max_left Rad 1) hn
  rw [hσ n] at h
  exact h

/-- **top 版梯度半 ⇐ 旧全域梯度背景（`_P6AN3`，接线变体）**：event `j` incoming slab 的
`GradientBoundBefore Cgrad qg v`（阈值 `qg ≤ qthr`）⇒ `PickedBallGrad_C11PB β Rad qthr Cgrad K j v w`（任意
`β, Rad`）。**注意**：这是旧的全域梯度背景（cap-side），与导数背景同类，按 R-C11-17 登记为向 `q_sel` 合同迁移的
义务（J10GEN）；局域来源（canonical neighbourhood 梯度估计）是 repair target，不在本车道。 -/
theorem pickedBallGrad_of_gradientBound_P6AN3 (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    (v : ℝ) (w : (K.stage j.castSucc).Carrier) {β Rad qthr qg : ℝ} {Cgrad : ℝ≥0}
    (hqg : qg ≤ qthr) (hG : (K.toHistory.event j).incoming.GradientBoundBefore Cgrad qg v) :
    PickedBallGrad_C11PB β Rad qthr Cgrad K j v w :=
  fun x _ v' hv' _ hq ξ => hG x v' hv' (lt_of_le_of_lt hqg hq) ξ

/-- **`topAnchorInputs_of_hgood_hkappa_P6AN3`（G4 组合，PROVISIONAL：picked-ball binder 已消去；剩余 = 旧全域
导数 `hslab / hderG` 与梯度 `hgradG` 背景（J10GEN 迁移义务）+ P6CD 层 supplies（含 `hkappa`）+ hgood）**：
`topAnchorInputs_of_hgood_P6AN3` 的 `hgradPB` ⇐ `pickedBallGrad_of_gradientBound_P6AN3`，`hκPB` ⇐
`pickedBallKappa_top_seq_of_hkappa_P6AN3`（P6CD `hkappa`，同 stage 平凡 trace）。top 点不用 hpick（无循环）。 -/
theorem topAnchorInputs_of_hgood_hkappa_P6AN3 {β : ℝ} (hβ : β ≤ 1 / 2)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    {D θcap qcan T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)}
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    {Ctime : ℝ≥0} {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi)
    (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount))
    (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
      t n) atTop atTop)
    {Cg : ℝ} (hCg : 0 < Cg)
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {ε C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L ε C1 C2 Ctg)
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hL : Tendsto L atTop atTop) (hε : ε ≤ coneAccuracy) {κ : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {ρnc : ℕ → ℝ} (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    {qg : ℕ → ℝ} (hqg : ∀ n, qg n ≤ Cg * R n)
    (hgradG : ∀ n,
      ((K n).toHistory.event (j n)).incoming.GradientBoundBefore Cgrad (qg n) (t n))
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
        ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (K n).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((K n).toHistory.activeStage v) le_rfl
            ((K n).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) r'') :
    TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (j n).castSucc)
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
      (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
      yG := by
  have hRpos : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  exact topAnchorInputs_of_hgood_P6AN3 hβ hjt htj hcan hqcan hpar hscale hθcap hphi hpinch hslab
    hderG hqR hnot hT₀ hRt hCg hgood hσ hyG hRn hL hε hκ hradii
    (fun _ => Eventually.of_forall fun n =>
      pickedBallGrad_of_gradientBound_P6AN3 (K n) (j n) (t n) (yG n) (hqg n) (hgradG n))
    (pickedBallKappa_top_seq_of_hkappa_P6AN3 hjt htj hσ hyG hRn hRpos hκ.le hkappa)

/-- **`hdistW_eventSlab_of_hgood_P6AN3`（G4 全链，PROVISIONAL：binder = `hbcadC` + P6CD 层 supplies（含
`hkappa / hseed / hwitC`）+ hgood + 旧全域导数 / 梯度背景 `hslab / hderG / hgradG`（J10GEN 迁移义务））**：
`hscalW_eventSlab_to_hdistW_P6AN3` 的 `TopAnchorInputs` 由 `topAnchorInputs_of_hgood_hkappa_P6AN3` 供
（κ 用链上**同一个** `hkappa`；`Kh = (K ·).toHistory` 经 `subst`）。picked-ball binder
（`hpb / hgradPB / hκPB`）与 hpick 全部不出现。结论 = `hdistW` 槽逐字（event 支）。 -/
theorem hdistW_eventSlab_of_hgood_P6AN3 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      {β : ℝ} → (hβ : 0 < β) →
      (hβ2 : β ≤ 1 / 2) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      ∀ {Cg εg C1g C2g : ℝ} {Ctg : ℝ≥0}, 0 < Cg → εg ≤ coneAccuracy →
      ObservedHistory.HgoodCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L εg C1g C2g
        Ctg →
      ∀ {qg : ℕ → ℝ} {Cgrad : ℝ≥0}, (∀ n, qg n ≤ Cg * R n) →
      (∀ n, ((K n).toHistory.event (j n)).incoming.GradientBoundBefore Cgrad (qg n) (t n)) →
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      ∀ {a₁ : ℝ}, 0 ≤ a₁ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₁ + τ') x) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Ctime phi ε hε hεX hεN hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hβ hβ2 Kh hKh σ y R
    hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC Tn aSeed haT
    hsT has pT seedTrace L r Cg εg C1g C2g Ctg hCg hεg hgood qg Cgrad hqg hgradG hL hsmall hclock
    hRr hwin a₁ ha₁ hpin
  subst hKh
  have hin := topAnchorInputs_of_hgood_hkappa_P6AN3 hβ2 hjt htj hcan hqcan hpar hscale hθcap hphi
    hpinch hslab hderG hqR hnot hT₀ hRt hCg hgood hσ hyG hRn hL hεg hκ hradii hqg hgradG hkappa
  exact hscalW_eventSlab_to_hdistW_P6AN3 hε hεX hεN hphi hjt htj recordsF ha₀ hHI hcan hδF hqcan
    hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hβ hin (fun n => (K n).toHistory) rfl σ y
    R hσ hyG hRn hr₀ hw hseed hκ ρnc hradii hkappa hqs hwitC hbcadC Tn aSeed haT hsT has pT
    seedTrace L r hL hsmall hclock hRr hwin ha₁ hpin

end KappaTop

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
