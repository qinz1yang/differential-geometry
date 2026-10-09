import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallSeedC11PB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.Pre841E2EFwdC11FR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.SmoothDistortionC11D

/-!
# picked-ball κ 覆盖的 FRESH producer（O-CH11-PBKAPPA，后缀 `_C11PK`）

PICKBALL 的 **hκ** = `PickedBallKappa_C11PB β Rad ρ κ`（二次选点球 `B_v(w, Rad/√q)`、共同窗口
`[v − β/q, v] ∩ slab`、半径 `≤ ρ` 的 controlled ball κ-noncollapsed）。本文件走 FRESH forward κ 路线，
**不经** Pre841（`nonempty_pre841Data_of_retention_fwd_C11FR` 的粗 seed `hdist`：所有 backward traces 落在
`A·r` footprint，SHALLOW-TOOLS §3 指出它绕回第 1 项），也不经 CXSK center 小工具。

## 路线（R-C11-12 D-9(3)；R-C11-10 D-10）
* **supply 形** `KappaSeedWindowFwd_C11PK nr A κ T H`：FRESH window-zero 输出
  （`localKappaWindow_zero_of_window_and_smallFwd_C11FR`）在单条 history `H` 上的逐字形：seed `(t, p, r)`
  （K0、`A⁻¹r³` 体积、`nr ≤ r` 窗口形、`aSeed = t − r²`）⇒ `v ∈ [t − r²/2, t]`、`x ∈ B_v(O_v, A·r)`、
  `0 ≤ ρ′ < r/100` 的 controlled ball `κρ′³ ≤ Vol`。producer（PROVED）
  `GC.LongTime.Ch11.kappaSeedWindowFwd_of_retention_C11PK`：retention 数据（`N rad Df …`，与 FRESH 的
  Pre841 存在定理同一组前提，**去掉** `hdist / hradii / hwin / hratio` 与 seed 序列）⇒ `∃ κ T, ∀ n, supply`。
* **G1** `pickedBallKappa_of_fresh_C11PK`（PROVED）：supply + selection 的 original seed prefix
  `(Tn, pT, r, aSeed, seedTrace)` + 窗口包含 `Tn − r²/2 ≤ v − β/q`、`v ≤ Tn` + **粗 footprint**
  `PickedBallFootprint_C11PK`（`d_τ(O, z) < A·r`，球内所有点、窗口所有时刻，无曲率阈值）+ `ρ < r/100`
  ⇒ `PickedBallKappa_C11PB`（结论逐字）。
* **粗 footprint 的生产**（PROVED，`pickedBallFootprint_of_distortion_C11PK`）：中心 `d_v(O, w) ≤ D₀`
  + 球半径 `Rad/√q` + 短窗 I.8.3(b) 距离畸变（`smooth_distance_distortion_C11D`，同一 slab，
  `d_τ ≤ d_v + (8/ℓ)(v − τ) ≤ d_v + 8β/(ℓ q)`）。**唯一新 binder**
  `PickedBallEndpointRicci_C11PK ℓ β Rad`（PROVISIONAL；两端 `ℓ`-球 `Ric ≤ (3/ℓ²) g`，`ℓ = ℓ₀/√q`，即
  `Ric ≤ 3q/ℓ₀²`；owner = DIST / PICKBALL `SurvivalOrCap` 的 Rm 界 + pinching；本车道不证）。
* **组合** `pickedBallKappa_of_fresh_distortion_C11PK`：top gate `hdσ`
  （`dσ + (L + 1)/√R_n ≤ A·r`，**与 J11 / PICKBALL G5 / `regionalKappa_of_closure_P6L3` 的 `hdσ` 同一陈述**，
  同一 original-seed prefix + 固定 `A`；只付一次）+ 中心 Good(L/2)（`hκPB` 自带前提）+ 端点 Ricci binder +
  `2(max Rad 0 + 8β/ℓ₀) ≤ L` ⇒ `PickedBallKappa_C11PB`。
* **G2** `hκPB_of_fresh_C11PK`：结论 = G4 `shallowSliceRC_of_pickedBall_seed_C11PB` 的 `hκPB` 逐字；
  consumer `ObservedHistory.shallowSliceRC_of_pickedBall_fresh_C11PK`：SHALLOW T1 的 `hκPB` 换成
  supply + seed prefix + `hwinF` + `hρr` + `hdσ` + 端点 Ricci binder 族 `hRicPB`（量词前缀同 `hκPB`）。

## 与 D-10 J11 footprint gate 的关系
J11 的 κ-volume 对 `B_σ(y, D/√R)` 的**所有** backward traces（跨 event，深度 `B/R`）量化 ⇒ 需要 Pre841 的
全 trace `hdist`（D-10 的缺口）。picked-ball κ 只需球 × 单 slab 短窗 `[v − β/q, v]`，中心已 Good(L/2)，故：
**top gate 同一义务**（`hdσ`，同名同式）；**窗口部分不是 J11 的 hdist**，只是端点局部 Ricci（局部曲率，无
seed 距离）。PICKBALL 的 `hseed`（带阈值 `R > Cg·R_n`）覆盖不到全球点，给不出 footprint；G5 的细 `hseedAll`
（`hclosC` 内层）在本路线**不需要**（κ 只要粗 `A·r`）。seed closure 归 SEEDCL。
非循环：import G4（PICKBALL）、FRESH `Pre841E2EFwdC11FR`、`SmoothDistortionC11D`；不经 Pre841 存在定理 / hdist /
hscalU / hclosG / hclosC / hUVC 生产者 / CanonicalLateCore / hspine（审计名字扫描）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Defs

/-- **FRESH window-zero supply（`_C11PK`，单条 history 形）**：
`localKappaWindow_zero_of_window_and_smallFwd_C11FR` 的结论体逐字（`∀ n, let H := …` 去掉 `n`）。
seed `(t, p, r)`：`T ≤ t`、`2r² < t`、K0、`A⁻¹r³ ≤ Vol`、`∀ w ∈ [t − r²/2, t], nr w ≤ r`、
`aSeed = t − r²`；
结论：`v ∈ [t − r²/2, t]`、`x ∈ B_v(O_v, A·r)`、`0 ≤ ρ′ < r/100`、controlled ⇒ `κρ′³ ≤ Vol`。 -/
def KappaSeedWindowFwd_C11PK (nr : ℝ → ℝ) (A κ T : ℝ) (H : ObservedHistory.{u}) : Prop :=
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → GC.LongTime.hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → nr w ≤ r) →
    ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t), (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono haT) p,
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
      (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
      (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
      (A * r),
    ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
      ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ'

/-- **粗 footprint（`_C11PK`）**：球 `B_v(w, Rad/√q)` 的所有点 `z`、窗口 `τ ∈ [v − β/q, v]`、`time j⁻ < τ`
⇒ `d_τ(O, z) < D`（`K.event j` incoming metric；`O` = seed 点在 stage `j⁻` 的位置）。κ 只需
`D = A·r`（宏观），无曲率阈值。形同 G5 的 `PickedBallWindowSeedAll_C11PB`（严格 `<`、粗 `D`）。 -/
def PickedBallFootprint_C11PK (β Rad : ℝ) (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    (v : ℝ) (w O : (K.stage j.castSucc).Carrier) (D : ℝ≥0∞) : Prop :=
  ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
    ∀ τ : ℝ, v - β / (K.toHistory.event j).incoming.flow.scalar v w ≤ τ → τ ≤ v →
      K.time j.castSucc < τ →
      riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric τ) O z < D

/-- **端点 Ricci（`_C11PK`，PROVISIONAL binder，本车道唯一新 binder）**：球点 `z`、窗口内部
`t ∈ (v − β/q, v)`、`time j⁻ < t`，两端 `ℓ`-球（`B_t(O, ℓ)` 或 `B_t(z, ℓ)`）上 `Ric ≤ (3/ℓ²) g`
（= `smooth_distance_distortion_C11D` 的 `hRic` 形；取 `ℓ = ℓ₀/√q` 即 `Ric ≤ 3q/ℓ₀²`）。
owner = DIST / PICKBALL（`PickedBallSurvivalOrCap_C11PB` 的 Rm 界 + pinching ⇒ 球端；seed 端由 K0 seed
shift）。 -/
def PickedBallEndpointRicci_C11PK (ℓ β Rad : ℝ) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w O : (K.stage j.castSucc).Carrier) : Prop :=
  ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
    ∀ t : ℝ, v - β / (K.toHistory.event j).incoming.flow.scalar v w < t → t < v →
      K.time j.castSucc < t →
    ∀ (y : (K.stage j.castSucc).Carrier) (ξ : TangentSpace ThreeModel y),
      (riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric t) O y <
          ENNReal.ofReal ℓ ∨
        riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric t) z y <
          ENNReal.ofReal ℓ) →
      ricciTensor ((K.toHistory.event j).incoming.flow.base.metric t) y ξ ξ ≤
        (3 / ℓ ^ 2) * ((K.toHistory.event j).incoming.flow.base.metric t).inner y ξ ξ

/-- **inhabitant（`_C11PK`）**：`Rad = 0` 时球空，粗 footprint 平凡成立。 -/
theorem pickedBallFootprint_zero_C11PK (β : ℝ) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w O : (K.stage j.castSucc).Carrier) (D : ℝ≥0∞) :
    PickedBallFootprint_C11PK β 0 K j v w O D := by
  intro x hx
  simp [riemannianBallOf] at hx

/-- **inhabitant（`_C11PK`）**：`Rad = 0` 时球空，端点 Ricci binder 平凡成立。 -/
theorem pickedBallEndpointRicci_zero_C11PK (ℓ β : ℝ) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w O : (K.stage j.castSucc).Carrier) :
    PickedBallEndpointRicci_C11PK ℓ β 0 K j v w O := by
  intro x hx
  simp [riemannianBallOf] at hx

end Defs

section G1

/-- **G1（`_C11PK`，PROVED）：hκ ⇐ FRESH supply + original seed prefix + 粗 footprint**。
`τ ∈ [v − β/q, v] ∩ slab j`：`aSeed = Tn − r² ≤ Tn − r²/2 ≤ τ ≤ v ≤ Tn`；`activeStage τ = j⁻`
（`activeStage_eq_castSucc_C11PB`）把 slab 形 footprint 搬到 supply 的 `B_τ(O_τ, A·r)`；`b ≤ ρ < r/100`。
结论 = `PickedBallKappa_C11PB` 逐字。不经 Pre841 / hdist。 -/
theorem pickedBallKappa_of_fresh_C11PK {nr : ℝ → ℝ} {A κ T : ℝ} (K : RetainedCoreHistory.{u})
    (hW : KappaSeedWindowFwd_C11PK nr A κ T K.toHistory)
    {Tn aSeed : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn)
    {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ} (hTn : T ≤ (Tn : ℝ))
    (htime : 2 * r ^ 2 < (Tn : ℝ))
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (K.toHistory.stageMetric (K.toHistory.activeStage Tn) Tn) pT r)
    (hnr : ∀ w : ℝ, (Tn : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn : ℝ) → nr w ≤ r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (j : Fin K.eventCount) (v : ℝ) (w : (K.stage j.castSucc).Carrier) {β Rad ρ : ℝ}
    (ha : (Tn : ℝ) - r ^ 2 / 2 ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (ht : v ≤ (Tn : ℝ))
    (h1 : K.toHistory.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ K.toHistory.activeStage Tn)
    (hfoot : PickedBallFootprint_C11PK β Rad K j v w (seedTrace.point j.castSucc h1 h2)
      (ENNReal.ofReal (A * r)))
    (hρ : ρ < r / 100) (hκ : 0 ≤ κ) :
    PickedBallKappa_C11PB β Rad ρ κ K j v w := by
  intro τ hτ1 hτ2 hτ3 hτ4 z hz zz hzz b hb hbρ hball
  have hr2 := sq_nonneg r
  have hav : aSeed ≤ τ := by
    change (aSeed : ℝ) ≤ (τ : ℝ)
    rw [hclock]
    linarith
  have hvt : τ ≤ Tn := by
    change (τ : ℝ) ≤ (Tn : ℝ)
    linarith
  have hact := K.activeStage_eq_castSucc_C11PB j τ hτ3 hτ4
  have key : ∀ (k : Fin (K.toHistory.eventCount + 1)) (_hk : K.toHistory.activeStage τ = k)
      (h1' : K.toHistory.activeStage aSeed ≤ k) (h2' : k ≤ K.toHistory.activeStage Tn)
      (z' : (K.toHistory.stage k).Carrier), HEq zz z' →
      riemannianEDistOf (K.toHistory.stageMetric k τ) (seedTrace.point k h1' h2') z' <
        ENNReal.ofReal (A * r) →
      zz ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
        (seedTrace.point (K.toHistory.activeStage τ) (K.toHistory.activeStage_mono hav)
          (K.toHistory.activeStage_mono hvt)) (A * r) := by
    intro k hk
    subst hk
    intro h1' h2' z' hzz' hd'
    rw [eq_of_heq hzz']
    exact hd'
  have hd' : riemannianEDistOf (K.toHistory.stageMetric j.castSucc τ)
      (seedTrace.point j.castSucc h1 h2) z < ENNReal.ofReal (A * r) := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hfoot z hz τ hτ1 hτ2 hτ3
  have hx := key j.castSucc hact h1 h2 z hzz hd'
  have h := hW Tn pT r hTn htime hsmall hvol hnr aSeed haT hclock seedTrace τ hav hvt
    (by linarith) zz hx b hb.le (by linarith) hball
  rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **粗 footprint ⇐ 中心 + 短窗 I.8.3(b) 距离畸变（`_C11PK`，PROVED；binder = 端点 Ricci）**：
`d_τ(O, z) ≤ d_v(O, z) + (8/ℓ)(v − τ)`（`smooth_distance_distortion_C11D`，stage `j⁻`，
`[τ, v]` 在 slab 内）、
`d_v(O, z) ≤ d_v(O, w) + Rad/√q`、`v − τ ≤ β/q`。 -/
theorem pickedBallFootprint_of_distortion_C11PK (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) {v : ℝ} (hvj : v < K.time j.succ)
    {w O : (K.stage j.castSucc).Carrier} {β Rad ℓ : ℝ} {D₀ D : ℝ≥0∞} (hℓ : 0 < ℓ)
    (hw : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) O w ≤ D₀)
    (hRic : PickedBallEndpointRicci_C11PK ℓ β Rad K j v w O)
    (hD : D₀ + ENNReal.ofReal (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)) +
      ENNReal.ofReal (8 * β / (ℓ * (K.toHistory.event j).incoming.flow.scalar v w)) < D) :
    PickedBallFootprint_C11PK β Rad K j v w O D := by
  intro z hz τ hτ1 hτ2 hτ3
  have hnext : ∀ e : Fin K.toHistory.eventCount, j.castSucc = e.castSucc →
      v < K.toHistory.time e.succ := by
    intro e he
    obtain rfl := Fin.castSucc_injective _ he
    exact hvj
  have hhor : v ≤ K.toHistory.horizon := hvj.le.trans (K.toHistory.time_le_horizon_at _)
  have hRic' : ∀ t ∈ Ioo τ v, ∀ y : (K.toHistory.stage j.castSucc).Carrier,
      ∀ ξ : TangentSpace ThreeModel y,
      (riemannianEDistOf (K.toHistory.stageMetric j.castSucc t) O y < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (K.toHistory.stageMetric j.castSucc t) z y < ENNReal.ofReal ℓ) →
      ricciTensor (K.toHistory.stageMetric j.castSucc t) y ξ ξ ≤
        (3 / ℓ ^ 2) * (K.toHistory.stageMetric j.castSucc t).inner y ξ ξ := by
    intro t ht y ξ hy
    rw [ObservedHistory.stageMetric_castSucc_apply] at hy ⊢
    exact hRic z hz t (lt_of_le_of_lt hτ1 ht.1) ht.2 (lt_trans hτ3 ht.1) y ξ hy
  have hdist := ObservedHistory.smooth_distance_distortion_C11D K.toHistory j.castSucc hℓ hτ2
    hτ3.le hnext hhor O z hRic'
  rw [ObservedHistory.stageMetric_castSucc_apply,
    ObservedHistory.stageMetric_castSucc_apply] at hdist
  have htri : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) O z ≤
      D₀ + ENNReal.ofReal (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)) :=
    (riemannianEDistOf_triangle _ O w z).trans (add_le_add hw hz.le)
  have hlen : ENNReal.ofReal (8 / ℓ * (v - τ)) ≤
      ENNReal.ofReal (8 * β / (ℓ * (K.toHistory.event j).incoming.flow.scalar v w)) := by
    apply ENNReal.ofReal_le_ofReal
    have hvτ : v - τ ≤ β / (K.toHistory.event j).incoming.flow.scalar v w := by linarith
    calc 8 / ℓ * (v - τ) ≤ 8 / ℓ * (β / (K.toHistory.event j).incoming.flow.scalar v w) :=
          mul_le_mul_of_nonneg_left hvτ (by positivity)
      _ = 8 * β / (ℓ * (K.toHistory.event j).incoming.flow.scalar v w) := by ring
  exact lt_of_le_of_lt (hdist.trans (add_le_add htri hlen)) hD

/-- **组合（`_C11PK`，PROVED；唯一 binder = 端点 Ricci）**：top gate `hdσ`（J11 / PICKBALL G5 /
`regionalKappa_of_closure_P6L3` 的 `hdσ` **同一陈述**，`Aκ := A`）+ 中心 Good(L/2) `hw`（`hκPB` 自带）+
`PickedBallEndpointRicci_C11PK (ℓ₀/√q)` + `2(max Rad 0 + 8β/ℓ₀) ≤ L` ⇒ 粗 footprint `A·r` ⇒ G1。
算术：`L/(2√R_n) + Rad/√q + 8β/(ℓ₀√q) ≤ (L/2 + max Rad 0 + 8β/ℓ₀)/√R_n < (L + 1)/√R_n`（`R_n ≤ q`）。 -/
theorem pickedBallKappa_of_fresh_distortion_C11PK {nr : ℝ → ℝ} {A κ T : ℝ}
    (K : RetainedCoreHistory.{u}) (hW : KappaSeedWindowFwd_C11PK nr A κ T K.toHistory)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ} (hTn : T ≤ (Tn : ℝ))
    (htime : 2 * r ^ 2 < (Tn : ℝ))
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (K.toHistory.stageMetric (K.toHistory.activeStage Tn) Tn) pT r)
    (hnr : ∀ w : ℝ, (Tn : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn : ℝ) → nr w ≤ r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (y : (K.toHistory.stageAt σ).Carrier) {Rn L ℓ₀ : ℝ} (hRn : 0 < Rn) (hℓ₀ : 0 < ℓ₀)
    (hdσ : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal ((L + 1) / Real.sqrt Rn) ≤ ENNReal.ofReal (A * r))
    (j : Fin K.eventCount) (v : ℝ) (w : (K.stage j.castSucc).Carrier) {β Rad ρ : ℝ}
    (hβ : 0 ≤ β) (hLR : 2 * (max Rad 0 + 8 * β / ℓ₀) ≤ L)
    (hRw : Rn ≤ (K.toHistory.event j).incoming.flow.scalar v w) (hvj : v < K.time j.succ)
    (ha : (Tn : ℝ) - r ^ 2 / 2 ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (ht : v ≤ (Tn : ℝ))
    (h1 : K.toHistory.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ K.toHistory.activeStage Tn)
    (hw : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) w ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / 2 / Real.sqrt Rn))
    (hRic : PickedBallEndpointRicci_C11PK
      (ℓ₀ / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)) β Rad K j v w
      (seedTrace.point j.castSucc h1 h2))
    (hρ : ρ < r / 100) (hκ : 0 ≤ κ) :
    PickedBallKappa_C11PB β Rad ρ κ K j v w := by
  set dσ := riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
    (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
      (K.toHistory.activeStage_mono hsT)) y with hdσdef
  set q := (K.toHistory.event j).incoming.flow.scalar v w with hqdef
  have hq : 0 < q := hRn.trans_le hRw
  have hs : 0 < Real.sqrt Rn := Real.sqrt_pos.2 hRn
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsle : Real.sqrt Rn ≤ Real.sqrt q := Real.sqrt_le_sqrt hRw
  have hm0 : 0 ≤ max Rad 0 := le_max_right _ _
  have h8β : 0 ≤ 8 * β := mul_nonneg (by norm_num) hβ
  have hc0 : 0 ≤ 8 * β / ℓ₀ := div_nonneg h8β hℓ₀.le
  have hL0 : 0 ≤ L := by linarith
  have hb : Rad / Real.sqrt q ≤ max Rad 0 / Real.sqrt Rn :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hsq.le).trans
      (div_le_div_of_nonneg_left hm0 hs hsle)
  have hlq : ℓ₀ / Real.sqrt q * q = ℓ₀ * Real.sqrt q := by
    have hsqq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
    calc ℓ₀ / Real.sqrt q * q = ℓ₀ / Real.sqrt q * (Real.sqrt q * Real.sqrt q) := by rw [hsqq]
      _ = ℓ₀ * Real.sqrt q := by rw [← mul_assoc, div_mul_cancel₀ ℓ₀ hsq.ne']
  have hc : 8 * β / (ℓ₀ / Real.sqrt q * q) ≤ 8 * β / (ℓ₀ * Real.sqrt Rn) := by
    rw [hlq]
    exact div_le_div_of_nonneg_left h8β (mul_pos hℓ₀ hs) (mul_le_mul_of_nonneg_left hsle hℓ₀.le)
  have ha0 : 0 ≤ L / 2 / Real.sqrt Rn := div_nonneg (div_nonneg hL0 (by norm_num)) hs.le
  have hb0 : 0 ≤ max Rad 0 / Real.sqrt Rn := div_nonneg hm0 hs.le
  have hc0' : 0 ≤ 8 * β / (ℓ₀ * Real.sqrt Rn) := div_nonneg h8β (mul_pos hℓ₀ hs).le
  have hsum : L / 2 / Real.sqrt Rn + (max Rad 0 / Real.sqrt Rn + 8 * β / (ℓ₀ * Real.sqrt Rn)) =
      (L / 2 + max Rad 0 + 8 * β / ℓ₀) / Real.sqrt Rn := by
    ring
  have hX : (L / 2 + max Rad 0 + 8 * β / ℓ₀) / Real.sqrt Rn < (L + 1) / Real.sqrt Rn :=
    div_lt_div_of_pos_right (by linarith) hs
  have hfin : dσ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hdσ)
  have hsplit : ENNReal.ofReal (L / 2 / Real.sqrt Rn) + (ENNReal.ofReal (Rad / Real.sqrt q) +
      ENNReal.ofReal (8 * β / (ℓ₀ / Real.sqrt q * q))) ≤
      ENNReal.ofReal ((L / 2 + max Rad 0 + 8 * β / ℓ₀) / Real.sqrt Rn) := by
    rw [← hsum, ENNReal.ofReal_add ha0 (add_nonneg hb0 hc0'), ENNReal.ofReal_add hb0 hc0']
    exact add_le_add le_rfl (add_le_add (ENNReal.ofReal_le_ofReal hb) (ENNReal.ofReal_le_ofReal hc))
  have hgate : dσ + ENNReal.ofReal (L / 2 / Real.sqrt Rn) + ENNReal.ofReal (Rad / Real.sqrt q) +
      ENNReal.ofReal (8 * β / (ℓ₀ / Real.sqrt q * q)) < ENNReal.ofReal (A * r) := by
    calc dσ + ENNReal.ofReal (L / 2 / Real.sqrt Rn) + ENNReal.ofReal (Rad / Real.sqrt q) +
          ENNReal.ofReal (8 * β / (ℓ₀ / Real.sqrt q * q))
        = dσ + (ENNReal.ofReal (L / 2 / Real.sqrt Rn) + (ENNReal.ofReal (Rad / Real.sqrt q) +
          ENNReal.ofReal (8 * β / (ℓ₀ / Real.sqrt q * q)))) := by simp only [add_assoc]
      _ ≤ dσ + ENNReal.ofReal ((L / 2 + max Rad 0 + 8 * β / ℓ₀) / Real.sqrt Rn) :=
          add_le_add le_rfl hsplit
      _ < dσ + ENNReal.ofReal ((L + 1) / Real.sqrt Rn) :=
          ENNReal.add_lt_add_left hfin
            ((ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) hs)).2 hX)
      _ ≤ ENNReal.ofReal (A * r) := hdσ
  exact pickedBallKappa_of_fresh_C11PK K hW haT hTn htime hsmall hvol hnr hclock seedTrace j v w
    ha ht h1 h2 (pickedBallFootprint_of_distortion_C11PK K j hvj (div_pos hℓ₀ hsq) hw hRic hgate)
    hρ hκ

end G1

section G2

/-- **G2（`_C11PK`，PROVISIONAL：binder 族 `hRicPB` = 端点 Ricci，owner DIST / PICKBALL）**：结论 =
G4 `ObservedHistory.shallowSliceRC_of_pickedBall_seed_C11PB` 的 `hκPB` **逐字**（直接作该参数）。输入：FRESH
supply `hWK`（`kappaSeedWindowFwd_of_retention_C11PK` 产出）+ selection 的 original seed prefix
（`hclock / htimeS / hsmallS / hvolS / hnrS`，与 J11 同一 prefix）+ `hTκ` + `hwinF`（J11 同式）+ `hρr`
（`ρV < r/100`）+ top gate `hdσ`（J11 / G5 同一陈述，eventually 形）+ `hRicPB`（量词前缀同 `hκPB`）。
时间域：`v − θ₀/q ≥ σ + σ₁/R_n − θ₀/R_n ≥ Tn − r²/2`，`v ≤ σ + σ₂/R_n < σ ≤ Tn`；
`L ≥ 2(max Rad 0 + 8θ₀/ℓ₀)`
eventually。不经 Pre841 / hdist / hseedAll。 -/
theorem hκPB_of_fresh_C11PK {θ₀ : ℝ} (hθ₀ : 0 < θ₀) {κ : ℝ} (hκ : 0 ≤ κ) {nr : ℝ → ℝ}
    {A Tκ ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {K : ℕ → RetainedCoreHistory.{u}}
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr A κ Tκ (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier) (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (ρV : ℕ → ℝ) (r : ℕ → ℝ)
    (hTκ : ∀ᶠ n in atTop, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hvolS : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r n ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r n)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hρr : ∀ᶠ n in atTop, ρV n < r n / 100)
    (hdσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (A * r n))
    (hRicPB : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (K n).toHistory.eventCount) (v : ℝ), (K n).toHistory.time j'.castSucc < v →
        v < (K n).toHistory.time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage
            (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (w :
            ((K n).toHistory.stage j'.castSucc).Carrier),
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((K n).toHistory.event j').incoming.flow.scalar v w →
          PickedBallEndpointRicci_C11PK
            (ℓ₀ / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)) θ₀ Rad (K n)
            j' v w ((seedTrace n).point j'.castSucc h1 h2)) :
    ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (K n).toHistory.eventCount) (v : ℝ), (K n).toHistory.time j'.castSucc < v →
        v < (K n).toHistory.time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage
            (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (w :
            ((K n).toHistory.stage j'.castSucc).Carrier),
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((K n).toHistory.event j').incoming.flow.scalar v w →
          PickedBallKappa_C11PB θ₀ Rad (ρV n) κ (K n) j' v w := by
  intro Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
  have hθσ : 0 < θ₀ - σ₁ := by linarith
  filter_upwards [hRicPB Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr,
    hφ.tendsto_atTop hTκ, hφ.tendsto_atTop (hwinF (θ₀ - σ₁) hθσ), hφ.tendsto_atTop hρr,
    hφ.tendsto_atTop hdσ,
    hφ.tendsto_atTop (hL.eventually_ge_atTop (2 * (max Rad 0 + 8 * θ₀ / ℓ₀)))]
    with n hRic hTn hwn hρn hdn hLn
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hw hzw hRw
  have hRn := hRpos n
  have hθq : θ₀ / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ θ₀ / R n :=
    div_le_div_of_nonneg_left hθ₀.le hRn hRw
  have hσR : (θ₀ - σ₁) / R n = θ₀ / R n - σ₁ / R n := sub_div _ _ _
  have hσ2R : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
  have hσT : (σ n : ℝ) ≤ (Tn n : ℝ) := hsT n
  exact pickedBallKappa_of_fresh_distortion_C11PK (K n) (hWK n) (haT n) (hsT n) (has n) hTn
    (htimeS n) (hsmallS n) (hvolS n) (hnrS n) (hclock n) (seedTrace n) (y n) hRn hℓ₀ hdn j' v w
    hθ₀.le hLn hRw hv2 (by linarith) (by linarith) h1 h2 hw
    (hRic j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hw hzw hRw) hρn hκ

end G2

section G2consumer

/-- **G2 consumer（`_C11PK`，PROVISIONAL：binder 族 `hseedPB`（SEEDCL）/ `hRicPB`（DIST / PICKBALL））**：
SHALLOW T1 = G4 `shallowSliceRC_of_pickedBall_seed_C11PB`，其 `hκPB` 由 `hκPB_of_fresh_C11PK` 供给
（FRESH supply + original seed prefix + `hwinF` + `hρr` + top gate `hdσ` + 端点 Ricci）。 -/
theorem ObservedHistory.shallowSliceRC_of_pickedBall_fresh_C11PK
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L ε C1 C2 Ctg)
    (hC2 : C2 ≤ (Cgrad : ℝ))
    (hseedPB : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (K n).toHistory.eventCount) (v : ℝ), (K n).toHistory.time j'.castSucc < v →
        v < (K n).toHistory.time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage
            (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (w :
            ((K n).toHistory.stage j'.castSucc).Carrier),
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((K n).toHistory.event j').incoming.flow.scalar v w →
          PickedBallWindowSeed_C11PB θ₀ Rad (Cg * R n) (K n) j' v w
            ((seedTrace n).point j'.castSucc h1 h2)
            (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n)) ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))))
    {nr : ℝ → ℝ} {A Tκ ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr A κ Tκ (K n).toHistory) (r : ℕ → ℝ)
    (hTκ : ∀ᶠ n in atTop, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hvolS : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r n ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r n)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hρr : ∀ᶠ n in atTop, ρV n < r n / 100)
    (hdσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (A * r n))
    (hRicPB : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (K n).toHistory.eventCount) (v : ℝ), (K n).toHistory.time j'.castSucc < v →
        v < (K n).toHistory.time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage
            (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (w :
            ((K n).toHistory.stage j'.castSucc).Carrier),
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((K n).toHistory.event j').incoming.flow.scalar v w →
          PickedBallEndpointRicci_C11PK
            (ℓ₀ / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)) θ₀ Rad (K n)
            j' v w ((seedTrace n).point j'.castSucc h1 h2)) :
    ObservedHistory.ShallowSliceRC_C11SH η₃ Lc (fun n => (K n).toHistory) σ y R :=
  ObservedHistory.shallowSliceRC_of_pickedBall_seed_C11PB hθ₀ hθ₀2 hεle hκ hphi hCg hη₃ hLc htj
    recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK σ y R hσ hRpos hqR hT₀
    Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV hdistQC hgood hC2 hseedPB
    (hκPB_of_fresh_C11PK hθ₀ hκ.le hℓ₀ hWK σ y R hRpos Tn aSeed haT hsT has pT seedTrace L hL ρV
      r hTκ htimeS hsmallS hvolS hnrS hclock hwinF hρr hdσ hRicPB)

end G2consumer

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow

universe u

/-- **FRESH supply producer（`_C11PK`，PROVED）**：`nonempty_pre841Data_of_retention_fwd_C11FR` 的
retention 前提（`N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU hA hP3 hprof hacc₀`，逐字）⇒
`∃ κ > 0, ∃ T > 0, ∀ n, KappaSeedWindowFwd_C11PK (nr(4·/3)) A κ T (F.tower.history n)`。证明 = 该定理的 κ 段
（K5 前向 → wide 前向 → hsmall 前向 + P6B window → window-zero glue），**去掉** Pre841 构造与其 `hdist / hradii /
hwin / hratio` 及 seed 序列。 -/
theorem kappaSeedWindowFwd_of_retention_C11PK {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ) (hrad : ∀ m, 0 < rad m)
    (hnr1 : ∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1)
    (hev : ∀ n (j : Fin (F.tower.history n).toHistory.eventCount), ∃ m : ℕ,
      preparedSpatialHorizon m < (F.tower.history n).toHistory.time j.succ ∧
      (F.tower.history n).toHistory.time j.succ ≤ (3 : ℝ) ^ m ∧
      N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤ cap m ∧
      (∀ T ∈ Icc ((F.tower.history n).toHistory.time j.succ)
          (2 * (F.tower.history n).toHistory.time j.succ),
        rad (m + 1) ≤ N.params.neckRadius T) ∧
      (∀ A : ℝ, 0 < A → N.params.delta ((F.tower.history n).toHistory.time j.succ) <
        diagonalAccuracy_C11S N.params.delta A ((F.tower.history n).toHistory.time j.succ) →
        A < 12 * (3 : ℝ) ^ m) ∧
      ∀ b', ∃ raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap N.params.fixed
          (Df m) (mf m) (εf m) b',
        raw.hasCanonicalWindow ∧ raw.neck.scale = ((N.records n j).static b').neck.scale ∧
        ∀ z, raw.inclusion (raw.witness.cap z) =
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z))
    (hdomK3 : ∀ m : ℕ,
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ Df m ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤ mf m ∧
      εf m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤
        Df (m + 1) ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤
        mf (m + 1) ∧
      εf (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1)
    (hdomE : ∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    (hdomU : ∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    {A : ℝ} (hA : 0 < A) (hP3 : CollarWindowSupply_C11E.{u} N.params)
    (hprof : ModelConstraintsSupply_C11E N.params εProf_C11E.{u})
    (hacc₀ : N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ T : ℝ, 0 < T ∧ ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => N.params.neckRadius (4 * w / 3)) A κ T
        (F.tower.history n).toHistory := by
  obtain ⟨v, hK5⟩ :=
    seedReducedVolumeFwd_of_retention_C11FR N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU
  have hloc : LocalKappaSupply_P6B F N.params.delta (diagonalAccuracy_C11S N.params.delta)
      N.params.neckRadius :=
    localKappaP6B_of_reducedVolumeScaled_C11Q4 (seedReducedVolumeScaled_of_fwd_C11FR hK5)
  obtain ⟨κ', hκ', hsmallSeed⟩ :=
    (hsmallSeedFwd_of_wideFwdSupply_C11FR.{u} N.epsilon N.C1 N.C2 P).choose_spec.2 hA hP3 hprof
      hacc₀ N.records N.canonical_windows N.delta_antitone N.radius_antitone N.canonical
      (localKappaWideFwd_of_reducedVolumeFwd_C11FR hK5)
  obtain ⟨κ₁, hκ₁, hW₁⟩ := localKappaWindow_of_late_P6B
    (localKappaLateSupply_of_envelope_P6B
      (largerBallAccuracySupply_diagonal_C11S N.params N.delta_antitone) hloc) A hA
  obtain ⟨T, hT, hK⟩ := localKappaWindow_zero_of_window_and_smallFwd_C11FR hW₁ hsmallSeed
  exact ⟨min κ₁ κ', lt_min hκ₁ hκ', T, hT, fun n => hK n⟩

end GC.LongTime.Ch11
