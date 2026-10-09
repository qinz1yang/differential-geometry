import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallSeedC11PB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HUVKappaClosure_P6L3

/-!
# hκ ⇐ 区域 κ `hκR` + 窗口 seed closure；SHALLOW T1 的新缺项只剩 hseedAll（O-CH11-PICKBALL G5，`_C11PB`）

`regionalKappa_of_closure_P6L3`（树内，KAPPA3 D-8 形区域 κ `hκR` + seed closure ⇒ 区域内 controlled ball 的 κ）
把 G1 的 hκ 化成 **同一个** 窗口 seed closure（不带曲率阈值）+ 既有的区域 κ binder `hκR`（owner CXSK /
`regionalKappa_of_seedWindow_center_CXSK`）+ selection 的 `hroom` / `hdistσ`（`P6HUVCondCgP6S3` 同款）。
* `PickedBallWindowSeedAll_C11PB β Rad K j v w O D`（**hseedAll**，PROVISIONAL）：`x ∈ B_v(w, Rad/√q)`、
  `τ ∈ [v − β/q, v]`、`time j⁻ < τ` ⇒ `d_τ(O, x) ≤ D`。**诚实标注**：这正是 `hUVC_of_selection_Cg_P6S3` 的
  `hclosC` 前提的内层命题在**固定短窗** `B := β = θ₀` 处的实例；deny-list 针对的是 `hclosC` 的既有（M4，经
  hclosG ← hscalU）生产者，本合同**要求独立生产者**（first-exit + G1 `PickedBallSurvivalOrCap` 的 Rm 界，
  owner SHALLOW-TOOLS M1 / DIST），不得接回 M4 链。`.toWindowSeed`：⇒ G4 的 hseed（任意阈值）。
* `pickedBallKappa_of_regional_C11PB`（PROVED）：`hκR` + `hdσ` + 时间域 + hseedAll ⇒
  `PickedBallKappa_C11PB`。
* `ObservedHistory.shallowSliceRC_of_pickedBall_kappa_C11PB`（consumer，PROVISIONAL）：SHALLOW T1 ⇐
  `ksw_C11KS2` + KSW consumer 其余前提 + hgood + `hC2` + `hroom` / `hdistσ` / `hκR`（P6S3 逐字形）
  + **唯一新 binder 族 `hallPB`**（hseedAll，量词前缀同 `hUVC`）。
非循环：import G4 与 `HUVKappaClosure_P6L3`（tracked）；不经 hscalU / hclosG / hclosC 生产者 / hUVC 生产者 /
CanonicalLateCore / hspine（审计名字扫描）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **hseedAll（`_C11PB`，PROVISIONAL binder）**：窗口 seed closure（无曲率阈值）。`x ∈ B_v(w, Rad/√q)`
（`q = R(v, w)`）、`τ ∈ [v − β/q, v]`、`time j⁻ < τ` ⇒ `d_τ(O, x) ≤ D`（`K.event j` incoming metric）。
= `hUVC_of_selection_Cg_P6S3` 的 `hclosC` 内层在固定短窗 `B := β` 的实例；需**独立**生产者（见模块注释）。 -/
def PickedBallWindowSeedAll_C11PB (β Rad : ℝ) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w O : (K.stage j.castSucc).Carrier) (D : ℝ≥0∞) : Prop :=
  ∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
    ∀ τ : ℝ, v - β / (K.toHistory.event j).incoming.flow.scalar v w ≤ τ → τ ≤ v →
      K.time j.castSucc < τ →
      riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric τ) O x ≤ D

/-- **inhabitant（`_C11PB`）**：`Rad = 0` 时球空，hseedAll 平凡成立。 -/
theorem pickedBallWindowSeedAll_zero_C11PB (β : ℝ) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w O : (K.stage j.castSucc).Carrier) (D : ℝ≥0∞) :
    PickedBallWindowSeedAll_C11PB β 0 K j v w O D := by
  intro x hx
  simp [riemannianBallOf] at hx

/-- **hseedAll ⇒ hseed（`_C11PB`）**：无阈值的窗口 closure 蕴含 G4 带阈值的 `PickedBallWindowSeed_C11PB`
（`v′ ∈ (time j⁻, v)` ⊂ 闭窗）。 -/
theorem PickedBallWindowSeedAll_C11PB.toWindowSeed {β Rad qthr : ℝ} {K : RetainedCoreHistory.{u}}
    {j : Fin K.eventCount} {v : ℝ} {w O : (K.stage j.castSucc).Carrier} {D : ℝ≥0∞}
    (h : PickedBallWindowSeedAll_C11PB β Rad K j v w O D) :
    PickedBallWindowSeed_C11PB β Rad qthr K j v w O D :=
  fun x hx v' hv' hβ _ => h x hx v' hβ hv'.2.le hv'.1

/-- **hκ ⇐ 区域 κ + hseedAll（`_C11PB`，PROVED）**：`regionalKappa_of_closure_P6L3`（`H := K.toHistory`、
`U := B_v(w, Rad/√q)`、`a := v − β/q`、`t := v`）。前提 `hκR` / `hdσ` 逐字取自该定理。 -/
theorem pickedBallKappa_of_regional_C11PB (K : RetainedCoreHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (y : (K.toHistory.stageAt σ).Carrier) {R L r ρ κ Aκ : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hκR : ∀ (j : Fin K.toHistory.eventCount) (c : (K.toHistory.stage j.castSucc).Carrier)
      (U : Set (K.toHistory.stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn : ℝ) - r ^ 2 / 2 ≤ a → t ≤ (Tn : ℝ) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        K.toHistory.time j.castSucc < τ → (τ : ℝ) < K.toHistory.time j.succ →
        ∀ z ∈ U, ∀ zz cc : (K.toHistory.stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        K.toHistory.time j.castSucc < τ → (τ : ℝ) < K.toHistory.time j.succ →
        ∀ (hav : aSeed ≤ τ) (hvt : τ ≤ Tn), ∀ cc : (K.toHistory.stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (seedTrace.point (K.toHistory.activeStage τ) (K.toHistory.activeStage_mono hav)
                (K.toHistory.activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r)) →
      ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        K.toHistory.time j.castSucc < τ → (τ : ℝ) < K.toHistory.time j.succ →
        ∀ z ∈ U, ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
              (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b))
    (hdσ : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal ((L + 1) / Real.sqrt R) ≤ ENNReal.ofReal (Aκ * r))
    (j : Fin K.eventCount) (v : ℝ) (w : (K.stage j.castSucc).Carrier) {β Rad : ℝ}
    (ha : (Tn : ℝ) - r ^ 2 / 2 ≤ v - β / (K.toHistory.event j).incoming.flow.scalar v w)
    (ht : v ≤ (Tn : ℝ))
    (h1 : K.toHistory.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ K.toHistory.activeStage Tn)
    (hall : PickedBallWindowSeedAll_C11PB β Rad K j v w (seedTrace.point j.castSucc h1 h2)
      (riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R))) :
    PickedBallKappa_C11PB β Rad ρ κ K j v w :=
  regionalKappa_of_closure_P6L3 K.toHistory haT hsT has seedTrace y hR hL hκR hdσ j _ _ v ha ht h1
    h2 (fun τ haτ hτv hτ1 _ x hx => hall x hx τ haτ hτv hτ1)

/-- **SHALLOW T1 ⇐ hgood + 区域 κ + 唯一 binder hseedAll（`_C11PB`，PROVISIONAL：binder `hallPB`）**：G4 的
`shallowSliceRC_of_pickedBall_seed_C11PB`，`hseedPB := hallPB.toWindowSeed`，`hκPB` 由
`pickedBallKappa_of_regional_C11PB`（`hroom` + 时间域：`Tn − r²/2 ≤ σ − L²/R_n ≤ v − θ₀/R(v,w)`；
`v ≤ σ ≤ Tn`）。 -/
theorem ObservedHistory.shallowSliceRC_of_pickedBall_kappa_C11PB
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
    (hallPB : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
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
          PickedBallWindowSeedAll_C11PB θ₀ Rad (K n) j' v w
            ((seedTrace n).point j'.castSucc h1 h2)
            (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n)) ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))))
    {r : ℕ → ℝ} {Aκ : ℝ}
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (K n).toHistory.eventCount) (c :
        ((K n).toHistory.stage j.castSucc).Carrier)
      (U : Set ((K n).toHistory.stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time j.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((K n).toHistory.stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time j.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc :
            ((K n).toHistory.stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
              ((seedTrace n).point ((K n).toHistory.activeStage τ)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time j.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j.succ →
        ∀ z ∈ U, ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
              (riemannianBallOf ((K n).toHistory.stageMetric
                  ((K n).toHistory.activeStage τ) τ) zz b)) :
    ObservedHistory.ShallowSliceRC_C11SH η₃ Lc (fun n => (K n).toHistory) σ y R := by
  refine ObservedHistory.shallowSliceRC_of_pickedBall_seed_C11PB hθ₀ hθ₀2 hεle hκ hphi hCg hη₃ hLc
    htj recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK σ y R hσ hRpos hqR hT₀
    Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV hdistQC hgood hC2 ?_ ?_
  · intro Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
    filter_upwards [hallPB Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr] with n hs
    intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hw hzw hRw
    exact (hs j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hw hzw hRw).toWindowSeed
  · intro Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
    have hθσ : 0 < θ₀ - σ₁ := by linarith
    filter_upwards [hallPB Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr,
      hφ.tendsto_atTop (hL.eventually_ge_atTop (max 1 (θ₀ - σ₁))),
      hφ.tendsto_atTop hκR, hφ.tendsto_atTop hdistσ] with n hs hLn hκn hdσ
    intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hw hzw hRw
    have hRn := hRpos n
    have hL1 : 1 ≤ L n := (le_max_left _ _).trans hLn
    have hLσ : θ₀ - σ₁ ≤ L n := (le_max_right _ _).trans hLn
    have hθq : θ₀ / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ θ₀ / R n :=
      div_le_div_of_nonneg_left hθ₀.le hRn hRw
    have hσR : σ₁ / R n - θ₀ / R n = -((θ₀ - σ₁) / R n) := by ring
    have hσ2R : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    have hLsq : (θ₀ - σ₁) / R n ≤ L n ^ 2 / R n :=
      div_le_div_of_nonneg_right (by nlinarith) hRn.le
    have hroomn := hroom n
    have hvT : v ≤ (Tn n : ℝ) := by
      have : (σ n : ℝ) ≤ Tn n := hsT n
      linarith
    exact pickedBallKappa_of_regional_C11PB (K n) (haT n) (hsT n) (has n) (seedTrace n) (y n) hRn
      (by linarith) hκn hdσ j' v w (by linarith) hvT h1 h2
      (hs j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hw hzw hRw)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
