import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallFixedC11PB

/-!
# hgrad ⇐ hgood + 窗口 seed closure（O-CH11-PICKBALL G4，后缀 `_C11PB`）

`SpatialCanonicalWitness` 自带 `gradient` 字段（`|dR| ≤ C2 R^{3/2}`），故 hUside 的梯度半
`PickedBallGrad_C11PB` 不需要独立的 canonical 梯度估计：只要窗口 `[v − β/q, v)` 上球点处 selection 的
`HgoodCg_C11SH` 可用，即球点在那些时刻的 **seed-distance closure**。本文件把它登记成精确的 binder：
* `PickedBallWindowSeed_C11PB β Rad qthr K j v w O D`（**hseed**，PROVISIONAL）：`B_v(w, Rad/√q)` 的点
  `x`、`v′ ∈ (time j⁻, v)`、`v − β/q ≤ v′`、`R(v′, x) > qthr` ⇒ `d_{v′}(O, x) ≤ D`
  （`O` = seed 点，`D = dσ + L/√R_n`）。
  这就是 first-exit closure 的窗口形；owner = SHALLOW-TOOLS M1 / DIST（输入 = G1 `SurvivalOrCap` 的 Rm 界，
  距离畸变 `e^{C Λ β}`；不得走 `hscalU` / M4 循环路线）。
* `pickedBallGrad_of_hgood_C11PB`（PROVED）：hgood + hseed + 时间域 + `C2 ≤ Cgrad` ⇒
  `PickedBallGrad_C11PB`。
* `ObservedHistory.shallowSliceRC_of_pickedBall_seed_C11PB`（consumer，PROVISIONAL）：G3 的 SHALLOW T1
  定理，`hgradPB` 换成 `hseedPB`（同一量词前缀）+ `hC2`；时间域 `aSeed ≤ v − θ₀/R(v,w)`
  （`hwin (θ₀ − σ₁)`）、`σ − L²/R_n ≤ v − θ₀/R(v,w)`（`L ≥ max 1 (θ₀ − σ₁)`）eventually。
  T1 的 U 侧 binder 只剩 **hseed + hκ**。
非循环：只 import G3（→ G1–G2、KSW2 G4）；不经 hscalU / hclosG / hclosC / hUVC 生产者 / CanonicalLateCore /
hspine。
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

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **hseed（`_C11PB`，PROVISIONAL binder）**：窗口 seed-distance closure。球 `B_v(w, Rad/√q)`
（`q = R(v, w)`）的点 `x` 在 `v′ ∈ (time j⁻, v)`、`v − β/q ≤ v′`、`R(v′, x) > qthr` 时 `d_{v′}(O, x) ≤ D`
（`K.event j` incoming metric；`O` 为 seed 点在 stage `j⁻` 的位置）。owner = SHALLOW-TOOLS M1 / DIST
（first-exit，输入 = G1 `PickedBallSurvivalOrCap` 的整球存活与 Rm 界）。 -/
def PickedBallWindowSeed_C11PB (β Rad qthr : ℝ) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w : (K.stage j.castSucc).Carrier)
    (O : (K.stage j.castSucc).Carrier) (D : ℝ≥0∞) : Prop :=
  ∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
    ∀ v' ∈ Ioo (K.time j.castSucc) v,
    v - β / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
    qthr < (K.toHistory.event j).incoming.flow.scalar v' x →
    riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v') O x ≤ D

/-- **inhabitant（`_C11PB`）**：`Rad = 0` 时球空，hseed 平凡成立（定义一致性检查）。 -/
theorem pickedBallWindowSeed_zero_C11PB (β qthr : ℝ) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w O : (K.stage j.castSucc).Carrier) (D : ℝ≥0∞) :
    PickedBallWindowSeed_C11PB β 0 qthr K j v w O D := by
  intro x hx
  simp [riemannianBallOf] at hx

/-- **hgrad ⇐ hgood + hseed（`_C11PB`，PROVED）**：窗口 `[v − β/q, v)` 上球点 `x` 在 `R(v′, x) > Cg·R_n` 处，
hseed 把 `x` 放进 hgood 的 seed 域（时间域由 `aSeed ≤ v − β/q`、`v ≤ σ`、`σ − L²/R_n ≤ v − β/q` 给出），
hgood 给 `SpatialCanonicalWitness`，其 `gradient` 字段即 `|dR| ≤ C2 R^{3/2} ≤ Cgrad R^{3/2}`。 -/
theorem pickedBallGrad_of_hgood_C11PB {Cg β : ℝ} {Cgrad : ℝ≥0} (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : C2 ≤ (Cgrad : ℝ)) (n : ℕ) (j : Fin (K n).eventCount) (v : ℝ)
    (hv2 : v < (K n).time j.succ)
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j.castSucc)
    (h2 : j.castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (w : ((K n).stage j.castSucc).Carrier) {Rad : ℝ}
    (hav : (aSeed n : ℝ) ≤ v - β / ((K n).toHistory.event j).incoming.flow.scalar v w)
    (hvs : v ≤ (σ n : ℝ))
    (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ v - β / ((K n).toHistory.event j).incoming.flow.scalar v w)
    (hseed : PickedBallWindowSeed_C11PB β Rad (Cg * R n) (K n) j v w
      ((seedTrace n).point j.castSucc h1 h2)
      (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)))) :
    PickedBallGrad_C11PB β Rad (Cg * R n) Cgrad (K n) j v w := by
  intro x hx v' hv' hwin hRx ξ
  have hd := hseed x hx v' hv' hwin hRx
  have hv'h : v' ≤ (K n).toHistory.horizon :=
    (hv'.2.le.trans hv2.le).trans ((K n).toHistory.time_le_horizon_at _)
  let τ : Icc (0 : ℝ) (K n).toHistory.horizon :=
    ⟨v', ((K n).toHistory.time_nonneg _).trans hv'.1.le, hv'h⟩
  have hact : (K n).toHistory.activeStage τ = j.castSucc :=
    (K n).activeStage_eq_castSucc_C11PB j τ hv'.1 (hv'.2.trans hv2)
  have hav' : aSeed n ≤ τ := by
    change (aSeed n : ℝ) ≤ v'
    linarith
  have hvs' : τ ≤ σ n := by
    change v' ≤ (σ n : ℝ)
    linarith [hv'.2]
  have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤ (τ : ℝ) := by
    change (σ n : ℝ) - L n ^ 2 / R n ≤ v'
    linarith
  have key : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage τ = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' : ((K n).toHistory.stage k).Carrier),
      riemannianEDistOf ((K n).toHistory.stageMetric k τ) ((seedTrace n).point k h1' h2') x' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric k τ) x' →
      ∃ W : SpatialCanonicalWitness ((K n).toHistory.stageMetric k τ) eps C1 C2 x',
        W.capTubeHasNeckChart eps := by
    intro k hk h1' h2' x' hd' hR'
    subst hk
    exact (hgood n τ hav' hvs' hvL' x' hd' hR').1
  have hd' : riemannianEDistOf ((K n).toHistory.stageMetric j.castSucc τ)
        ((seedTrace n).point j.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hd
  have hR' : Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric j.castSucc τ) x := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hRx.le
  have hres := key j.castSucc hact h1 h2 x hd' hR'
  rw [ObservedHistory.stageMetric_castSucc_apply] at hres
  obtain ⟨W, -⟩ := hres
  have hR0 : 0 ≤ ((K n).toHistory.event j).incoming.flow.scalar v' x := W.Q_pos.le
  exact (W.gradient ξ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC2 hR0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

/-- **SHALLOW T1 ⇐ hgood + hseed + hκ（`_C11PB`，PROVISIONAL：binder `hseedPB` / `hκPB`）**：
`shallowSliceRC_of_pickedBall_C11PB`（G3）的 `hgradPB` 由 `pickedBallGrad_of_hgood_C11PB` 从 `hseedPB`（同一
量词前缀）+ `hgood` + `hC2` 产出；时间域：`R_n ≤ R(v, w)` ⇒ `θ₀/R(v, w) ≤ θ₀/R_n`，`aSeed ≤ σ − (θ₀ − σ₁)/R_n`
（`hwin`），`θ₀ − σ₁ ≤ L²`（`L ≥ max 1 (θ₀ − σ₁)`），均 eventually。 -/
theorem ObservedHistory.shallowSliceRC_of_pickedBall_seed_C11PB
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
    (hκPB : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
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
          PickedBallKappa_C11PB θ₀ Rad (ρV n) κ (K n) j' v w) :
    ObservedHistory.ShallowSliceRC_C11SH η₃ Lc (fun n => (K n).toHistory) σ y R := by
  refine ObservedHistory.shallowSliceRC_of_pickedBall_C11PB (Cgrad := Cgrad) hθ₀ hθ₀2 hεle hκ hphi
    hCg hη₃ hLc htj recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK σ y R hσ
    hRpos hqR hT₀ Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV hdistQC hgood ?_ hκPB
  intro Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
  have hθσ : 0 < θ₀ - σ₁ := by linarith
  filter_upwards [hseedPB Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr,
    hφ.tendsto_atTop (hL.eventually_ge_atTop (max 1 (θ₀ - σ₁))),
    hφ.tendsto_atTop (hwin (θ₀ - σ₁) hθσ)] with n hs hLn hwn
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
  exact pickedBallGrad_of_hgood_C11PB K hgood hC2 n j' v hv2 h1 h2 w (by linarith) (by linarith)
    (by linarith) (hs j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hw hzw hRw)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
