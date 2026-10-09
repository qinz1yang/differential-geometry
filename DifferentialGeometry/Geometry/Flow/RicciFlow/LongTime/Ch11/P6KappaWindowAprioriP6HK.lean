import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallSeedClosureC11SC

/-!
# Q-HK1 先验供给件：KS2 窗口的 κ 高点支、梯度、前推 ODE（A1 续，后缀 `_P6HK`）

A1 G0 表（`build-logs/resume/state-O-CH11-HARNACK.md` "A1 续作" 节）：KS2 / P6TF 窗口供给全部可由先验供给给出。
本文件只做其中**不需要帧搬运**的三件逐点核（PROVED，无 binder）：
* `rm_le_of_controlledBall_P6HK`：`isParabolicallyRmControlledBall τ p b` ⇒ `b⁴|Rm|²(τ, p) ≤ 1`
  （中心点、端点时刻）。
* `requiresVolume_of_low_point_P6HK`：witness 的 round 支排除——同一连通分量里有一点 `R(p) < C2⁻¹·R(x)`
  （driver 里 = seed 点，`hsmall`）⇒ `W.alternative.requiresVolume`（round 支 domain = 整个分量，与
  `scalar_bounds` 矛盾）。
* `exists_kappa_hi_P6HK`：**K6 高点支**——witness（S16 全局供给）在 `(τ, zz)` ⇒ KS2 / P6TF κ 合取的逐点形，
  κ 只依赖 `(ε, C1, C2)`（在 ∀A 之前），经 `exists_ball_volume_of_spatialCanonicalWitness`。
* `gradient_of_witness_P6HK`：**K4**——slab 时刻 `v′` 的 witness ⇒ KS2 梯度前提逐点形（`Cgrad := C2`）。
* `scalar_le_two_mul_forward_P6HK`：**K6 低点支的时间件**——event slab 的 `DerivativeBoundBefore`（先验 Dt）
  前推：`R(s, y) ≤ M`、`Ctime·M·(v − s) ≤ 1/2` ⇒ `R(v, y) ≤ 2M`
  （`scalar_le_two_mul_of_derivativeBound_C11SC` 的前向孪生）。
不声称 happrox / hRP 已得；装配（S16 帧搬运、WSBASE footprint ⇒ `hκR`、P6TF、介值、window 帧）见 state。
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness
  SpatialCanonicalAlternative exists_ball_volume_of_spatialCanonicalWitness)

/-- **controlled ball ⇒ 中心点曲率（`_P6HK`）**：`b⁴|Rm|² ≤ 1` 在 `(τ, p)`。 -/
theorem rm_le_of_controlledBall_P6HK (H : ObservedHistory.{u}) {τ : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt τ).Carrier} {b : ℝ} (h : H.isParabolicallyRmControlledBall τ p b) :
    b ^ 4 * normSq0S (H.stageMetric (H.activeStage τ) τ) p 4
      (metricRm04At (H.stageMetric (H.activeStage τ) τ) p) ≤ 1 := by
  obtain ⟨hb, a, hat, -, htr⟩ := h
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage τ) τ) p b := by
    change riemannianEDistOf (H.stageMetric (H.activeStage τ) τ) p p < ENNReal.ofReal b
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hb
  obtain ⟨A, hA⟩ := htr p hp
  have h1 := hA.1 τ hat le_rfl
  have he : A.point (H.activeStage τ) (H.activeStage_mono hat) (H.activeStage_mono le_rfl) = p :=
    A.endpoint_eq
  rw [he] at h1
  exact h1

/-- **round 支排除（`_P6HK`）**：同分量里有 `R(p) < C2⁻¹·R(x)` 的点 ⇒ witness 不是 round 支。 -/
theorem requiresVolume_of_low_point_P6HK {P : OrientedThreeStage.{u}} {g : P.Metric}
    {ε C1 C2 : ℝ} {x : P.Carrier} (W : SpatialCanonicalWitness g ε C1 C2 x) (p : P.Carrier)
    (hp : p ∈ connectedComponent x)
    (hlow : metricScalarAt g p < C2⁻¹ * metricScalarAt g x) :
    W.alternative.requiresVolume := by
  cases hA : W.alternative with
  | round whole data =>
    exfalso
    have hpD : p ∈ W.domain.carrier := whole ▸ hp
    exact absurd (W.scalar_bounds p hpD).1 (not_le.mpr hlow)
  | neck data => trivial
  | cap data deep => trivial
  | positive whole data sec => trivial

/-- **K6 高点支（`_P6HK`，PROVED）**：controlled ball 中心有（非 round）witness ⇒ KS2 / P6TF 的 κ 逐点形；
κ 只依赖 `(ε, C1, C2)`。 -/
theorem exists_kappa_hi_P6HK (ε C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (H : ObservedHistory.{u}) (τ : Icc (0 : ℝ) H.horizon)
      (zz : (H.stageAt τ).Carrier) (b : ℝ)
      (W : SpatialCanonicalWitness (H.stageMetric (H.activeStage τ) τ) ε C1 C2 zz),
      W.capTubeHasNeckChart ε → W.alternative.requiresVolume →
      H.isParabolicallyRmControlledBall τ zz b →
      ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt τ).Carrier
          (H.stageMetric (H.activeStage τ) τ)
          (riemannianBallOf (H.stageMetric (H.activeStage τ) τ) zz b) := by
  obtain ⟨κ, hκ, hvol⟩ := exists_ball_volume_of_spatialCanonicalWitness.{u} ε C1 C2
  refine ⟨κ, hκ, ?_⟩
  intro H τ zz b W hchart hreq hball
  have hb : 0 < b := hball.1
  have h := hvol W hchart hreq b hb (rm_le_of_controlledBall_P6HK H hball)
  rw [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **K4（`_P6HK`，PROVED）**：slab 时刻 `v′` 的 witness ⇒ KS2 梯度前提逐点形（`Cgrad := C2`，`C2 ≤ Cgrad`）。 -/
theorem gradient_of_witness_P6HK {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) {ε C1 C2 : ℝ} {Cgrad : ℝ≥0} (hC2 : C2 ≤ (Cgrad : ℝ)) {v : ℝ}
    {x : P.Carrier} (W : SpatialCanonicalWitness (G.flow.base.metric v) ε C1 C2 x)
    (ξ : TangentSpace ThreeModel x) :
    |scalarDifferential G.flow v x ξ| ≤
      Cgrad * G.flow.scalar v x * Real.sqrt (G.flow.scalar v x) *
        Real.sqrt ((G.flow.base.metric v).inner x ξ ξ) := by
  have hR0 : 0 ≤ G.flow.scalar v x := W.Q_pos.le
  exact (W.gradient ξ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC2 hR0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

/-- **前推 ODE（`_P6HK`，PROVED）**：`scalar_le_two_mul_of_derivativeBound_C11SC` 的前向孪生：
`R(s, y) ≤ M`（`qcan ≤ M`）、`time j⁻ ≤ s ≤ v < time j⁺`、`Ctime·M·(v − s) ≤ 1/2` ⇒ `R(v, y) ≤ 2M`。 -/
theorem ObservedHistory.scalar_le_two_mul_forward_P6HK (H : ObservedHistory.{u})
    (j : Fin H.eventCount) {Ctime : ℝ≥0} {qcan : ℝ}
    (hder : (H.event j).incoming.DerivativeBoundBefore Ctime qcan (H.time j.succ))
    {v M s : ℝ} (hM : 0 < M) (hqcan : qcan ≤ M) (hv2 : v < H.time j.succ)
    (hs1 : H.time j.castSucc ≤ s) (hsv : s ≤ v) (hbud : (Ctime : ℝ) * M * (v - s) ≤ 1 / 2)
    (y : (H.stage j.castSucc).Carrier) (hy : (H.event j).incoming.flow.scalar s y ≤ M) :
    (H.event j).incoming.flow.scalar v y ≤ 2 * M := by
  have hL := (H.event j).incoming.lipschitzOnWith_inv_max_scalar_of_derivativeBoundBefore_P6L
    hM hqcan hv2 y (fun r hr hR => hder y r ⟨hr.1, hr.2.trans hv2⟩ hR)
  have hd := hL.dist_le_mul v ⟨hs1.trans hsv, le_rfl⟩ s ⟨hs1, hsv⟩
  have hvs : |v - s| = v - s := abs_of_nonneg (by linarith)
  rw [Real.dist_eq, Real.dist_eq, hvs] at hd
  exact le_two_mul_of_abs_inv_max_sub_le_C11SC hM hy hd hbud

/-- consumer：K6 高点支 + round 排除 一次装配（witness、同分量低点 ⇒ κ）。 -/
example (ε C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (H : ObservedHistory.{u}) (τ : Icc (0 : ℝ) H.horizon)
      (zz p : (H.stageAt τ).Carrier) (b : ℝ)
      (W : SpatialCanonicalWitness (H.stageMetric (H.activeStage τ) τ) ε C1 C2 zz),
      W.capTubeHasNeckChart ε → p ∈ connectedComponent zz →
      metricScalarAt (H.stageMetric (H.activeStage τ) τ) p <
        C2⁻¹ * metricScalarAt (H.stageMetric (H.activeStage τ) τ) zz →
      H.isParabolicallyRmControlledBall τ zz b →
      ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt τ).Carrier
          (H.stageMetric (H.activeStage τ) τ)
          (riemannianBallOf (H.stageMetric (H.activeStage τ) τ) zz b) := by
  obtain ⟨κ, hκ, h⟩ := exists_kappa_hi_P6HK.{u} ε C1 C2
  exact ⟨κ, hκ, fun H τ zz p b W hc hp hlow hball =>
    h H τ zz b W hc (requiresVolume_of_low_point_P6HK W p hp hlow) hball⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
