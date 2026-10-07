import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LimitNoncollapseP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AncientWitnessP6D
import DifferentialGeometry.Geometry.Collapse.ScaleInvariance

/-!
# 外审 R-C11-2 D-3：(K-seq) → P6B M8 binder 的慢对角化 adapter（O-CH11-P6D2 G0）

后缀 `_P6D2`。外审 D-R-C11-2-3 冻结局部 κ 的量词形 (K-seq)
`∃ κ_A > 0, ∀ D L B > 0, ∀ᶠ n, ∀ 合格测试球, Vol_ĝ ≥ κ_A ϱ³ (0 < ϱ ≤ L)`；
P6B M8 / P6D G2 的 binder 是 `ρnc n √R n → ∞` + 尺度 `≤ ρnc n` 的 trace-local `hkappa`——二者
不逐字相同。**判定走 (a)（慢对角化）**：M8 内部（`:213` 的 `hnc`，`radii n = ρnc n √R n → ∞`）
本来就是"半径随 n 发散"的形；(b)（固定窗口固定尺度 eventually 形）要重写树内极限 noncollapse
（`:202` / `:213`）与 P6D G1 / G2 的 binder，成本远大于 adapter。

(K-seq) 在本文件是**显式前提 `hK`**（COMMON "显式函数与性质参数"，不打包新结构）：测试球中心
`x ∈ B_{t n}(y n, D/√R n)` 的 backward trace 点、中心时刻 `v ≥ t n − B/R n`、半径 `ϱ/√R n`
（`ϱ ≤ L`，球自带深度 `≤ L²/R n`，合计"深度备到 `B + L²`"）、`isParabolicallyRmControlledBall`、
体积在 `ĝ = scaleMetric (R n)` 下。与 S-CH11-PRE841 `Pre841Data_C11K.volume_ge`（01:2x 形）
逐字同形；PRE841 交付后以 `example` 把 `d.volume_ge` 喂给 `hK`。

* `exists_diagonal_nat_P6D2`：`∀ k, ∀ᶠ n, p k n` ⇒ `∃ L → ∞, ∀ᶠ n, p (L n) n`。
* `exists_slow_level_P6D2`：对任意上界 `M n → ∞`，存在 `m n → ∞`、`m n ≤ M n`，eventually
  **第 `m n` 级测试**（`D = L = B = m n`）成立。`M` 即"`m(n)` 慢到满足种子尺度 / 时间余量"的上界：
  调用者把种子尺度 `c r_n √Q_n` 或时间余量 `√(Q_n (s_n − (t_n − r_n²/2)))` 填进 `M`。
* `exists_tracedKappa_le_P6D2`：`ρnc n := m n / √R n`，给出 M8 binder（`hradii` + `hkappa`，`κ` 原样），
  并且 `ρnc ≤ σ`（`σ n √R n → ∞` 任给）；`exists_tracedKappa_of_kseq_P6D2`：不带上界的版本。
* consumer：`exists_local_ancient_limit_kappa_noncollapsed_of_kseq_P6D2`（M8 装配吃 (K-seq)，极限
  `κ/250`-noncollapsed）与 `exists_eventually_hasSpatialCanonicalTimeControl_of_kseq_P6D2`
  （P6D G2 吃 (K-seq)）。

**D-4 / D-6 遵守**：本文件不涉及小半径下界（没有 `nr`，更没有 `nr := 0`）；(D2) 时间余量
`Q_n (s_n − (t_n − r_n²/2)) → ∞` 不在本文件出现——(K-seq) 的 `B` 任意，深度由 (K-seq) 的生产者负责；
若由 window 形（P6B bridge）生产 (K-seq)，(D2) 是那边的显式前提，不用 `Q_n r_n² → ∞` 替代。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood (IsAncientKappaSolution PointedFlowScalarAtBase
  ancientTimeInterval)
open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- **对角论证**：`∀ k, ∀ᶠ n, p k n` ⇒ 存在 `L n → ∞`，`∀ᶠ n, p (L n) n`。 -/
theorem exists_diagonal_nat_P6D2 (p : ℕ → ℕ → Prop) (h : ∀ k, ∀ᶠ n in atTop, p k n) :
    ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧ ∀ᶠ n in atTop, p (L n) n := by
  choose N hN using fun k => eventually_atTop.1 (h k)
  refine ⟨fun n => Nat.findGreatest (fun k => N k ≤ n) n, ?_, ?_⟩
  · refine tendsto_atTop.2 fun K => eventually_atTop.2 ⟨max K (N K), fun n hn => ?_⟩
    exact Nat.le_findGreatest (le_of_max_le_left hn) (le_of_max_le_right hn)
  · refine eventually_atTop.2 ⟨N 0, fun n hn => ?_⟩
    exact hN _ n (Nat.findGreatest_spec (P := fun k => N k ≤ n) (m := 0) (Nat.zero_le n) hn)

variable {H : ℕ → ObservedHistory.{u}} {t : ∀ n, Icc (0 : ℝ) (H n).horizon}
  {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n} {κ : ℝ}

/-- **慢对角化（第 `m n` 级测试）**：(K-seq) + 任意上界 `M n → ∞` ⇒ 存在 `m n → ∞`、`m n ≤ M n`，
eventually 第 `m n` 级测试（`D = L = B = m n`）成立。 -/
theorem exists_slow_level_P6D2
    (hK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - B / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
          (H n).isParabolicallyRmControlledBall v
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
            (ϱ / Real.sqrt (R n)) →
          ENNReal.ofReal (κ * ϱ ^ 3) ≤
            Geometry.Collapse.ballVolume
              (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage v) v))
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ϱ)
    (M : ℕ → ℝ) (hM : Tendsto M atTop atTop) :
    ∃ m : ℕ → ℝ, Tendsto m atTop atTop ∧ (∀ n, m n ≤ M n) ∧ ∀ᶠ n in atTop,
    ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
        (m n / Real.sqrt (R n)),
    ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - m n / R n ≤ v →
    ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
      ((H n).activeStage_mono hvt) x,
    ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ m n →
      (H n).isParabolicallyRmControlledBall v
        (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
        (ϱ / Real.sqrt (R n)) →
      ENNReal.ofReal (κ * ϱ ^ 3) ≤
        Geometry.Collapse.ballVolume
          (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage v) v))
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ϱ := by
  have hk1 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  obtain ⟨Ls, hLs, hev⟩ := exists_diagonal_nat_P6D2 _
    (fun k : ℕ => hK ((k : ℝ) + 1) ((k : ℝ) + 1) ((k : ℝ) + 1) (hk1 k) (hk1 k) (hk1 k))
  have hL1 : Tendsto (fun n => (Ls n : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hLs).atTop_add tendsto_const_nhds
  refine ⟨fun n => min ((Ls n : ℝ) + 1) (M n), ?_, fun n => min_le_right _ _, ?_⟩
  · refine tendsto_atTop.2 fun b => ?_
    filter_upwards [hL1.eventually_ge_atTop b, hM.eventually_ge_atTop b] with n h1 h2
    exact le_min h1 h2
  · filter_upwards [hev] with n hn
    intro x hx v hvt hv tr ϱ hϱ0 hϱ hball
    have hmL : min ((Ls n : ℝ) + 1) (M n) ≤ (Ls n : ℝ) + 1 := min_le_left _ _
    have hx' := riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right hmL (Real.sqrt_nonneg _)) hx
    have hv' : (t n : ℝ) - ((Ls n : ℝ) + 1) / R n ≤ v := by
      linarith [div_le_div_of_nonneg_right hmL (hR n).le]
    exact hn x hx' v hvt hv' tr ϱ hϱ0 (hϱ.trans hmL) hball

/-- **(K-seq) → M8 binder，带上界**：对任意 `σ`（`σ n √R n → ∞`，种子尺度 / 时间余量的上界），存在
`ρnc ≤ σ`，`ρnc n √R n → ∞`，且 P6B M8 / P6D 的 trace-local `hkappa`（逐字同形，`κ` 原样）成立。
`ρnc n = m n / √R n`，`m` 来自 `exists_slow_level_P6D2`（`M n = σ n √R n`）。 -/
theorem exists_tracedKappa_le_P6D2
    (hK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - B / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
          (H n).isParabolicallyRmControlledBall v
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
            (ϱ / Real.sqrt (R n)) →
          ENNReal.ofReal (κ * ϱ ^ 3) ≤
            Geometry.Collapse.ballVolume
              (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage v) v))
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ϱ)
    (σ : ℕ → ℝ) (hσ : Tendsto (fun n => σ n * Real.sqrt (R n)) atTop atTop) :
    ∃ ρnc : ℕ → ℝ, (∀ n, ρnc n ≤ σ n) ∧
      Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop ∧
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (H n).isParabolicallyRmControlledBall v
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' := by
  obtain ⟨m, hm, hmM, hev⟩ := exists_slow_level_P6D2 hK _ hσ
  have hsR : ∀ n, 0 < Real.sqrt (R n) := fun n => Real.sqrt_pos.mpr (hR n)
  refine ⟨fun n => m n / Real.sqrt (R n), fun n => ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (hsR n)]
    exact hmM n
  · have hfun : (fun n => m n / Real.sqrt (R n) * Real.sqrt (R n)) = m :=
      funext fun n => div_mul_cancel₀ _ (hsR n).ne'
    rw [hfun]
    exact hm
  · intro D T hD hT
    filter_upwards [hev, hm.eventually_ge_atTop (max D T)] with n hn hmn
    intro x hx v hvt hv tr r'' hr0 hr hball
    have hx' := riemannianBallOf_mono _ _
      (div_le_div_of_nonneg_right ((le_max_left D T).trans hmn) (Real.sqrt_nonneg _)) hx
    have hv' : (t n : ℝ) - m n / R n ≤ v := by
      linarith [div_le_div_of_nonneg_right ((le_max_right D T).trans hmn) (hR n).le]
    have hr' : r'' ≤ m n / Real.sqrt (R n) := hr
    have hϱ : Real.sqrt (R n) * r'' ≤ m n := by
      have := (le_div_iff₀ (hsR n)).1 hr'
      linarith
    have hball' : (H n).isParabolicallyRmControlledBall v
        (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
        (Real.sqrt (R n) * r'' / Real.sqrt (R n)) := by
      rw [mul_div_cancel_left₀ _ (hsR n).ne']
      exact hball
    have h := hn x hx' v hvt hv' tr (Real.sqrt (R n) * r'') (mul_pos (hsR n) hr0) hϱ hball'
    have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp
    exact (Geometry.Collapse.le_ballVolume_scaleMetric_iff hfin (R n) (hR n)).1 h

/-- **(K-seq) → M8 binder**（无上界版；`σ n = (n + 1)/√R n`）。 -/
theorem exists_tracedKappa_of_kseq_P6D2
    (hK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - B / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
          (H n).isParabolicallyRmControlledBall v
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
            (ϱ / Real.sqrt (R n)) →
          ENNReal.ofReal (κ * ϱ ^ 3) ≤
            Geometry.Collapse.ballVolume
              (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage v) v))
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ϱ) :
    ∃ ρnc : ℕ → ℝ, Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop ∧
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (H n).isParabolicallyRmControlledBall v
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' := by
  have hsR : ∀ n, 0 < Real.sqrt (R n) := fun n => Real.sqrt_pos.mpr (hR n)
  have hσ : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / Real.sqrt (R n) * Real.sqrt (R n))
      atTop atTop := by
    have hfun : (fun n : ℕ => ((n : ℝ) + 1) / Real.sqrt (R n) * Real.sqrt (R n)) =
        fun n : ℕ => (n : ℝ) + 1 := funext fun n => div_mul_cancel₀ _ (hsR n).ne'
    rw [hfun]
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  obtain ⟨ρnc, -, hradii, hkappa⟩ := exists_tracedKappa_le_P6D2 hK _ hσ
  exact ⟨ρnc, hradii, hkappa⟩

/-- **consumer（M8 吃 (K-seq)）**：P6B M8 装配 `exists_local_ancient_limit_kappa_noncollapsed_P6B`
的 `ρnc, hradii, hkappa` 换成 (K-seq) `hK`（经慢对角化）；极限 `κ/250`-noncollapsed，`κ` 原样。 -/
theorem exists_local_ancient_limit_kappa_noncollapsed_of_kseq_P6D2
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    (htraced : ∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ)
    (hK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - B / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
          (H n).isParabolicallyRmControlledBall v
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
            (ϱ / Real.sqrt (R n)) →
          ENNReal.ofReal (κ * ϱ ^ 3) ≤
            Geometry.Collapse.ballVolume
              (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage v) v))
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ϱ)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v)
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
          (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))))) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (_ : PointedRiemannianConvergenceMaps X P f),
        MetricComplete P ∧ ConnectedSpace P.M ∧
        ∃ (G : ℝ → SmoothRiemannianMetric ThreeModel P.M)
          (_ : IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
            ancientTimeInterval)),
          G 0 = P.metric ∧
          ∀ ρ : ℝ, 0 < ρ → Perelman.ParabolicallyKappaNoncollapsedBelowScale
            ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
              ancientTimeInterval) (κ / 250) ρ := by
  obtain ⟨ρnc, hradii, hkappa⟩ := exists_tracedKappa_of_kseq_P6D2 hK
  exact exists_local_ancient_limit_kappa_noncollapsed_P6B H t y R hR hRlim htraced hr₀ hw hseed
    hκ ρnc hradii hkappa hPhi hpinch

/-- **consumer（P6D G2 吃 (K-seq)）**：
`exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D` 的 `ρnc, hradii, hkappa` 换成
(K-seq)；(i) 极限是 `κ/250/30³`-ancient κ-solution，(ii) 坏点 eventually 满足完整
`HasSpatialCanonicalTimeControl`。 -/
theorem exists_eventually_hasSpatialCanonicalTimeControl_of_kseq_P6D2 :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n),
      (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) = R n) →
      Tendsto R atTop atTop →
      (∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) →
      ∀ {r₀ w : ℝ}, 0 < r₀ → 0 < w →
      (∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
            ((H n).stageMetric ((H n).activeStage (t n)) (t n))
            (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      ∀ {κ : ℝ}, 0 < κ →
      (∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
          ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
              (D / Real.sqrt (R n)),
          ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - B / R n ≤ v →
          ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
            ((H n).activeStage_mono hvt) x,
          ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
            (H n).isParabolicallyRmControlledBall v
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
              (ϱ / Real.sqrt (R n)) →
            ENNReal.ofReal (κ * ϱ ^ 3) ≤
              Geometry.Collapse.ballVolume
                (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage v) v))
                (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ϱ) →
      ∀ {Phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction Phi →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))))) →
      ∀ {C1s C2s Cs Cq : ℝ} {Ctime : ℝ≥0} {qs qcan : ℕ → ℝ},
      (∀ n, qs n ≤ Cs * R n) → (∀ n, qcan n ≤ Cq * R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        (v : ℝ) < t n → (H n).time ((H n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) ε C1s C2s
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        (v : ℝ) < t n → (H n).time ((H n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v')
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ^ 2) →
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    (∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (_ : PointedRiemannianConvergenceMaps X P f)
        (G : ℝ → SmoothRiemannianMetric ThreeModel P.M)
        (hG : IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
          ancientTimeInterval)),
        IsAncientKappaSolution (κ / 250 / 30 ^ 3) (flowOfMetric ancientTimeInterval P G hG) ∧
        PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval P G hG) 1) ∧
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
      (H (ψ i)).HasSpatialCanonicalTimeControl ε C C C.toNNReal (t (ψ i)) (y (ψ i)) := by
  obtain ⟨epsW, hepsW, hB⟩ :=
    exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW
  refine ⟨C, hC, ?_⟩
  intro H t y R hR hscal hRlim htraced r₀ w hr₀ hw hseed κ hκ hK Phi hPhi hpinch
    C1s C2s Cs Cq Ctime qs qcan hqs hqcan hwit hderiv
  obtain ⟨ρnc, hradii, hkappa⟩ := exists_tracedKappa_of_kseq_P6D2 hK
  exact hB' H t y R hR hscal hRlim htraced hr₀ hw hseed hκ ρnc hradii hkappa hPhi hpinch
    hqs hqcan hwit hderiv

/-- consumer（带上界的慢对角化）：种子尺度上界 `σ`（`σ n √R n → ∞`）下取 `ρnc ≤ σ`，`ρnc √R → ∞`
（即 M8 的 `hradii`），`hkappa` 由同一 `ρnc` 给出。 -/
example (hK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - B / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
          (H n).isParabolicallyRmControlledBall v
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
            (ϱ / Real.sqrt (R n)) →
          ENNReal.ofReal (κ * ϱ ^ 3) ≤
            Geometry.Collapse.ballVolume
              (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage v) v))
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ϱ)
    (σ : ℕ → ℝ) (hσ : Tendsto (fun n => σ n * Real.sqrt (R n)) atTop atTop) :
    ∃ ρnc : ℕ → ℝ, (∀ n, ρnc n ≤ σ n) ∧ Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop :=
  let ⟨ρnc, hle, hradii, _⟩ := exists_tracedKappa_le_P6D2 hK σ hσ
  ⟨ρnc, hle, hradii⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
