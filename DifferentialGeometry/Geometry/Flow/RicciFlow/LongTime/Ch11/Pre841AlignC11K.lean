import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Pre841DefsC11K
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedRegionAncientLimitTimeControl_P6L

/-!
# `Pre841` 与 P6B / P6D 的对齐（S-CH11-PRE841 G2，后缀 `_C11K`）

`Pre841Data_C11K`（`Pre841DefsC11K.lean`）与树内两个已有形的关系：

* **(ii) P6D / `TracedRegionAncientLimitTimeControl_P6L` 的 trace-local `hkappa`**
  （`∀ D T`、eventually、尺度 `≤ ρnc n`、`ρnc n √R n → ∞`）——**同构（只差存在性的 `ρnc`）**：
  - `Pre841Data_C11K.ofTracedKappa`（Defs）：`hkappa` ⇒ `Pre841`；
  - `Pre841Data_C11K.exists_tracedKappa`：`Pre841` ⇒ `∃ ρnc, ρnc √R → ∞ ∧ hkappa`，`ρnc` 由对角论证
    `exists_diagonal_nat_C11K`（`ρnc n = (L n + 1)/√(R n)`，`L n → ∞`）给出，`κ` 原样保留；
  - `nonempty_pre841_iff_tracedKappa_C11K`：两者互相蕴含；
  - consumer：`Pre841` 直接喂 P6D 的 `…_of_traced_seed_P6L`。
* **(i) P6B 的 `hKappaLocal` = `LocalKappaSupply_P6B`**——**单向，且方向是 `hKappaLocal ⇒ Pre841`**
  （需要额外前提）：`Pre841ConsumerC11K.lean` 的 `pre841Data_of_window_C11K` /
  `pre841_of_localKappa_C11K` 把 L5 window 形 + L7 survival 的距离结论 `hdist` + 窗口条件
  `hwin` + `(r n / 200) √(R n) → ∞` 打包成 `Pre841`
  （就是 `tracedKappa_of_window_P6B` 加 `ofTracedKappa`）。**反向不成立**：`Pre841` 的测试球在
  `ϱ ≤ L` 的归一化尺度（`≪` 种子尺度 `r n`），`hKappaLocal` 在种子球 `B(p, A r)` 上（`A` 与种子
  同量级）且 `κ(A)` 依赖 `A`、对一切 `n` 与一切种子成立；`Pre841` 只对一条给定序列、eventually。
  能证的最强"特化"是 `Pre841Data_C11K.eventually_localKappa_base`：基点时刻（`v = t n`，平凡
  trace）、半径 `≤ 1/√R n` 的 `LocalKappaAt_P6B` 结论块，沿这条序列 eventually 成立。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 对角论证 -/

/-- **对角论证**：`∀ k, ∀ᶠ n, p k n` ⇒ 存在 `L n → ∞`，`∀ᶠ n, p (L n) n`。 -/
theorem exists_diagonal_nat_C11K (p : ℕ → ℕ → Prop) (h : ∀ k, ∀ᶠ n in atTop, p k n) :
    ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧ ∀ᶠ n in atTop, p (L n) n := by
  choose N hN using fun k => eventually_atTop.1 (h k)
  refine ⟨fun n => Nat.findGreatest (fun k => N k ≤ n) n, ?_, ?_⟩
  · refine tendsto_atTop.2 fun K => eventually_atTop.2 ⟨max K (N K), fun n hn => ?_⟩
    exact Nat.le_findGreatest (le_of_max_le_left hn) (le_of_max_le_right hn)
  · refine eventually_atTop.2 ⟨N 0, fun n hn => ?_⟩
    exact hN _ n (Nat.findGreatest_spec (P := fun k => N k ≤ n) (m := 0) (Nat.zero_le n) hn)

namespace Pre841Data_C11K

variable {H : ℕ → ObservedHistory.{u}} {t : ∀ n, Icc (0 : ℝ) (H n).horizon}
  {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n}

/-! ## (ii) 与 P6D `hkappa` 的对齐 -/

/-- **`Pre841` ⇒ P6D 的 trace-local `hkappa`**【同构，无额外前提】
（`TracedRegionAncientLimitTimeControl_P6L` 的同名前提，逐字同形）：
对角 `ρnc n = (L n + 1)/√(R n)`，`L n → ∞`，`κ = d.kappa`。 -/
theorem exists_tracedKappa (d : Pre841Data_C11K H t y R hR) :
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
        ENNReal.ofReal (d.kappa * r'' ^ 3) ≤
          ballVolume ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' := by
  obtain ⟨Ls, hLs, hev⟩ := exists_diagonal_nat_C11K _
    (fun k : ℕ => d.volume_ge ((k : ℝ) + 1) ((k : ℝ) + 1) ((k : ℝ) + 1)
      (by positivity) (by positivity) (by positivity))
  have hsR : ∀ n, 0 < Real.sqrt (R n) := fun n => Real.sqrt_pos.mpr (hR n)
  refine ⟨fun n => ((Ls n : ℝ) + 1) / Real.sqrt (R n), ?_, ?_⟩
  · have hfun : (fun n => ((Ls n : ℝ) + 1) / Real.sqrt (R n) * Real.sqrt (R n)) =
        fun n => (Ls n : ℝ) + 1 := funext fun n => div_mul_cancel₀ _ (hsR n).ne'
    rw [hfun]
    exact (tendsto_natCast_atTop_atTop.comp hLs).atTop_add tendsto_const_nhds
  · intro D T hD hT
    filter_upwards [hev, hLs.eventually_ge_atTop ⌈max D T⌉₊] with n hn hL
    intro x hx v hvt hv tr r'' hr0 hr hball
    have hDT : max D T ≤ (Ls n : ℝ) + 1 :=
      calc max D T ≤ (⌈max D T⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (Ls n : ℝ) := by exact_mod_cast hL
        _ ≤ (Ls n : ℝ) + 1 := by linarith
    have hx' := riemannianBallOf_mono _ _
      (div_le_div_of_nonneg_right (le_trans (le_max_left D T) hDT) (Real.sqrt_nonneg _)) hx
    have hv' : (t n : ℝ) - ((Ls n : ℝ) + 1) / R n ≤ v := by
      linarith [div_le_div_of_nonneg_right (le_trans (le_max_right D T) hDT) (hR n).le]
    have hϱ : Real.sqrt (R n) * r'' ≤ (Ls n : ℝ) + 1 := by
      have := (le_div_iff₀ (hsR n)).1 hr
      linarith
    have hball' : (H n).isParabolicallyRmControlledBall v
        (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
        (Real.sqrt (R n) * r'' / Real.sqrt (R n)) := by
      rw [mul_div_cancel_left₀ _ (hsR n).ne']
      exact hball
    have h := hn x hx' v hvt hv' tr (Real.sqrt (R n) * r'') (mul_pos (hsR n) hr0) hϱ hball'
    have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp
    exact (le_ballVolume_scaleMetric_iff hfin (R n) (hR n)).1 h


/-! ## (i) 与 P6B `hKappaLocal` 的对齐：能证的"特化" -/

/-- **特化（基点时刻、平凡 trace）**【单向：`Pre841 ⇒` `LocalKappaAt_P6B` 结论块的基点版；
缺 `hKappaLocal` 的 `∀ n`、种子前提、`κ(A)` 在种子尺度，故不是 `Pre841 ⇒ hKappaLocal`】：
`Pre841` 对每个 `A > 0` 给出 `LocalKappaAt_P6B` 结论块的基点时刻版本：`v = t n`，
半径 `ρ' ≤ 1/√(R n)`（种子尺度 `r = 1/√(R n)`），`x ∈ B(y n, A r)`，
`κ = d.kappa` 与 `A` 无关；**只沿这条序列 eventually**，没有 `hKappaLocal` 的 `∀ n`、种子前提与
`ρ' ≥ nr t/100` 下界——这就是 `Pre841 ⇒ hKappaLocal` 缺的部分（见文件头）。 -/
theorem eventually_localKappa_base (d : Pre841Data_C11K H t y R hR) (A : ℝ) :
    ∀ᶠ n in atTop,
    ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
        (A / Real.sqrt (R n)),
    ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ 1 / Real.sqrt (R n) →
      (H n).isParabolicallyRmControlledBall (t n) x ρ' →
      ENNReal.ofReal (d.kappa * ρ' ^ 3) ≤
        ballVolume ((H n).stageMetric ((H n).activeStage (t n)) (t n)) x ρ' := by
  filter_upwards [d.volume_ge (max A 1) 1 1 (lt_max_of_lt_right one_pos) one_pos one_pos] with n hn
  intro x hx ρ' hρ0 hρr hball
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hx' := riemannianBallOf_mono _ _
    (div_le_div_of_nonneg_right (le_max_left A 1) (Real.sqrt_nonneg _)) hx
  have hϱ : Real.sqrt (R n) * ρ' ≤ 1 := by
    have := (le_div_iff₀ hsR).1 hρr
    linarith
  let tr := BackwardPointTrace.singleton (H n) ((H n).activeStage (t n)) x
  have hpt : tr.point ((H n).activeStage (t n)) le_rfl ((H n).activeStage_mono le_rfl) = x :=
    tr.endpoint_eq
  have hball' : (H n).isParabolicallyRmControlledBall (t n)
      (tr.point ((H n).activeStage (t n)) le_rfl ((H n).activeStage_mono le_rfl))
      (Real.sqrt (R n) * ρ' / Real.sqrt (R n)) := by
    rw [hpt, mul_div_cancel_left₀ _ hsR.ne']
    exact hball
  have h := hn x hx' (t n) le_rfl (by linarith [div_pos one_pos (hR n)]) tr
    (Real.sqrt (R n) * ρ') (mul_pos hsR hρ0) hϱ hball'
  rw [hpt] at h
  have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp
  exact (le_ballVolume_scaleMetric_iff hfin (R n) (hR n)).1 h

end Pre841Data_C11K

/-- **【同构】（至多差存在性的 `ρnc` 与 native 内容 `N`）**：`Pre841` 数据存在 ⇔ native 内容存在
且 P6D 的 `hkappa` 对某个 `κ > 0`、某个 `ρnc`（`ρnc n √R n → ∞`）成立。 -/
theorem nonempty_pre841_iff_tracedKappa_C11K {H : ℕ → ObservedHistory.{u}}
    {t : ∀ n, Icc (0 : ℝ) (H n).horizon} {y : ∀ n, ((H n).stageAt (t n)).Carrier}
    {R : ℕ → ℝ} (hR : ∀ n, 0 < R n) :
    Nonempty (Pre841Data_C11K H t y R hR) ↔
      Nonempty (Pre841NativeData_C11K H) ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ ρnc : ℕ → ℝ,
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
            ballVolume ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' := by
  constructor
  · rintro ⟨d⟩
    obtain ⟨ρnc, hradii, hkappa⟩ := d.exists_tracedKappa
    exact ⟨⟨d.native⟩, d.kappa, d.kappa_pos, ρnc, hradii, hkappa⟩
  · rintro ⟨⟨N⟩, κ, hκ, ρnc, hradii, hkappa⟩
    exact ⟨Pre841Data_C11K.ofTracedKappa N hκ hradii hkappa⟩

open ObservedHistory in
/-- **consumer（P6D）**【同构 ⇒ 直接消费，无额外前提；其余前提是 `…_of_traced_seed_P6L` 自己的】：
`Pre841` 数据直接喂 `TracedRegionAncientLimitTimeControl_P6L` 的
`…_of_traced_seed_P6L`（`hkappa` / `hradii` 由 `exists_tracedKappa` 给出，`κ = d.kappa`）。 -/
example {H : ℕ → ObservedHistory.{u}} {t : ∀ n, Icc (0 : ℝ) (H n).horizon}
    {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n}
    (d : Pre841Data_C11K H t y R hR) (hRlim : Tendsto R atTop atTop)
    (htraced : ∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (R n))))
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
    True := by
  obtain ⟨ρnc, hradii, hkappa⟩ := d.exists_tracedKappa
  have key := exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_traced_seed_P6L
    H t y R hR hRlim htraced hr₀ hw hseed d.kappa_pos ρnc hradii hkappa hPhi hpinch
  obtain ⟨W, h, -⟩ := key
  trivial

end GC.LongTime.Ch11
