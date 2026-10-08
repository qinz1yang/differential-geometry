import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingMaximalWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.FixedEndpoints

/-!
# maximal-depth 的有限年龄迹 Harnack（O-CH11-HARNACK G1，后缀 `_P6HK`）

R-C11-22/23 后的修正目标（lead）：Perelman I.12.1 maximal-depth 论证用的**有限年龄迹 Harnack**
`R_t ≥ -R/(t - t*)`，在 driver 的局部流极限（窗口 `(-T, 0]`，`t* = -T`）上。树内来源（均 PROVED，axioms standard）：
* `hamilton_trace_harnack`（`HamiltonHarnack/TraceHarnack.lean:26`，有限 origin 的迹 Harnack）
  及其推论
  `hamilton_scalar_clock_monotoneOn`（`TraceCorollaries.lean`：`(s - t₀)·R(s, x)` 单调）；
* 非负曲率算子：`curvatureOperator_nonnegative_of_local_pinching_limit_on_window`（Hamilton–Ivey + `Q → ∞`）；
  完备：`complete_at_earlier_time_of_ricci_nonnegative`；`|Rm| ≤ √3·R`：
  `sqrt_rmNormSq_le_sqrt_three_mul_scalar_of_curvatureOperatorNonneg`（3 维）。
本文件：
* §1 `scalar_shift_mul_le_of_window_harnack_P6HK`（核心，参数形：每个紧子 slab 上标量有界 `hbd`，供截短窗口
  `(-T+ε, 0]` 的 `C(ε)` 路线用）：`(t + T)·R(t, x)` 在 `(-T, 0]` 上单调（origin `a → -T⁺` 极限 + 端点 `t → 0⁻`）；
  推论 `scalar_le_div_of_window_harnack_P6HK`（`R(t,x) ≤ T·R(0,x)/(t+T)`）、
  `neg_scalar_div_le_deriv_of_window_harnack_P6HK`（`-R/(t+T) ≤ ∂ₜR`，内部时刻）。
* §2 `harnack_window_limit_P6HK`：window 引理
  `exists_uniform_scalar_bound_of_local_flow_limit_on_window` 前提**逐字**（binder 块 sha256
  = ab660c4a53c6390f…；hcone/hcomplete 证明前缀逐字 sha256 = e0cdf95cd744a821…）⇒ 原结论 ∧ 上述三形。
* §3 example：新结论第一合取 = 旧结论逐字。
**循环警告**：§2 的 `hbd` 来自 window 引理结论，后者要 `happrox`（整窗 `[-c k, 0]`、`C` 对 `k` 一致）= driver 内
hbcadC 的 U 侧；所以 §2 本身**不**解决 hclosC 底部溢出。Perelman 次序用 §1 的参数形（截短窗口 + 对角极限），
见 `build-logs/resume/state-O-CH11-HARNACK.md`"maximal-depth 的有限年龄 Harnack 路线"。
无新具名 binder / 合同 Prop。由 `build-logs/scratch/O-CH11-HARNACK/gen/gen.py` 生成（逐字抽取 + assert）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-! ## §1 有限年龄迹 Harnack：openClosed 窗口上的 origin → −T 极限形（核心，参数形 `hbd`） -/

open Perelman.CanonicalNeighborhood in
/-- 窗口 `(-T, 0]` 上的 Ricci flow（完备、非负曲率算子、每个紧子 slab 上标量有上界）满足
有限年龄迹 Harnack 的积分形：`(t + T)·R(t, x)` 在 `(-T, 0]` 上单调不减（年龄原点 `t* = -T`）。
证明 = 树内 `hamilton_scalar_clock_monotoneOn`（origin `a ∈ (-T, t₁)`）+ `a → -T⁺` 极限 +
`t₂ → 0⁻` 端点连续性；`hcurv` 由 `|Rm| ≤ √3·R`（3 维非负曲率算子）与 `hbd` 给。 -/
theorem scalar_shift_mul_le_of_window_harnack_P6HK
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {T : ℝ} (hT : 0 < T)
    {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)))
    (hcomplete : ∀ t ∈ Ioo (-T) 0, RiemannianMetricComplete (G t))
    (hcone : ∀ t ∈ Ioo (-T) 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone)
    (hbd : ∀ a b : ℝ, Icc a b ⊆ Ioo (-T) 0 → ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x : P.M,
      metricScalarAt (G t) x ≤ C)
    {t₁ t₂ : ℝ} (h₁ : -T < t₁) (h12 : t₁ ≤ t₂) (h₂ : t₂ ≤ 0) (x : P.M) :
    (t₁ + T) * metricScalarAt (G t₁) x ≤ (t₂ + T) * metricScalarAt (G t₂) x := by
  let D : RealTimeInterval := RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩
  let S : SolutionOn (I := I3) (M := P.M) D := { base.metric := G }
  have hreg : D.regular = Ioo (-T) 0 := rfl
  have hcurv : ∀ a b : ℝ, Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ y : P.M,
        Tensor0SBundle.normSq0S (I := I3) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ C := by
    intro a b hab
    obtain ⟨C, hC⟩ := hbd a b (by simpa only [hreg] using hab)
    refine ⟨3 * C ^ 2, fun t ht y => ?_⟩
    have htr : t ∈ Ioo (-T) 0 := by simpa only [hreg] using hab ht
    have hnn : curvatureOperatorLowerBoundAt (I := I3) (S.base.metric t) y
        ⟨S.base.rm04 t y, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I3) (S.base.metric t) y⟩ 0 := by
      intro n c v w
      have h := (mem_algebraicCurvatureOperatorNonnegativeCone.mp (hcone t htr y)) n c v w
      rw [zero_mul, add_zero]
      exact h
    have hsq := sqrt_rmNormSq_le_sqrt_three_mul_scalar_of_curvatureOperatorNonneg
      (I := I3) S (by simp) t y hnn
    have hR0 : 0 ≤ metricScalarAt (G t) y :=
      metricScalarAt_nonnegative_of_curvatureOperator_nonnegative (G t) y (hcone t htr y)
    have hRC : metricScalarAt (G t) y ≤ C := hC t ht y
    have hnorm0 : 0 ≤ Perelman.FlowMetricBall.rmNormSq (I := I3) S t y :=
      Tensor0SBundle.normSq0S_nonneg (I := I3) (S.base.metric t) y 4 (S.base.rm04 t y)
    have hscal : S.scalar t y = metricScalarAt (G t) y := rfl
    rw [hscal] at hsq
    have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsq2 : Perelman.FlowMetricBall.rmNormSq (I := I3) S t y ≤
        (Real.sqrt 3 * metricScalarAt (G t) y) ^ 2 := by
      calc Perelman.FlowMetricBall.rmNormSq (I := I3) S t y
          = (Real.sqrt (Perelman.FlowMetricBall.rmNormSq (I := I3) S t y)) ^ 2 :=
            (Real.sq_sqrt hnorm0).symm
        _ ≤ (Real.sqrt 3 * metricScalarAt (G t) y) ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
    have hfin : (Real.sqrt 3 * metricScalarAt (G t) y) ^ 2 ≤ 3 * C ^ 2 := by
      rw [mul_pow, h3]
      have : metricScalarAt (G t) y ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hR0 hRC 2
      linarith
    exact hsq2.trans hfin
  have hcompS : ∀ t ∈ D.regular, RiemannianMetricComplete (I := I3) (S.base.metric t) :=
    fun t ht => hcomplete t (by simpa only [hreg] using ht)
  have hconeS : ∀ t ∈ D.regular, ∀ y : P.M,
      metricAlgebraicCurvatureTensorAt (I := I3) (M := P.M) (S.base.metric t) y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I3) (M := P.M) :=
    fun t ht y => hcone t (by simpa only [hreg] using ht) y
  -- interior case `t₂ < 0`
  have hinterior : ∀ s : ℝ, t₁ ≤ s → s < 0 →
      (t₁ + T) * metricScalarAt (G t₁) x ≤ (s + T) * metricScalarAt (G s) x := by
    intro s h1s hs0
    have hshift : ∀ a : ℝ, -T < a → a < t₁ →
        (t₁ - a) * metricScalarAt (G t₁) x ≤ (s - a) * metricScalarAt (G s) x := by
      intro a ha hat
      have hregA : Icc a s ⊆ D.regular := by
        intro r hr
        rw [hreg]
        exact ⟨ha.trans_le hr.1, hr.2.trans_lt hs0⟩
      have hmono := hamilton_scalar_clock_monotoneOn (I := I3) S hGsol hcompS hcurv hconeS
        hat hregA x
      exact hmono ⟨le_rfl, h1s⟩ ⟨h1s, le_rfl⟩ h1s
    have hleft : Tendsto (fun a : ℝ => (t₁ - a) * metricScalarAt (G t₁) x)
        (𝓝[>] (-T)) (𝓝 ((t₁ + T) * metricScalarAt (G t₁) x)) := by
      have hc : Continuous (fun a : ℝ => (t₁ - a) * metricScalarAt (G t₁) x) :=
        (continuous_const.sub continuous_id).mul continuous_const
      simpa only [sub_neg_eq_add] using (hc.continuousAt (x := -T)).continuousWithinAt.tendsto
    have hright : Tendsto (fun a : ℝ => (s - a) * metricScalarAt (G s) x)
        (𝓝[>] (-T)) (𝓝 ((s + T) * metricScalarAt (G s) x)) := by
      have hc : Continuous (fun a : ℝ => (s - a) * metricScalarAt (G s) x) :=
        (continuous_const.sub continuous_id).mul continuous_const
      simpa only [sub_neg_eq_add] using (hc.continuousAt (x := -T)).continuousWithinAt.tendsto
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h₁)]
      with a ha hat
    exact hshift a ha hat
  rcases h₂.lt_or_eq with h2lt | h2eq
  · exact hinterior t₂ h12 h2lt
  · subst h2eq
    rcases h12.lt_or_eq with h1lt | h1eq
    · -- endpoint `t₂ = 0`：`s → 0⁻`
      have hcont : ContinuousOn (fun s : ℝ => metricScalarAt (G s) x) (Ioc (-T) 0) := by
        have hmap : Continuous (fun s : ℝ => (s, x)) := continuous_id.prodMk continuous_const
        have h := hGsol.scalarCont.comp hmap.continuousOn
          (fun s (hs : s ∈ Ioc (-T) (0 : ℝ)) => ⟨hs, mem_univ x⟩)
        exact h
      have hcw : ContinuousWithinAt (fun s : ℝ => metricScalarAt (G s) x) (Ioo (-T) 0) 0 :=
        (hcont 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩).mono Ioo_subset_Ioc_self
      have hlim : Tendsto (fun s : ℝ => (s + T) * metricScalarAt (G s) x)
          (𝓝[<] (0 : ℝ)) (𝓝 ((0 + T) * metricScalarAt (G 0) x)) := by
        have ht1 : Tendsto (fun s : ℝ => metricScalarAt (G s) x) (𝓝[<] (0 : ℝ))
            (𝓝 (metricScalarAt (G 0) x)) := by
          have h := hcw.tendsto
          rwa [nhdsWithin_Ioo_eq_nhdsLT (neg_lt_zero.mpr hT)] at h
        have ht2 : Tendsto (fun s : ℝ => s + T) (𝓝[<] (0 : ℝ)) (𝓝 (0 + T)) :=
          ((continuous_id.add continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
        exact ht2.mul ht1
      apply ge_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds h1lt)]
        with s hs0 hs1
      exact hinterior s hs1.le hs0
    · subst h1eq
      exact le_rfl

/-- 推论（零阶形）：`R(t, x) ≤ T·R(0, x)/(t + T)`，`t ∈ (-T, 0]`。 -/
theorem scalar_le_div_of_window_harnack_P6HK
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {T : ℝ} (hT : 0 < T)
    {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)))
    (hcomplete : ∀ t ∈ Ioo (-T) 0, RiemannianMetricComplete (G t))
    (hcone : ∀ t ∈ Ioo (-T) 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone)
    (hbd : ∀ a b : ℝ, Icc a b ⊆ Ioo (-T) 0 → ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x : P.M,
      metricScalarAt (G t) x ≤ C)
    {t : ℝ} (ht : t ∈ Ioc (-T) 0) (x : P.M) :
    metricScalarAt (G t) x ≤ T * metricScalarAt (G 0) x / (t + T) := by
  have hpos : 0 < t + T := by linarith [ht.1]
  have h := scalar_shift_mul_le_of_window_harnack_P6HK hT hGsol hcomplete hcone hbd
    ht.1 ht.2 le_rfl x
  rw [zero_add] at h
  rw [le_div_iff₀ hpos]
  linarith

/-- 推论（导数形，内部时刻）：`-R(t, x)/(t + T) ≤ ∂ₜR(t, x)`，`t ∈ (-T, 0)`。
证明 = §1 单调形（其底层 = 树内 `hamilton_trace_harnack` 的 clock 推论）+ 右差商极限。 -/
theorem neg_scalar_div_le_deriv_of_window_harnack_P6HK
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {T : ℝ} (hT : 0 < T)
    {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)))
    (hcomplete : ∀ t ∈ Ioo (-T) 0, RiemannianMetricComplete (G t))
    (hcone : ∀ t ∈ Ioo (-T) 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone)
    (hbd : ∀ a b : ℝ, Icc a b ⊆ Ioo (-T) 0 → ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x : P.M,
      metricScalarAt (G t) x ≤ C)
    {t : ℝ} (ht : t ∈ Ioo (-T) 0) (x : P.M) :
    -metricScalarAt (G t) x / (t + T) ≤ deriv (fun s : ℝ => metricScalarAt (G s) x) t := by
  have hpos : 0 < t + T := by linarith [ht.1]
  let D : RealTimeInterval := RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩
  have hreg : D.regular = Ioo (-T) 0 := rfl
  -- 由 §1 单调形：对 `s ∈ (t, 0)`，`(t+T)R(t) ≤ (s+T)R(s)`；对 `s ∈ (-T, t)`，`(s+T)R(s) ≤ (t+T)R(t)`。
  -- 于是 `φ(s) := (s + T)·R(s)` 在 `t` 可导且单调不减 ⇒ `φ'(t) ≥ 0`，`φ'(t) = R(t) + (t+T)·∂ₜR(t)`。
  have hdiff : HasDerivAt (fun s : ℝ => metricScalarAt (G s) x)
      (deriv (fun s : ℝ => metricScalarAt (G s) x) t) t := by
    have htr : t ∈ D.regular := by rw [hreg]; exact ht
    exact ((hGsol.scalarTime (K := D.carrier) (D.regular_subset htr) (fun _ hs => hs) x
      ).differentiableAt (D.regular_mem_nhds htr)).hasDerivAt
  have hφ : HasDerivAt (fun s : ℝ => (s + T) * metricScalarAt (G s) x)
      (1 * metricScalarAt (G t) x + (t + T) * deriv (fun s : ℝ => metricScalarAt (G s) x) t) t :=
    ((hasDerivAt_id t).add_const T).mul hdiff
  have hmono : MonotoneOn (fun s : ℝ => (s + T) * metricScalarAt (G s) x) (Ioo (-T) 0) := by
    intro a ha b hb hab
    exact scalar_shift_mul_le_of_window_harnack_P6HK hT hGsol hcomplete hcone hbd
      ha.1 hab hb.2.le x
  have hφnonneg : 0 ≤ 1 * metricScalarAt (G t) x +
      (t + T) * deriv (fun s : ℝ => metricScalarAt (G s) x) t := by
    apply ge_of_tendsto hφ.tendsto_slope_zero_right
    have hneg : 0 < -t := neg_pos.mpr ht.2
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hneg)]
      with h (hh : 0 < h) (hh' : h < -t)
    have hmem : t + h ∈ Ioo (-T) 0 := ⟨by linarith [ht.1], by linarith⟩
    have hle := hmono ht hmem (by linarith)
    rw [smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hh.le) (sub_nonneg.mpr hle)
  rw [div_le_iff₀ hpos]
  linarith

/-! ## §4 积分形距离漂移（I.8.3(b) 固定区间形 `riemannianEDistOf_le_add_of_endpoint_ricci_on_interval` 的
四进分段求和）：`R ≤ K/(t + T)` ⇒ `d_t ≤ d_0 + 24·√K·(√T − √(t + T))` -/

/-- 单步：`-T < a ≤ b ≤ 0`、`b + T ≤ 4(a + T)`，窗口上 `R ≤ K/(t + T)`、非负曲率算子、完备 ⇒
`d_a ≤ d_b + 24·√K·(√(b+T) − √(a+T))`（及 `[a, b]` 上距离有限）。`ℓ := √(a+T)/√K`。 -/
theorem edist_step_of_window_harnack_P6HK
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {T : ℝ} (hT : 0 < T)
    {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)))
    (hcomplete : ∀ t ∈ Ioc (-T) 0, RiemannianMetricComplete (G t))
    (hcone : ∀ t ∈ Ioo (-T) 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone)
    {K : ℝ} (hK : 0 < K)
    (hRK : ∀ t ∈ Ioo (-T) 0, ∀ x : P.M, metricScalarAt (G t) x ≤ K / (t + T))
    {a b : ℝ} (ha : -T < a) (hab : a ≤ b) (hb : b ≤ 0) (h4 : b + T ≤ 4 * (a + T))
    (p x : P.M) (hfin : riemannianEDistOf (G b) p x ≠ ⊤) :
    (∀ s ∈ Icc a b, riemannianEDistOf (G s) p x ≠ ⊤) ∧
      riemannianEDistOf (G a) p x ≤ riemannianEDistOf (G b) p x +
        ENNReal.ofReal (24 * Real.sqrt K * (Real.sqrt (b + T) - Real.sqrt (a + T))) := by
  let D : RealTimeInterval := RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩
  let S : SolutionOn (I := I3) (M := P.M) D := { base.metric := G }
  have hu : 0 < a + T := by linarith
  have hsu : 0 < Real.sqrt (a + T) := Real.sqrt_pos.mpr hu
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  set ℓ : ℝ := Real.sqrt (a + T) / Real.sqrt K with hℓdef
  have hℓ : 0 < ℓ := div_pos hsu hsK
  have hℓsq : ℓ ^ 2 = (a + T) / K := by
    rw [hℓdef, div_pow, Real.sq_sqrt hu.le, Real.sq_sqrt hK.le]
  have hcarrier : Icc a b ⊆ D.carrier := fun s hs => ⟨ha.trans_le hs.1, hs.2.trans hb⟩
  have hregular : Ioo a b ⊆ D.regular := fun s hs => ⟨ha.trans hs.1, hs.2.trans_le hb⟩
  have hcompl : ∀ s ∈ Icc a b, RiemannianMetricComplete (I := I3) (S.base.metric s) :=
    fun s hs => hcomplete s (hcarrier hs)
  have hRic : ∀ s ∈ Ioo a b, ∀ z : P.M, ∀ ξ : TangentSpace I3 z,
      (riemannianEDistOf (S.base.metric s) p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (S.base.metric s) x z < ENNReal.ofReal ℓ) →
      ricciTensor (S.base.metric s) z ξ ξ ≤ (3 / ℓ ^ 2) * (S.base.metric s).inner z ξ ξ := by
    intro s hs z ξ _
    have hsreg : s ∈ Ioo (-T) 0 := hregular hs
    have hst : a + T < s + T := by linarith [hs.1]
    have hRz : metricScalarAt (G s) z ≤ K / (a + T) :=
      (hRK s hsreg z).trans (div_le_div_of_nonneg_left hK.le hu hst.le)
    have hup := metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
      (G s) z (hcone s hsreg z) ξ
    rw [metricRicciAt_apply_eq_ricciTensor] at hup
    have hg : 0 ≤ (G s).inner z ξ ξ := metric_inner_self_nonneg (G s) z ξ
    have hcoef : metricScalarAt (G s) z / 2 ≤ 3 / ℓ ^ 2 := by
      rw [hℓsq, div_div_eq_mul_div]
      have hKu : 0 ≤ K / (a + T) := div_nonneg hK.le hu.le
      have h3 : 3 * K / (a + T) = 3 * (K / (a + T)) := by ring
      rw [h3]
      linarith
    exact hup.trans (mul_le_mul_of_nonneg_right hcoef hg)
  obtain ⟨hfinI, hdist⟩ := riemannianEDistOf_le_add_of_endpoint_ricci_on_interval
    (I := I3) S hGsol (by simp) hab hℓ hcarrier hregular hcompl p x hfin hRic
  refine ⟨hfinI, hdist.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))⟩
  -- `(8/ℓ)(b − a) ≤ 24·√K·(√(b+T) − √(a+T))`
  have hv : 0 ≤ b + T := by linarith
  have hsv0 : 0 ≤ Real.sqrt (b + T) := Real.sqrt_nonneg _
  have hsvu : Real.sqrt (a + T) ≤ Real.sqrt (b + T) := Real.sqrt_le_sqrt (by linarith)
  have hsv2 : Real.sqrt (b + T) ≤ 2 * Real.sqrt (a + T) := by
    rw [show (2 : ℝ) * Real.sqrt (a + T) = Real.sqrt (4 * (a + T)) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt h4
  have hba : b - a = Real.sqrt (b + T) ^ 2 - Real.sqrt (a + T) ^ 2 := by
    rw [Real.sq_sqrt hv, Real.sq_sqrt hu.le]; ring
  have h8 : 8 / ℓ = 8 * Real.sqrt K / Real.sqrt (a + T) := by
    rw [hℓdef]; field_simp
  rw [h8, hba, div_mul_eq_mul_div, div_le_iff₀ hsu]
  nlinarith [mul_nonneg (mul_nonneg hsK.le (sub_nonneg.mpr hsvu)) (by linarith : (0 : ℝ) ≤
    2 * Real.sqrt (a + T) - Real.sqrt (b + T))]

/-- 四进分段求和：窗口上 `R ≤ K/(t + T)` ⇒ `t ∈ (-T, 0]` 处
`d_t(p, x) ≤ d_0(p, x) + 24·√K·(√T − √(t + T)) ≤ d_0(p, x) + 24·√K·√T`（可积距离漂移）。 -/
theorem edist_le_add_of_window_harnack_P6HK
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {T : ℝ} (hT : 0 < T)
    {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)))
    (hcomplete : ∀ t ∈ Ioc (-T) 0, RiemannianMetricComplete (G t))
    (hcone : ∀ t ∈ Ioo (-T) 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone)
    {K : ℝ} (hK : 0 < K)
    (hRK : ∀ t ∈ Ioo (-T) 0, ∀ x : P.M, metricScalarAt (G t) x ≤ K / (t + T))
    (p x : P.M) (hfin : riemannianEDistOf (G 0) p x ≠ ⊤) {t : ℝ} (ht : t ∈ Ioc (-T) 0) :
    riemannianEDistOf (G t) p x ≤ riemannianEDistOf (G 0) p x +
      ENNReal.ofReal (24 * Real.sqrt K * Real.sqrt T) := by
  have hsK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  -- 不变式：`T/4^N ≤ s + T`、`s ≤ 0` ⇒ 有限 ∧ `d_s ≤ d_0 + 24√K(√T − √(s+T))`
  have key : ∀ N : ℕ, ∀ s : ℝ, T / 4 ^ N ≤ s + T → s ≤ 0 →
      riemannianEDistOf (G s) p x ≠ ⊤ ∧
        riemannianEDistOf (G s) p x ≤ riemannianEDistOf (G 0) p x +
          ENNReal.ofReal (24 * Real.sqrt K * (Real.sqrt T - Real.sqrt (s + T))) := by
    intro N
    induction N with
    | zero =>
      intro s hs hs0
      have hs' : s = 0 := le_antisymm hs0 (by simpa using hs)
      subst hs'
      refine ⟨hfin, ?_⟩
      simp
    | succ N ih =>
      intro s hs hs0
      have h4N : (0 : ℝ) < 4 ^ N := by positivity
      by_cases hcase : T / 4 ^ N ≤ s + T
      · exact ih s hcase hs0
      · replace hcase := not_le.mp hcase
        set b : ℝ := -T + T / 4 ^ N with hbdef
        have hbT : b + T = T / 4 ^ N := by rw [hbdef]; ring
        have hb0 : b ≤ 0 := by
          have : T / 4 ^ N ≤ T := div_le_self hT.le (one_le_pow₀ (by norm_num))
          linarith
        have hsb : s ≤ b := by linarith
        have hpos : 0 < T / 4 ^ (N + 1) := by positivity
        have hsT : -T < s := by linarith
        have h4 : b + T ≤ 4 * (s + T) := by
          have : T / 4 ^ N = 4 * (T / 4 ^ (N + 1)) := by
            rw [pow_succ]; field_simp
          linarith
        obtain ⟨hfb, hdb⟩ := ih b (by rw [hbT]) hb0
        obtain ⟨hfs, hds⟩ := edist_step_of_window_harnack_P6HK hT hGsol hcomplete hcone hK hRK
          hsT hsb hb0 h4 p x hfb
        refine ⟨hfs s ⟨le_rfl, hsb⟩, ?_⟩
        have hm1 : 0 ≤ 24 * Real.sqrt K * (Real.sqrt T - Real.sqrt (b + T)) :=
          mul_nonneg (by positivity) (sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith)))
        have hm2 : 0 ≤ 24 * Real.sqrt K * (Real.sqrt (b + T) - Real.sqrt (s + T)) :=
          mul_nonneg (by positivity) (sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith)))
        calc riemannianEDistOf (G s) p x
            ≤ riemannianEDistOf (G b) p x + ENNReal.ofReal
                (24 * Real.sqrt K * (Real.sqrt (b + T) - Real.sqrt (s + T))) := hds
          _ ≤ riemannianEDistOf (G 0) p x +
                ENNReal.ofReal (24 * Real.sqrt K * (Real.sqrt T - Real.sqrt (b + T))) +
                ENNReal.ofReal (24 * Real.sqrt K * (Real.sqrt (b + T) - Real.sqrt (s + T))) :=
              add_le_add hdb le_rfl
          _ = riemannianEDistOf (G 0) p x +
                ENNReal.ofReal (24 * Real.sqrt K * (Real.sqrt T - Real.sqrt (s + T))) := by
              rw [add_assoc, ← ENNReal.ofReal_add hm1 hm2]
              congr 2
              ring
  have htT : 0 < t + T := by linarith [ht.1]
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (T / (t + T)) (by norm_num : (1 : ℝ) < 4)
  have hN' : T / 4 ^ N ≤ t + T := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ htT] at hN
    linarith
  obtain ⟨_, hd⟩ := key N t hN' ht.2
  refine hd.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have : 0 ≤ Real.sqrt (t + T) := Real.sqrt_nonneg _
  nlinarith

/-! ## §2 driver 窗口极限上的有限年龄 Harnack（window 引理前提逐字） -/

/-- `exists_uniform_scalar_bound_of_local_flow_limit_on_window` 的**同一组前提（逐字）** ⇒ 其结论（标量界 `C`）
∧ 极限流 `G` 上有限年龄迹 Harnack（年龄原点 `t* = -T`）的单调形、零阶形 `R ≤ T·R(0)/(t+T)`、导数形
`∂ₜR ≥ -R/(t+T)`。非负曲率算子 / 完备性按 window 引理证明体的前两步（逐字）。无新 binder。 -/
theorem harnack_window_limit_P6HK
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F)
    (hcan : ∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hPc : MetricComplete P) (hconn : ConnectedSpace P.M) {V : ℕ → TopologicalSpace.Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} (hVF : ∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j)
    {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    (hWF : ∀ k, ∀ᶠ j in atTop, ((W k (f j) : Set (X.obj (f j)).M)) ⊆ F.target j)
    {T : ℝ} (hT : 0 < T) {c τ : ℕ → ℝ} (hτ : ∀ k, 0 < τ k) (hcτ : ∀ k, c k < τ k)
    (hcmono : Monotone c) (hcT : ∀ s ∈ Ioc (-T) 0, ∃ k, -c k < s)
    {G : ℝ → SmoothRiemannianMetric I3 P.M} (hG0 : G 0 = P.metric)
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-c k) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I3) (M := W k n)
        (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le))))
    {Q : ℕ → ℝ} (hQ : Tendsto Q atTop atTop) {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-c k) 0, ∀ x : W k n,
      curvatureOperatorLowerBoundAt (h k n t) x (metricAlgebraicCurvatureTensorAt (h k n t) x)
        (Perelman.rescalePinchingFunction (Q n) Phi (metricScalarAt (h k n t) x)))
    (hLip : ∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-c k) 0,
      ∀ σ' ∈ Icc (-c k) 0,
        ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|)
    {E : ℕ → Set ℝ} {ζ : ℕ → ℝ} (hζ : Tendsto ζ atTop (𝓝 0))
    (hE : ∀ n, (E n \ Icc (-(ζ n)) 0).Finite)
    {eps qW C2 qD Ctime κ : ℝ} (heps : eps ≤ crossingWindowNeckAccuracy.{u}) (hC2 : 1 ≤ C2)
    (hκ : 0 < κ)
    (hW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, s ∉ E n → ∀ z : W k n,
      (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
      qW < metricScalarAt (h k n s) z →
      Nonempty (SpatialNeck (h k n s) eps z) ∨
        (∃ w : W k n, Nonempty (SpatialNeck (h k n s) eps w) ∧
          metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
          metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
          riemannianEDistOf (h k n s) z w <
            ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
        IsCompact (connectedComponent z))
    (hderiv : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-τ k) 0, s ∉ E n →
      ∀ z : W k n, qD < metricScalarAt (h k n s) z →
        |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
          Ctime * metricScalarAt (h k n s) z ^ 2)
    (hpar : (∀ t ∈ Ioc (-T) 0, RiemannianMetricComplete (G t)) →
      Perelman.ParabolicallyKappaNoncollapsedBelowScale ({ base.metric := G } :
        SolutionOn (I := I3) (M := P.M)
          (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) κ 1)
    (happrox : ∀ A Dd : ℝ, ∃ C : ℝ, ∀ k : ℕ, ∀ τ ∈ Icc (-c k) 0, τ < 0 → ∀ᶠ n in atTop,
      ∀ z x : W k n, metricScalarAt (h k n τ) z ≤ A →
        riemannianEDistOf (h k n τ) z x < ENNReal.ofReal Dd →
        metricScalarAt (h k n τ) x ≤ C) :
    ∃ C : ℝ, (∀ t ∈ Ioc (-T) 0, ∀ x : P.M, metricScalarAt (G t) x ≤ C) ∧
      (∀ t₁ t₂ : ℝ, -T < t₁ → t₁ ≤ t₂ → t₂ ≤ 0 → ∀ x : P.M,
        (t₁ + T) * metricScalarAt (G t₁) x ≤ (t₂ + T) * metricScalarAt (G t₂) x) ∧
      (∀ t ∈ Ioc (-T) 0, ∀ x : P.M,
        metricScalarAt (G t) x ≤ T * metricScalarAt (G 0) x / (t + T)) ∧
      (∀ t ∈ Ioo (-T) 0, ∀ x : P.M,
        -metricScalarAt (G t) x / (t + T) ≤ deriv (fun s : ℝ => metricScalarAt (G s) x) t) := by
  obtain ⟨C, hC⟩ := exists_uniform_scalar_bound_of_local_flow_limit_on_window hf F Cd hcan hPc
    hconn hV hVF hφF hWF hT hτ hcτ hcmono hcT hG0 hGsol hψ hconv hsol hQ hPhi hpinch hLip hζ hE
    heps hC2 hκ hW hderiv hpar happrox
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  have hcone := curvatureOperator_nonnegative_of_local_pinching_limit_on_window hf hVmono hVcover
    hcmono hcT hψ hconv hQ hPhi hpinch
  have hcompl0 : RiemannianMetricComplete (G 0) := by
    rw [hG0]
    exact ⟨CheegerGromovCompactness.MetricComplete.complete P hPc⟩
  have hcomplete : ∀ t ∈ Ioc (-T) 0, RiemannianMetricComplete (G t) := fun t ht =>
    complete_at_earlier_time_of_ricci_nonnegative
      ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
        (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) hGsol
      (a := t) (b := 0) (fun r hr => ⟨ht.1.trans_le hr.1, hr.2⟩)
      (fun r hr => ⟨ht.1.trans hr.1, hr.2⟩)
      (fun r hr x v => metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
        (G r) x (hcone r ⟨ht.1.trans hr.1, hr.2.le⟩ x) v) hcompl0 ⟨le_rfl, ht.2⟩
  have hcompI : ∀ t ∈ Ioo (-T) 0, RiemannianMetricComplete (G t) :=
    fun t ht => hcomplete t (Ioo_subset_Ioc_self ht)
  have hconeI : ∀ t ∈ Ioo (-T) 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone :=
    fun t ht x => hcone t (Ioo_subset_Ioc_self ht) x
  have hbd : ∀ a b : ℝ, Icc a b ⊆ Ioo (-T) 0 → ∃ C' : ℝ, ∀ t ∈ Icc a b, ∀ x : P.M,
      metricScalarAt (G t) x ≤ C' :=
    fun a b hab => ⟨C, fun t ht x => hC t (Ioo_subset_Ioc_self (hab ht)) x⟩
  exact ⟨C, hC,
    fun t₁ t₂ h₁ h12 h₂ x =>
      scalar_shift_mul_le_of_window_harnack_P6HK hT hGsol hcompI hconeI hbd h₁ h12 h₂ x,
    fun t ht x => scalar_le_div_of_window_harnack_P6HK hT hGsol hcompI hconeI hbd ht x,
    fun t ht x => neg_scalar_div_le_deriv_of_window_harnack_P6HK hT hGsol hcompI hconeI hbd ht x⟩

/-! ## §2′ driver 窗口极限上的可积距离漂移（window 引理前提逐字） -/

/-- window 引理同一组前提（逐字）⇒ 原结论 ∧ 极限流上 `d_t ≤ d_0 + 24·√(T·max C 1)·√T`（`t ∈ (-T, 0]`，
`d_0` 有限的点对）：§1 零阶 Harnack `R ≤ T·C/(t+T)` + §4 四进求和。无新 binder。 -/
theorem drift_window_limit_P6HK
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F)
    (hcan : ∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hPc : MetricComplete P) (hconn : ConnectedSpace P.M) {V : ℕ → TopologicalSpace.Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} (hVF : ∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j)
    {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    (hWF : ∀ k, ∀ᶠ j in atTop, ((W k (f j) : Set (X.obj (f j)).M)) ⊆ F.target j)
    {T : ℝ} (hT : 0 < T) {c τ : ℕ → ℝ} (hτ : ∀ k, 0 < τ k) (hcτ : ∀ k, c k < τ k)
    (hcmono : Monotone c) (hcT : ∀ s ∈ Ioc (-T) 0, ∃ k, -c k < s)
    {G : ℝ → SmoothRiemannianMetric I3 P.M} (hG0 : G 0 = P.metric)
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-c k) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I3) (M := W k n)
        (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le))))
    {Q : ℕ → ℝ} (hQ : Tendsto Q atTop atTop) {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-c k) 0, ∀ x : W k n,
      curvatureOperatorLowerBoundAt (h k n t) x (metricAlgebraicCurvatureTensorAt (h k n t) x)
        (Perelman.rescalePinchingFunction (Q n) Phi (metricScalarAt (h k n t) x)))
    (hLip : ∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-c k) 0,
      ∀ σ' ∈ Icc (-c k) 0,
        ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|)
    {E : ℕ → Set ℝ} {ζ : ℕ → ℝ} (hζ : Tendsto ζ atTop (𝓝 0))
    (hE : ∀ n, (E n \ Icc (-(ζ n)) 0).Finite)
    {eps qW C2 qD Ctime κ : ℝ} (heps : eps ≤ crossingWindowNeckAccuracy.{u}) (hC2 : 1 ≤ C2)
    (hκ : 0 < κ)
    (hW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, s ∉ E n → ∀ z : W k n,
      (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
      qW < metricScalarAt (h k n s) z →
      Nonempty (SpatialNeck (h k n s) eps z) ∨
        (∃ w : W k n, Nonempty (SpatialNeck (h k n s) eps w) ∧
          metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
          metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
          riemannianEDistOf (h k n s) z w <
            ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
        IsCompact (connectedComponent z))
    (hderiv : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-τ k) 0, s ∉ E n →
      ∀ z : W k n, qD < metricScalarAt (h k n s) z →
        |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
          Ctime * metricScalarAt (h k n s) z ^ 2)
    (hpar : (∀ t ∈ Ioc (-T) 0, RiemannianMetricComplete (G t)) →
      Perelman.ParabolicallyKappaNoncollapsedBelowScale ({ base.metric := G } :
        SolutionOn (I := I3) (M := P.M)
          (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) κ 1)
    (happrox : ∀ A Dd : ℝ, ∃ C : ℝ, ∀ k : ℕ, ∀ τ ∈ Icc (-c k) 0, τ < 0 → ∀ᶠ n in atTop,
      ∀ z x : W k n, metricScalarAt (h k n τ) z ≤ A →
        riemannianEDistOf (h k n τ) z x < ENNReal.ofReal Dd →
        metricScalarAt (h k n τ) x ≤ C) :
    ∃ C : ℝ, (∀ t ∈ Ioc (-T) 0, ∀ x : P.M, metricScalarAt (G t) x ≤ C) ∧
      ∀ p x : P.M, riemannianEDistOf (G 0) p x ≠ ⊤ → ∀ t ∈ Ioc (-T) 0,
        riemannianEDistOf (G t) p x ≤ riemannianEDistOf (G 0) p x +
          ENNReal.ofReal (24 * Real.sqrt (T * max C 1) * Real.sqrt T) := by
  obtain ⟨C, hC, -, hdiv, -⟩ := harnack_window_limit_P6HK hf F Cd hcan hPc hconn hV hVF hφF hWF hT
    hτ hcτ hcmono hcT hG0 hGsol hψ hconv hsol hQ hPhi hpinch hLip hζ hE heps hC2 hκ hW hderiv hpar
    happrox
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  have hcone := curvatureOperator_nonnegative_of_local_pinching_limit_on_window hf hVmono hVcover
    hcmono hcT hψ hconv hQ hPhi hpinch
  have hcompl0 : RiemannianMetricComplete (G 0) := by
    rw [hG0]
    exact ⟨CheegerGromovCompactness.MetricComplete.complete P hPc⟩
  have hcomplete : ∀ t ∈ Ioc (-T) 0, RiemannianMetricComplete (G t) := fun t ht =>
    complete_at_earlier_time_of_ricci_nonnegative
      ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
        (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) hGsol
      (a := t) (b := 0) (fun r hr => ⟨ht.1.trans_le hr.1, hr.2⟩)
      (fun r hr => ⟨ht.1.trans hr.1, hr.2⟩)
      (fun r hr x v => metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
        (G r) x (hcone r ⟨ht.1.trans hr.1, hr.2.le⟩ x) v) hcompl0 ⟨le_rfl, ht.2⟩
  have hconeI : ∀ t ∈ Ioo (-T) 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone :=
    fun t ht x => hcone t (Ioo_subset_Ioc_self ht) x
  have hK : 0 < T * max C 1 := mul_pos hT (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hRK : ∀ t ∈ Ioo (-T) 0, ∀ x : P.M,
      metricScalarAt (G t) x ≤ T * max C 1 / (t + T) := by
    intro t ht x
    have htT : 0 < t + T := by linarith [ht.1]
    refine (hdiv t (Ioo_subset_Ioc_self ht) x).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hT.le) htT.le)
    exact (hC 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩ x).trans (le_max_left _ _)
  exact ⟨C, hC, fun p x hfin t ht =>
    edist_le_add_of_window_harnack_P6HK hT hGsol hcomplete hconeI hK hRK p x hfin ht⟩

/-! ## §3 形状对齐 -/

/-- 消费点对齐：新定理的第一个合取 = window 引理结论逐字（同一组前提 ⇒ 旧结论）。 -/
example
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F)
    (hcan : ∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hPc : MetricComplete P) (hconn : ConnectedSpace P.M) {V : ℕ → TopologicalSpace.Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} (hVF : ∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j)
    {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    (hWF : ∀ k, ∀ᶠ j in atTop, ((W k (f j) : Set (X.obj (f j)).M)) ⊆ F.target j)
    {T : ℝ} (hT : 0 < T) {c τ : ℕ → ℝ} (hτ : ∀ k, 0 < τ k) (hcτ : ∀ k, c k < τ k)
    (hcmono : Monotone c) (hcT : ∀ s ∈ Ioc (-T) 0, ∃ k, -c k < s)
    {G : ℝ → SmoothRiemannianMetric I3 P.M} (hG0 : G 0 = P.metric)
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-c k) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I3) (M := W k n)
        (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le))))
    {Q : ℕ → ℝ} (hQ : Tendsto Q atTop atTop) {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-c k) 0, ∀ x : W k n,
      curvatureOperatorLowerBoundAt (h k n t) x (metricAlgebraicCurvatureTensorAt (h k n t) x)
        (Perelman.rescalePinchingFunction (Q n) Phi (metricScalarAt (h k n t) x)))
    (hLip : ∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-c k) 0,
      ∀ σ' ∈ Icc (-c k) 0,
        ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|)
    {E : ℕ → Set ℝ} {ζ : ℕ → ℝ} (hζ : Tendsto ζ atTop (𝓝 0))
    (hE : ∀ n, (E n \ Icc (-(ζ n)) 0).Finite)
    {eps qW C2 qD Ctime κ : ℝ} (heps : eps ≤ crossingWindowNeckAccuracy.{u}) (hC2 : 1 ≤ C2)
    (hκ : 0 < κ)
    (hW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, s ∉ E n → ∀ z : W k n,
      (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
      qW < metricScalarAt (h k n s) z →
      Nonempty (SpatialNeck (h k n s) eps z) ∨
        (∃ w : W k n, Nonempty (SpatialNeck (h k n s) eps w) ∧
          metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
          metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
          riemannianEDistOf (h k n s) z w <
            ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
        IsCompact (connectedComponent z))
    (hderiv : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-τ k) 0, s ∉ E n →
      ∀ z : W k n, qD < metricScalarAt (h k n s) z →
        |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
          Ctime * metricScalarAt (h k n s) z ^ 2)
    (hpar : (∀ t ∈ Ioc (-T) 0, RiemannianMetricComplete (G t)) →
      Perelman.ParabolicallyKappaNoncollapsedBelowScale ({ base.metric := G } :
        SolutionOn (I := I3) (M := P.M)
          (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) κ 1)
    (happrox : ∀ A Dd : ℝ, ∃ C : ℝ, ∀ k : ℕ, ∀ τ ∈ Icc (-c k) 0, τ < 0 → ∀ᶠ n in atTop,
      ∀ z x : W k n, metricScalarAt (h k n τ) z ≤ A →
        riemannianEDistOf (h k n τ) z x < ENNReal.ofReal Dd →
        metricScalarAt (h k n τ) x ≤ C) :
    ∃ C : ℝ, ∀ t ∈ Ioc (-T) 0, ∀ x : P.M, metricScalarAt (G t) x ≤ C := by
  exact Exists.imp (fun _ h => h.1) (harnack_window_limit_P6HK hf F Cd hcan hPc hconn hV hVF hφF
    hWF hT hτ hcτ hcmono hcT hG0 hGsol hψ hconv hsol hQ hPhi hpinch hLip hζ hE heps hC2 hκ hW
    hderiv hpar happrox)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
