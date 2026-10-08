import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalEndComparison
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ScalarRescaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.ConeExclusion
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative

/-!
# O-CH11-SPINE-IFACE G2：punctured cone → local flow → exclusion 的史无关桥（后缀 `_C11SP`）

只 import 树内 tracked 模块。三件桥引理，都是 CODEX-C §3.3 路线 2–3 的 binder 付款（不含任何 history 输入）：

* `secLower_zero_of_nonnegCone_C11SP` / `…_flow_C11SP`：exclusion 核心
  `solution_not_rescaled_cone_limit`
  （`Compactness/ConeExclusion.lean:22`）的
  `hsec : ∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ`
  ⇐ 局部 flow 输出的 curvature operator 非负（P6L:739–746 的 inline 转换抽成定理）。
* `tendsto_time_mul_scale_C11SP`：WIP `exists_prepared_stage_local_flow_CXSP` 的 `t·R → ∞`
  binder（`hage`）
  ⇐ 原坏序列自己的 `r/√t → 0`、物理尺度 `R = H0·r⁻²·q`、`q ≥ 1`（二次 blow-up 的 rescaled scalar）。
* `exists_secondBlowup_comparison_C11SP` + consumer `exists_local_flow_at_cone_points_C11SP`：
  cone 端点列
  `xW` 经一次 blow-up 的 convergence data（`X f Pl maps conv hcanonical`）拉回原 stage，给出**二次 blow-up 源序列**
  `X₂`（物理尺度 `q·Q`）与 comparison `B n = inc ∘ maps.pd (k n)`，付清树内
  `exists_nonnegative_local_flow_with_end_comparison`
  （`Compactness/Limits/LocalEndComparison.lean:31`）的
  `Hn / x / B / hBsource / hBbase / hcapture / hBconv` 七个 binder；consumer 的结论 =
  A2 `flow-binder-form.txt` (II)
  的 flow + comparison 形（`j, g, IsSolutionOn, nonneg cone, r, compact, cover, dist`）。
  **剩余 binder = flow 侧**（`F₂ C₂ hcanonical₂ V hsource S hS hterminal hcurv hpinching`：X₂ 沿 `f₂` 的收敛与
  固定 `V` 上的 pulled-back flows），由 G45/G59 + WIP kernel 在 `X₂` 上生产（A1-G2 的义务，见 state 的对照表）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-! ## (1′) exclusion 侧 hsec -/

/-- curvature operator 非负 ⇒ `SecLower g 0 univ`（`solution_not_rescaled_cone_limit` 的 hsec 形）。 -/
theorem secLower_zero_of_nonnegCone_C11SP {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I3 M)
    (h : ∀ z : M, metricAlgebraicCurvatureTensorAt g z ∈
      algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) :
    SecLower g 0 univ := by
  intro z _ v w
  have hz := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
    g z (by simp [ThreeSpace])).mp (h z) v w
  have hslots : (fun i => ![v, w, w, v] i) = vec4 (I := ThreeModel) v w w v := by
    funext i
    fin_cases i <;> rfl
  simpa only [zero_mul, metricRm04StandardAt_apply, hslots] using hz

/-- 时间层版本：局部 flow 输出 `∀ t ∈ Icc (-tau) 0, ∀ y, Rm(g t) y ∈ cone` ⇒ exclusion 的 `hsec`。 -/
theorem secLower_zero_of_nonnegCone_flow_C11SP {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    {tau : ℝ} (g : ℝ → SmoothRiemannianMetric I3 M)
    (h : ∀ t ∈ Icc (-tau) 0, ∀ y : M, metricAlgebraicCurvatureTensorAt (g t) y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) :
    ∀ t ∈ Icc (-tau) 0, SecLower (g t) 0 univ :=
  fun t ht => secLower_zero_of_nonnegCone_C11SP (g t) (h t ht)

/-! ## (2a) local flow 的 `t·R → ∞` binder -/

/-- 原坏序列 `r/√t → 0` ⇒ 二次 blow-up 物理尺度 `R = H0·r⁻²·q`（`q ≥ 1`）下 `t·R → ∞`。 -/
theorem tendsto_time_mul_scale_C11SP {t r q : ℕ → ℝ} {H0 : ℝ} (hH0 : 0 < H0)
    (hr : ∀ n, 0 < r n) (ht : ∀ n, 0 < t n) (hq : ∀ n, 1 ≤ q n)
    (hratio : Tendsto (fun n => r n / Real.sqrt (t n)) atTop (𝓝 0)) :
    Tendsto (fun n => t n * (H0 * (r n ^ 2)⁻¹ * q n)) atTop atTop := by
  have hu0 : Tendsto (fun n => (r n / Real.sqrt (t n)) ^ 2) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using hratio.pow 2
    · exact pow_pos (div_pos (hr n) (Real.sqrt_pos.mpr (ht n))) 2
  have hinv := (tendsto_inv_nhdsGT_zero.comp hu0).const_mul_atTop hH0
  refine tendsto_atTop_mono (fun n => ?_) hinv
  have hsq : Real.sqrt (t n) ^ 2 = t n := Real.sq_sqrt (ht n).le
  have hr2 : 0 < r n ^ 2 := pow_pos (hr n) 2
  have heq : ((r n / Real.sqrt (t n)) ^ 2)⁻¹ = t n * (r n ^ 2)⁻¹ := by
    rw [div_pow, hsq, inv_div, div_eq_mul_inv]
  change H0 * ((r n / Real.sqrt (t n)) ^ 2)⁻¹ ≤ t n * (H0 * (r n ^ 2)⁻¹ * q n)
  rw [heq]
  have hpos : 0 ≤ t n * (H0 * (r n ^ 2)⁻¹) :=
    mul_nonneg (ht n).le (mul_nonneg hH0.le (inv_nonneg.mpr hr2.le))
  nlinarith [hq n]

/-! ## (2d) F8 的对角支付：慢重索引 -/

/-- **慢重索引（PROVED，纯 ℕ/ℝ）**：任意门槛 `T : ℕ → ℝ`（如 G43 traced region 的 `T₀(L)` 在第 `m` 个
cone 点的整数 level 处的值）与 `s → ∞`（如一次 blow-up 沿 `f` 的原时间 `t (f i)`），存在 `σ → ∞` 使
最终 `∀ i ≥ n, T (σ n) ≤ s i`。用法：cone 点换成 `x ∘ σ`（仍 → qW、scalar → ∞），任意 StrictMono 对角 `k`
（`k n ≥ n`）上 `T (σ n) ≤ t (f (k n))`——即 CODEX-C F8 在实际 selection 里支付，不由 `t → ∞` 直接认领。 -/
theorem exists_slow_reindex_C11SP (T : ℕ → ℝ) {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) :
    ∃ σ : ℕ → ℕ, Tendsto σ atTop atTop ∧ ∀ᶠ n in atTop, ∀ i, n ≤ i → T (σ n) ≤ s i := by
  classical
  have hN : ∀ m, ∃ N : ℕ, ∀ i, N ≤ i → T m ≤ s i := fun m =>
    eventually_atTop.mp (hs.eventually_ge_atTop (T m))
  let N : ℕ → ℕ := fun m => Nat.find (hN m)
  have hNspec : ∀ m i, N m ≤ i → T m ≤ s i := fun m => Nat.find_spec (hN m)
  let σ : ℕ → ℕ := fun n => Nat.findGreatest (fun m => N m ≤ n) n
  refine ⟨σ, tendsto_atTop.mpr fun m₀ => ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (max m₀ (N m₀))] with n hn
    exact Nat.le_findGreatest ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn i hi
    have hσ : N (σ n) ≤ n := Nat.findGreatest_spec (P := fun m => N m ≤ n) (Nat.zero_le n) hn
    exact hNspec _ _ (hσ.trans hi)

/-- 用法形：对任意 StrictMono 对角 `k`，最终 `T (σ n) ≤ s (k n)`。 -/
theorem slow_reindex_le_of_strictMono_C11SP {T s : ℕ → ℝ} {σ : ℕ → ℕ}
    (h : ∀ᶠ n in atTop, ∀ i, n ≤ i → T (σ n) ≤ s i) {k : ℕ → ℕ} (hk : StrictMono k) :
    ∀ᶠ n in atTop, T (σ n) ≤ s (k n) := by
  filter_upwards [h] with n hn
  exact hn (k n) (hk.id_le n)

/-! ## (2c) 二次 blow-up 源度量与 WIP local flow 的 `X` 形对齐 -/

/-- `q · (Q · g) = (q·Q) · g`（等式，非仅 inner）：二次 blow-up 源序列 `X₂` 的度量
`scaleMetric (q n) (scaleMetric Q g)` 与 WIP `exists_prepared_stage_local_flow_CXSP` 的
`scaleMetric (R n) g`（`R n = q n · Q`）对齐用。 -/
theorem scaleMetric_scaleMetric_eq_C11SP {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    scaleMetric a ha (scaleMetric b hb g) = scaleMetric (a * b) (mul_pos ha hb) g := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  simp only [scaleMetric_inner]
  ring

/-! ## (2b) cone 端点 → 二次 blow-up 源序列与 comparison -/

private theorem inner_self_nonneg_C11SP {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (y : M)
    (v : TangentSpace ThreeModel y) : 0 ≤ g.inner y v v := by
  by_cases hv : v = 0
  · subst hv
    simp
  · exact (g.pos y v hv).le

/-- **(2b) PROVED**：cone 端点列 `x : ℕ → W`（`W ⊆ L`、`R(x n) ≥ 2`、`4R/√R(x n)` 闭球紧）+ 一次 blow-up 的
convergence data ⇒ 对角 `k`、rescaled scalar `q n`（`q n / R_L(x n) → 1`）、
comparison `B n : W → X.obj (f (k n))`，
满足 `exists_nonnegative_local_flow_with_end_comparison` 的 source / capture / `(1 ± η)` 度量比较 binder
（`Hn n = q n · g_L|W`，二次源度量 `q n · (X.obj (f (k n))).metric`，基点 `B n (x n)`）。 -/
theorem exists_secondBlowup_comparison_C11SP
    (X : PointedRiemannianSeq.{u, 0, 0} ThreeModel) (f : ℕ → ℕ)
    (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (maps : PointedRiemannianConvergenceMaps X L f) (conv : MetricConvergenceData maps)
    (hcanonical : ∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i)
    (W : TopologicalSpace.Opens L.M) (x : ℕ → W) {R : ℝ} (hR : 0 < R)
    (hQ : ∀ n, 2 ≤ metricScalarAt L.metric (x n : L.M))
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf (L.metric.restrictOpen W) (x n)
      (4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M))))) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ q : ℕ → ℝ, ∃ hq : ∀ n, 0 < q n, (∀ n, 1 ≤ q n) ∧
      Tendsto (fun n => q n / metricScalarAt L.metric (x n : L.M)) atTop (𝓝 1) ∧
      ∃ B : ∀ n, PartialDiffeomorph ThreeModel ThreeModel W (X.obj (f (k n))).M ∞,
        (∀ n, riemannianClosedBallOf (scaleMetric (q n) (hq n) (L.metric.restrictOpen W))
          (x n) R ⊆ (B n).source) ∧
        (∀ n, riemannianClosedBallOf (scaleMetric (q n) (hq n) (X.obj (f (k n))).metric)
          (B n (x n)) (R / 4) ⊆
            (B n) '' riemannianClosedBallOf (scaleMetric (q n) (hq n) (L.metric.restrictOpen W))
              (x n) R) ∧
        ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
          ∀ y ∈ riemannianClosedBallOf (scaleMetric (q n) (hq n) (L.metric.restrictOpen W))
            (x n) R, ∀ v : TangentSpace ThreeModel y,
            (1 - eta) * (scaleMetric (q n) (hq n) (L.metric.restrictOpen W)).inner y v v ≤
              (scaleMetric (q n) (hq n) (X.obj (f (k n))).metric).inner (B n y)
                (mfderiv ThreeModel ThreeModel (B n) y v)
                (mfderiv ThreeModel ThreeModel (B n) y v) ∧
            (scaleMetric (q n) (hq n) (X.obj (f (k n))).metric).inner (B n y)
                (mfderiv ThreeModel ThreeModel (B n) y v)
                (mfderiv ThreeModel ThreeModel (B n) y v) ≤
              (1 + eta) * (scaleMetric (q n) (hq n) (L.metric.restrictOpen W)).inner y v v := by
  have hcmp := exists_scalar_rescaled_source_comparison X f L maps conv hcanonical W x hR hQ
    hcompact
  obtain ⟨k, hk, hq1, hrest⟩ := hcmp
  let q : ℕ → ℝ := fun n => metricScalarAt (X.obj (f (k n))).metric
    (maps.partialDiffeomorph (k n) (x n : L.M))
  have hqpos : ∀ n, 0 < q n := fun n => lt_of_lt_of_le zero_lt_one (hq1 n)
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := ThreeModel) W
    ⟨x 0⟩
  refine ⟨k, hk, q, hqpos, hq1, hrest.1, fun n => inc.trans (maps.partialDiffeomorph (k n)),
    fun n => (hrest.2 n).2.1, fun n => (hrest.2 n).2.2.2.1, fun eta heta => ?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 2) ≤ eta := by
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      squeeze_zero (fun n => by positivity)
        (fun n => one_div_le_one_div_of_le (by positivity) (by linarith))
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact hlim.eventually (ge_mem_nhds heta)
  filter_upwards [hsmall] with n hn y hy v
  have hb := ((hrest.2 n).2.2.1 y hy v)
  have h0 := inner_self_nonneg_C11SP
    (scaleMetric (q n) (hqpos n) (L.metric.restrictOpen W)) y v
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) h0) hb.1
  · exact le_trans hb.2 (mul_le_mul_of_nonneg_right (by linarith) h0)

/-- **(2d) consumer = F8 支付后的二次 blow-up comparison**：cone 点换成慢重索引 `x ∘ σ`，对角 `k` 上
门槛 `T (σ n) ≤ s (f (k n))`（`s` = 一次 blow-up 源序列的原时间），comparison 子句与
`exists_secondBlowup_comparison_C11SP` 相同（对 `x ∘ σ`）。 -/
theorem exists_slow_secondBlowup_comparison_C11SP
    (X : PointedRiemannianSeq.{u, 0, 0} ThreeModel) (f : ℕ → ℕ)
    (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (maps : PointedRiemannianConvergenceMaps X L f) (conv : MetricConvergenceData maps)
    (hcanonical : ∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i)
    (W : TopologicalSpace.Opens L.M) (x : ℕ → W) {R : ℝ} (hR : 0 < R)
    (hQ : ∀ n, 2 ≤ metricScalarAt L.metric (x n : L.M))
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf (L.metric.restrictOpen W) (x n)
      (4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M)))))
    (T : ℕ → ℝ) {s : ℕ → ℝ} (hs : Tendsto (fun i => s (f i)) atTop atTop) :
    ∃ σ : ℕ → ℕ, Tendsto σ atTop atTop ∧
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ᶠ n in atTop, T (σ n) ≤ s (f (k n))) ∧
    ∃ q : ℕ → ℝ, ∃ hq : ∀ n, 0 < q n, (∀ n, 1 ≤ q n) ∧
      Tendsto (fun n => q n / metricScalarAt L.metric (x (σ n) : L.M)) atTop (𝓝 1) ∧
      ∃ B : ∀ n, PartialDiffeomorph ThreeModel ThreeModel W (X.obj (f (k n))).M ∞,
        (∀ n, riemannianClosedBallOf (scaleMetric (q n) (hq n) (L.metric.restrictOpen W))
          (x (σ n)) R ⊆ (B n).source) ∧
        (∀ n, riemannianClosedBallOf (scaleMetric (q n) (hq n) (X.obj (f (k n))).metric)
          (B n (x (σ n))) (R / 4) ⊆
            (B n) '' riemannianClosedBallOf (scaleMetric (q n) (hq n) (L.metric.restrictOpen W))
              (x (σ n)) R) ∧
        ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
          ∀ y ∈ riemannianClosedBallOf (scaleMetric (q n) (hq n) (L.metric.restrictOpen W))
            (x (σ n)) R, ∀ v : TangentSpace ThreeModel y,
            (1 - eta) * (scaleMetric (q n) (hq n) (L.metric.restrictOpen W)).inner y v v ≤
              (scaleMetric (q n) (hq n) (X.obj (f (k n))).metric).inner (B n y)
                (mfderiv ThreeModel ThreeModel (B n) y v)
                (mfderiv ThreeModel ThreeModel (B n) y v) ∧
            (scaleMetric (q n) (hq n) (X.obj (f (k n))).metric).inner (B n y)
                (mfderiv ThreeModel ThreeModel (B n) y v)
                (mfderiv ThreeModel ThreeModel (B n) y v) ≤
              (1 + eta) * (scaleMetric (q n) (hq n) (L.metric.restrictOpen W)).inner y v v := by
  obtain ⟨σ, hσ, hT⟩ := exists_slow_reindex_C11SP T hs
  obtain ⟨k, hk, q, hq, hq1, hratio, B, hsrc, hcap, hconv⟩ :=
    exists_secondBlowup_comparison_C11SP X f L maps conv hcanonical W (fun n => x (σ n)) hR
      (fun n => hQ (σ n)) (fun n => hcompact (σ n))
  exact ⟨σ, hσ, k, hk, slow_reindex_le_of_strictMono_C11SP hT hk, q, hq, hq1, hratio, B, hsrc,
    hcap, hconv⟩

/-- **(2b) consumer = cone 端点处局部 flow 接口（INTEGRATION-ONLY；flow 侧 binder 显式）**：在
`exists_secondBlowup_comparison_C11SP` 的 `k q B` 上定义二次 blow-up 源序列 `X₂`（基点 `B n (x n)`、度量
`q n · (X.obj (f (k n))).metric`），则对 `X₂` 沿任意 `f₂` 的收敛数据与固定 `V` 上的 pulled-back flows
（flow 侧 binder，A1-G2 的义务），树内 `exists_nonnegative_local_flow_with_end_comparison` 直接给出
A2 (II) 形的局部反向非负 flow + comparison（`Hn = q·g_L|W`、端点列 `x ∘ f₂`）。 -/
theorem exists_local_flow_at_cone_points_C11SP
    (X : PointedRiemannianSeq.{u, 0, 0} ThreeModel) (f : ℕ → ℕ)
    (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (maps : PointedRiemannianConvergenceMaps X L f) (conv : MetricConvergenceData maps)
    (hcanonical : ∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i)
    (W : TopologicalSpace.Opens L.M) (x : ℕ → W) {R : ℝ} (hR : 0 < R)
    (hQ : ∀ n, 2 ≤ metricScalarAt L.metric (x n : L.M))
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf (L.metric.restrictOpen W) (x n)
      (4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M))))) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ q : ℕ → ℝ, ∃ hq : ∀ n, 0 < q n, (∀ n, 1 ≤ q n) ∧
      Tendsto (fun n => q n / metricScalarAt L.metric (x n : L.M)) atTop (𝓝 1) ∧
      ∃ B : ∀ n, PartialDiffeomorph ThreeModel ThreeModel W (X.obj (f (k n))).M ∞,
      let X₂ : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
        { obj := fun n =>
            { M := (X.obj (f (k n))).M
              basepoint := B n (x n)
              metric := scaleMetric (q n) (hq n) (X.obj (f (k n))).metric } }
      ∀ (f₂ : ℕ → ℕ), StrictMono f₂ →
      ∀ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F₂ : PointedRiemannianConvergenceMaps X₂ P₂ f₂) (C₂ : MetricConvergenceData F₂),
        (∀ n, C₂.domain n = CanonicalMetricCompactness.canonicalSourceData F₂ n) →
      ∀ (V : TopologicalSpace.Opens P₂.M) (hp : P₂.basepoint ∈ V) [PathConnectedSpace V],
        (∀ n, (V : Set P₂.M) ⊆ (F₂.partialDiffeomorph n).source) →
      ∀ {D : RealTimeInterval} (S : ℕ → SolutionOn (I := ThreeModel) (M := V) D),
        (∀ n, IsSolutionOn (S n)) →
      ∀ {a b : ℝ} (hab : a < b), Icc a b ⊆ D.carrier → Ico a b ⊆ D.regular →
        (∀ n (z : V) (v w : TangentSpace ThreeModel z),
          ((S n).base.metric b).inner z v w =
            (X₂.obj (f₂ n)).metric.inner (F₂.partialDiffeomorph n z)
              (mfderiv ThreeModel ThreeModel (F₂.partialDiffeomorph n) z v)
              (mfderiv ThreeModel ThreeModel (F₂.partialDiffeomorph n) z w)) →
        (∀ K : Set V, IsCompact K → ∀ m : ℕ,
          ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∀ z ∈ K,
            curvDerivNorm m ((S n).base.metric t) z ≤ Bd) →
      ∀ {Phi : ℝ → ℝ}, AdmissiblePinchingFunction Phi →
      ∀ Qs : ℕ → ℝ, (∀ n, 0 < Qs n) → Tendsto Qs atTop atTop →
        (∀ t ∈ Icc a b, ∀ᶠ n in atTop, ∀ z : V,
          curvatureOperatorLowerBoundAt ((S n).base.metric t) z
            (metricAlgebraicCurvatureTensorAt ((S n).base.metric t) z)
            (rescalePinchingFunction (Qs n) Phi (metricScalarAt ((S n).base.metric t) z))) →
      let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := ThreeModel) V
        ⟨⟨P₂.basepoint, hp⟩⟩
      let A := fun n => inc.trans (F₂.partialDiffeomorph n)
      let comparison := fun n => (A n).trans (B (f₂ n)).symm
      ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric ThreeModel V,
        g b = P₂.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed a b hab.le)) ∧
        (∀ t ∈ Icc a b, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
          algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        (∀ K : Set V, IsCompact K → ∀ m : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
          ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ∈ Icc a b,
            metricDerivNormSupOn K m ((S (rho n)).base.metric t) (g t)
              (P₂.metric.restrictOpen V) < epsilon) ∧
        ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g b) ⟨P₂.basepoint, hp⟩ r) ∧
          (∀ n, comparison n ⟨P₂.basepoint, hp⟩ = x (f₂ n)) ∧
          (∀ᶠ n in atTop,
            riemannianClosedBallOf (g b) ⟨P₂.basepoint, hp⟩ r ⊆ (comparison n).source ∧
            riemannianClosedBallOf (scaleMetric (q (f₂ n)) (hq (f₂ n))
                (L.metric.restrictOpen W)) (x (f₂ n)) (r / 4) ⊆
              (comparison n) '' riemannianClosedBallOf (g b) ⟨P₂.basepoint, hp⟩ r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ y ∈ riemannianClosedBallOf (g b) ⟨P₂.basepoint, hp⟩ r,
              ∀ z ∈ riemannianClosedBallOf (g b) ⟨P₂.basepoint, hp⟩ r,
                |(riemannianEDistOf (scaleMetric (q (f₂ n)) (hq (f₂ n))
                    (L.metric.restrictOpen W)) (comparison n y) (comparison n z)).toReal -
                  (riemannianEDistOf (g b) y z).toReal| < eta := by
  obtain ⟨k, hk, q, hq, hq1, hratio, B, hsrc, hcap, hconv⟩ :=
    exists_secondBlowup_comparison_C11SP X f L maps conv hcanonical W x hR hQ hcompact
  refine ⟨k, hk, q, hq, hq1, hratio, B, ?_⟩
  intro X₂ f₂ hf₂ P₂ F₂ C₂ hcan₂ V hp _ hsource D S hS a b hab hslab hreg hterminal hcurv
    Phi hPhi Qs hQpos hQs hpinching
  exact exists_nonnegative_local_flow_with_end_comparison F₂ C₂ hcan₂ V hp hsource S hS hab
    hslab hreg hterminal hcurv hPhi Qs hQpos hQs hpinching
    (fun n => scaleMetric (q (f₂ n)) (hq (f₂ n)) (L.metric.restrictOpen W))
    (fun n => x (f₂ n)) (fun n => B (f₂ n)) hR (fun n => hsrc (f₂ n)) (fun _ => rfl)
    (fun n => hcap (f₂ n))
    (fun eta heta => hf₂.tendsto_atTop.eventually (hconv eta heta))

end GC.LongTime.Ch11
