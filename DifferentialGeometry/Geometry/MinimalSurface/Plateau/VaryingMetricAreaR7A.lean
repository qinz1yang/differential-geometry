import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SecondTrimR8
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.Measure.Area.ManifoldMeasurable

/-!
# S-MY-R7A G1：common competitor 的面积比较 + 面积随度量收敛

外审 D-R-MY3-4：只控制 `B` 上的度量；`R7` 极限识别链 `A_G(q) ≤ A_G(u∞) ≤ liminf A_{Gₙ}(uₙ) ≤
limsup A_{Gₙ}(uₙ) ≤ A_G(q)` 的末项由
`A_{Gₙ}(uₙ) ≤ A_{Gₙ}(q) → A_G(q)` 给出。本文件给这两步：

* `area_le_common_competitor_R7A`（[PF]，`MYD3/R06R07.lean:170` 逐字）：
  `q` 光滑到边界（`SmoothDiskExtension`）⇒ 对每个 `Gₙ` 是 metric-Lipschitz 的合格 competitor。
* `tangentTwoJacobian_rel_R7A`：逐点相对度量比较 ⇒ 面积密度比较（`(1 − ε) J_g ≤ J_h ≤ (1 + ε) J_g`）。
* `area_tendsto_of_metric_tendsto_R7A`：`Gₙ → G` 于 `B`（chart-free 的相对一致收敛：
  `|Gₙ(v,v) − G(v,v)| ≤ ε G(v,v)`，`x ∈ B`）且 `q` 的像在 `B` 内 ⇒ `A_{Gₙ}(q) → A_G(q)`。
  相对一致收敛由 `R6b` 的 chart `C^∞`（只要 `k = 0`）经紧性给出（`MetricTendstoCInftyOn_MYD3` 的
  `k = 0` 部分蕴含此形——桥接在 G1b 文件末尾）。**不需要 dominated convergence**：相对比较直接夹逼。

不含新 Prop / structure。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **G1a**（R7 核心比较，[PF]，`MYD3/R06R07.lean:170` 逐字）：`q` 光滑到边界且 trace class 为 `Γ` ⇒
`A_{Gₙ}(uₙ) ≤ A_{Gₙ}(q)`（`q` 是**合格** common competitor）。 -/
theorem area_le_common_competitor_R7A [FiniteDimensional ℝ E] {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk G Γ q) {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n)) (n : ℕ) :
    riemannianDiskArea (Gn n) (u n) ≤ riemannianDiskArea (Gn n) q :=
  (hu n).minimizesLipschitz q hq.trace (hQ.lipschitz (Gn n))

/-- 逐点相对度量比较 ⇒ `tangentTwoJacobian` 比较：`h` 在 `x` 处与 `g` 相对误差 `≤ ε < 1`。 -/
theorem tangentTwoJacobian_rel_R7A {g h : SmoothRiemannianMetric 𝓘(ℝ, E) M} {x : M} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hx : ∀ v : TangentSpace 𝓘(ℝ, E) x, |h.inner x v v - g.inner x v v| ≤ ε * g.inner x v v)
    (a b : TangentSpace 𝓘(ℝ, E) x) :
    (1 - ε) * tangentTwoJacobian g a b ≤ tangentTwoJacobian h a b ∧
      tangentTwoJacobian h a b ≤ (1 + ε) * tangentTwoJacobian g a b := by
  have h1 : 0 < 1 - ε := by linarith
  have h2 : 0 < 1 + ε := by linarith
  constructor
  · rw [← tangentTwoJacobian_scaleMetric (1 - ε) h1 g]
    apply tangentTwoJacobian_mono
    intro v
    rw [scaleMetric_inner]
    have := (abs_le.mp (hx v)).1
    linarith
  · rw [← tangentTwoJacobian_scaleMetric (1 + ε) h2 g]
    apply tangentTwoJacobian_mono
    intro v
    rw [scaleMetric_inner]
    have := (abs_le.mp (hx v)).2
    linarith

/-- 夹逼：对每个小 `ε`，`aₙ ∈ [(1 − ε) A, (1 + ε) A]` 终将成立 ⇒ `aₙ → A`（`A ≥ 0`）。 -/
theorem tendsto_of_rel_le_R7A {a : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n in atTop, (1 - ε) * A ≤ a n ∧ a n ≤ (1 + ε) * A) :
    Tendsto a atTop (𝓝 A) := by
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · set ε : ℝ := min (1 / 2) ((A - c) / (2 * (A + 1))) with hεdef
    have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hεA : ε * (A + 1) ≤ (A - c) / 2 := by
      calc ε * (A + 1) ≤ (A - c) / (2 * (A + 1)) * (A + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = (A - c) / 2 := by field_simp
    filter_upwards [h ε hε0 hε1] with n hn
    nlinarith [hn.1]
  · set ε : ℝ := min (1 / 2) ((c - A) / (2 * (A + 1))) with hεdef
    have hε0 : 0 < ε := lt_min (by norm_num) (by apply div_pos <;> linarith)
    have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hεA : ε * (A + 1) ≤ (c - A) / 2 := by
      calc ε * (A + 1) ≤ (c - A) / (2 * (A + 1)) * (A + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = (c - A) / 2 := by field_simp
    filter_upwards [h ε hε0 hε1] with n hn
    nlinarith [hn.2]

/-- **G1b**（R7A）：`Gₙ → G` 于 `B`（相对一致收敛）、`q` 的像在 `B` 内、`A_G(q) < ∞` ⇒
`A_{Gₙ}(q) → A_G(q)`。夹逼 `(1 − ε) A_G(q) ≤ A_{Gₙ}(q) ≤ (1 + ε) A_G(q)`，不需 dominated convergence。 -/
theorem area_tendsto_of_metric_tendsto_R7A [FiniteDimensional ℝ E]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M}
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {q : C(closedDisk, M)} (hqB : range q ⊆ B)
    (hqint : IntegrableOn (riemannianAreaDensity G (diskExtension q)) (Metric.closedBall 0 1)) :
    Tendsto (fun n => riemannianDiskArea (Gn n) q) atTop (𝓝 (riemannianDiskArea G q)) := by
  have hcont : Continuous (diskExtension q) := q.continuous.comp diskRetraction_lipschitz.continuous
  have hrange : ∀ z, diskExtension q z ∈ B := fun z => hqB ⟨_, rfl⟩
  apply tendsto_of_rel_le_R7A (riemannianDiskArea_nonneg G q)
  intro ε hε0 hε1
  filter_upwards [hrel ε hε0] with n hn
  have hpt : ∀ z, (1 - ε) * riemannianAreaDensity G (diskExtension q) z ≤
      riemannianAreaDensity (Gn n) (diskExtension q) z ∧
      riemannianAreaDensity (Gn n) (diskExtension q) z ≤
        (1 + ε) * riemannianAreaDensity G (diskExtension q) z := fun z =>
    tangentTwoJacobian_rel_R7A hε0.le hε1 (hn _ (hrange z)) _ _
  have hup : Integrable (fun z => (1 + ε) * riemannianAreaDensity G (diskExtension q) z)
      (volume.restrict (Metric.closedBall (0 : ℂ) 1)) := hqint.const_mul _
  have hint : Integrable (riemannianAreaDensity (Gn n) (diskExtension q))
      (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
    hup.mono' (measurable_riemannianAreaDensity (Gn n) hcont).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (riemannianAreaDensity_nonneg _ _ _)]
        exact (hpt z).2)
  constructor
  · unfold riemannianDiskArea riemannianArea
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (by linarith) (riemannianAreaDensity_nonneg _ _ _))
      hint (Eventually.of_forall fun z => (hpt z).1)
  · unfold riemannianDiskArea riemannianArea
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg
      (Eventually.of_forall fun z => riemannianAreaDensity_nonneg _ _ _) hup
      (Eventually.of_forall fun z => (hpt z).2)

/-! ## G4：面积 / 能量下半连续（度量也在变） -/

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem coe_extChartAt_eq_R7A (p : M) : (extChartAt 𝓘(ℝ, E) p : M → E) = chartAt E p := by
  ext x
  simp [extChartAt]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem extChartAt_source_eq_R7A (p : M) :
    (extChartAt 𝓘(ℝ, E) p).source = (chartAt E p).source := by
  simp

/-- chart 内 `C¹` 数据（`hCk` 的 `k = 0, 1`，单点）⇒ 固定度量下面积密度逐点收敛。 -/
theorem tendsto_areaDensity_of_chart_R7A
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℕ → ℂ → M} {U₀ : ℂ → M} {z : ℂ} {p : M}
    (hU : ∀ n, ContinuousAt (U n) z) (hU₀ : ContinuousAt U₀ z)
    (hp : U₀ z ∈ (extChartAt 𝓘(ℝ, E) p).source)
    (hmaps : ∀ᶠ n in atTop, U n z ∈ (extChartAt 𝓘(ℝ, E) p).source)
    (h0 : Tendsto (fun n => extChartAt 𝓘(ℝ, E) p (U n z)) atTop
      (𝓝 (extChartAt 𝓘(ℝ, E) p (U₀ z))))
    (h1 : Tendsto (fun n => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (U n w)) z) atTop
      (𝓝 (fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (U₀ w)) z))) :
    Tendsto (fun n => riemannianAreaDensity G (U n) z) atTop
      (𝓝 (riemannianAreaDensity G U₀ z)) := by
  rw [extChartAt_source_eq_R7A] at hp hmaps
  rw [coe_extChartAt_eq_R7A] at h0 h1
  have hc : ContinuousAt (fun q : E × (ℂ →L[ℝ] E) => chartAreaDensity G p q.1 q.2)
      ((chartAt E p (U₀ z)), fderiv ℝ (fun w => chartAt E p (U₀ w)) z) := by
    apply (continuousOn_chartAreaDensity G p).continuousAt
    exact ((chartAt E p).open_target.preimage continuous_fst).mem_nhds
      ((chartAt E p).map_source hp)
  have ht := hc.tendsto.comp (h0.prodMk_nhds h1)
  rw [riemannianAreaDensity_eq_chart G p hU₀ hp]
  refine ht.congr' ?_
  filter_upwards [hmaps] with n hn
  exact (riemannianAreaDensity_eq_chart G p (hU n) hn).symm

/-- 相对夹逼：`aₙ → A`、`|bₙ − aₙ| ≤ ε aₙ`（每个小 `ε`，终将）⇒ `bₙ → A`。 -/
theorem tendsto_of_rel_R7A {a b : ℕ → ℝ} {A : ℝ} (ha : Tendsto a atTop (𝓝 A))
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n in atTop, |b n - a n| ≤ ε * a n) :
    Tendsto b atTop (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hA1 : 0 < |A| + 1 := by positivity
  set ε : ℝ := min (1 / 2) (δ / (2 * (|A| + 1))) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hεA : ε * (|A| + 1) ≤ δ / 2 := by
    calc ε * (|A| + 1) ≤ δ / (2 * (|A| + 1)) * (|A| + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hA1.le
      _ = δ / 2 := by field_simp
  have hA : ∀ᶠ n in atTop, dist (a n) A < min 1 (δ / 2) :=
    Metric.tendsto_nhds.mp ha _ (lt_min one_pos (half_pos hδ))
  filter_upwards [h ε hε0 hε1, hA] with n hn hAn
  have h1 : dist (a n) A < 1 := lt_of_lt_of_le hAn (min_le_left _ _)
  have h2 : dist (a n) A < δ / 2 := lt_of_lt_of_le hAn (min_le_right _ _)
  rw [Real.dist_eq] at h1 h2 ⊢
  have han : a n ≤ |A| + 1 := by
    have := (abs_lt.mp h1).2
    have := le_abs_self A
    linarith
  have hεa : ε * a n ≤ ε * (|A| + 1) := mul_le_mul_of_nonneg_left han hε0.le
  calc |b n - A| = |(b n - a n) + (a n - A)| := by ring_nf
    _ ≤ |b n - a n| + |a n - A| := abs_add_le _ _
    _ < δ := by linarith

/-- **G4a**（lintegral 形）：`uₙ → w` 在 chart `C¹_loc`（`hCk` 的形状，`q := w`）、`Gₙ → G` 于 `B`
（相对一致收敛）、`uₙ` 的像在 `B` ⇒ 面积下半连续 `∫⁻ A_G(w) ≤ liminf ∫⁻ A_{Gₙ}(uₙ)`（Fatou，
逐点收敛 + 度量相对夹逼）。 -/
theorem area_lsc_lintegral_R7A [FiniteDimensional ℝ E]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M}
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {u : ℕ → C(closedDisk, M)} (huB : ∀ n, range (u n) ⊆ B) {w : C(closedDisk, M)}
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension w ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension w z))) atTop Kc) :
    ∫⁻ z in Metric.closedBall (0 : ℂ) 1,
        ENNReal.ofReal (riemannianAreaDensity G (diskExtension w) z) ≤
      liminf (fun n => ∫⁻ z in Metric.closedBall (0 : ℂ) 1,
        ENNReal.ofReal (riemannianAreaDensity (Gn n) (diskExtension (u n)) z)) atTop := by
  have hcont : ∀ n, Continuous (diskExtension (u n)) := fun n =>
    (u n).continuous.comp diskRetraction_lipschitz.continuous
  have hF : ∀ n, Measurable (fun z => ENNReal.ofReal
      (riemannianAreaDensity (Gn n) (diskExtension (u n)) z)) := fun n =>
    ENNReal.measurable_ofReal.comp (measurable_riemannianAreaDensity (Gn n) (hcont n))
  have hpt : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Tendsto (fun n => riemannianAreaDensity (Gn n) (diskExtension (u n)) z) atTop
        (𝓝 (riemannianAreaDensity G (diskExtension w) z)) := by
    intro z hz
    have hwc : Continuous (diskExtension w) := w.continuous.comp diskRetraction_lipschitz.continuous
    obtain ⟨hmaps, hk⟩ := hCk (diskExtension w z) {z} isCompact_singleton
      (singleton_subset_iff.mpr ⟨hz, mem_extChartAt_source (I := 𝓘(ℝ, E)) _⟩)
    have h0 := (tendstoUniformlyOn_of_iteratedFDeriv_zero_R8 (hk 0)).tendsto_at (mem_singleton z)
    have h1 := (tendstoUniformlyOn_fderiv_of_iteratedFDeriv_one_R8 (hk 1)).tendsto_at
      (mem_singleton z)
    have hG := tendsto_areaDensity_of_chart_R7A G (fun n => (hcont n).continuousAt)
      hwc.continuousAt (mem_extChartAt_source (I := 𝓘(ℝ, E)) _)
      (hmaps.mono fun n hn => hn (mem_singleton z)) h0 h1
    refine tendsto_of_rel_R7A hG fun ε hε0 hε1 => ?_
    filter_upwards [hrel ε hε0] with n hn
    have hh : (1 - ε) * riemannianAreaDensity G (diskExtension (u n)) z ≤
        riemannianAreaDensity (Gn n) (diskExtension (u n)) z ∧
        riemannianAreaDensity (Gn n) (diskExtension (u n)) z ≤
          (1 + ε) * riemannianAreaDensity G (diskExtension (u n)) z :=
      tangentTwoJacobian_rel_R7A hε0.le hε1 (hn _ (huB n ⟨_, rfl⟩)) _ _
    rw [abs_le]
    constructor <;> linarith [hh.1, hh.2]
  calc ∫⁻ z in Metric.closedBall (0 : ℂ) 1,
        ENNReal.ofReal (riemannianAreaDensity G (diskExtension w) z)
      ≤ ∫⁻ z in Metric.closedBall (0 : ℂ) 1, liminf (fun n => ENNReal.ofReal
          (riemannianAreaDensity (Gn n) (diskExtension (u n)) z)) atTop := by
        apply lintegral_mono_ae
        filter_upwards [ae_disk_interior] with z hz
        exact ((ENNReal.tendsto_ofReal (hpt z hz)).liminf_eq).ge
    _ ≤ _ := lintegral_liminf_le hF

/-- **G4a'**（`ofReal` 形）：`uₙ` 的面积密度可积 ⇒
`∫⁻ A_G(w) ≤ liminf ofReal (A_{Gₙ}(uₙ))`。 -/
theorem area_lsc_R7A [FiniteDimensional ℝ E]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M}
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {u : ℕ → C(closedDisk, M)} (huB : ∀ n, range (u n) ⊆ B) {w : C(closedDisk, M)}
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension w ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension w z))) atTop Kc)
    (hint : ∀ n, IntegrableOn (riemannianAreaDensity (Gn n) (diskExtension (u n)))
      (Metric.closedBall (0 : ℂ) 1)) :
    ∫⁻ z in Metric.closedBall (0 : ℂ) 1,
        ENNReal.ofReal (riemannianAreaDensity G (diskExtension w) z) ≤
      liminf (fun n => ENNReal.ofReal (riemannianDiskArea (Gn n) (u n))) atTop := by
  refine (area_lsc_lintegral_R7A hrel huB hCk).trans_eq ?_
  congr 1
  funext n
  exact (ofReal_integral_eq_lintegral_ofReal (hint n)
    (Eventually.of_forall fun z => riemannianAreaDensity_nonneg _ _ _)).symm

/-- **G4a''**（有界形，R7 极限识别链 `A_G(u∞) ≤ liminf ≤ c`）：`A_{Gₙ}(uₙ) ≤ c` 终将 ⇒ 极限的面积密度
可积（于是 `A_G(w)` 是真实积分）且 `A_G(w) ≤ c`。 -/
theorem area_lsc_of_bound_R7A [FiniteDimensional ℝ E]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M}
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {u : ℕ → C(closedDisk, M)} (huB : ∀ n, range (u n) ⊆ B) {w : C(closedDisk, M)}
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension w ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension w z))) atTop Kc)
    (hint : ∀ n, IntegrableOn (riemannianAreaDensity (Gn n) (diskExtension (u n)))
      (Metric.closedBall (0 : ℂ) 1))
    {c : ℝ} (hc : ∀ᶠ n in atTop, riemannianDiskArea (Gn n) (u n) ≤ c) :
    IntegrableOn (riemannianAreaDensity G (diskExtension w)) (Metric.closedBall (0 : ℂ) 1) ∧
      riemannianDiskArea G w ≤ c := by
  have hlsc := area_lsc_R7A hrel huB hCk hint
  have hfreq : ∃ᶠ n in atTop, ENNReal.ofReal (riemannianDiskArea (Gn n) (u n)) ≤
      ENNReal.ofReal c := hc.frequently.mono fun n hn => ENNReal.ofReal_le_ofReal hn
  have hle : ∫⁻ z in Metric.closedBall (0 : ℂ) 1,
      ENNReal.ofReal (riemannianAreaDensity G (diskExtension w) z) ≤ ENNReal.ofReal c :=
    hlsc.trans (liminf_le_of_frequently_le' hfreq)
  have hwc : Continuous (diskExtension w) := w.continuous.comp diskRetraction_lipschitz.continuous
  have hint' : IntegrableOn (riemannianAreaDensity G (diskExtension w))
      (Metric.closedBall (0 : ℂ) 1) :=
    (lintegral_ofReal_ne_top_iff_integrable
      (measurable_riemannianAreaDensity G hwc).aestronglyMeasurable
      (Eventually.of_forall fun z => riemannianAreaDensity_nonneg _ _ _)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
  refine ⟨hint', ?_⟩
  have hc0 : 0 ≤ c := by
    obtain ⟨n, hn⟩ := hc.exists
    exact (riemannianDiskArea_nonneg _ _).trans hn
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
    (Eventually.of_forall fun z => riemannianAreaDensity_nonneg _ _ _)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hc0).mp hle

/-- 共形点上能量密度 = 面积密度。 -/
theorem diskMapEnergyDensity_eq_areaDensity_of_conformal_R7A
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (h : DiskMapConformalAt g U z) :
    diskMapEnergyDensity g U z = riemannianAreaDensity g U z := by
  have hA : riemannianAreaDensity g U z =
      tangentTwoJacobian g (diskMapPartial U z 1) (diskMapPartial U z Complex.I) := rfl
  rw [hA, tangentTwoJacobian_of_conformal g h.1 h.2]
  unfold diskMapEnergyDensity
  rw [← h.2]
  ring

/-- **G4b**（能量下半连续，共形盘）：`uₙ` 对 `Gₙ` 共形、`w` 对 `G` 共形（内部）⇒ 能量也下半连续
`∫⁻ E_G(w) ≤ liminf ∫⁻ E_{Gₙ}(uₙ)`（共形时能量密度 = 面积密度，归结为 G4a）。 -/
theorem energy_lsc_R7A [FiniteDimensional ℝ E]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M}
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {u : ℕ → C(closedDisk, M)} (huB : ∀ n, range (u n) ⊆ B) {w : C(closedDisk, M)}
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension w ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension w z))) atTop Kc)
    (hconfn : ∀ n, ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt (Gn n) (diskExtension (u n)) z)
    (hconfw : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt G (diskExtension w) z) :
    ∫⁻ z in Metric.closedBall (0 : ℂ) 1,
        ENNReal.ofReal (diskMapEnergyDensity G (diskExtension w) z) ≤
      liminf (fun n => ∫⁻ z in Metric.closedBall (0 : ℂ) 1,
        ENNReal.ofReal (diskMapEnergyDensity (Gn n) (diskExtension (u n)) z)) atTop := by
  have hw : ∫⁻ z in Metric.closedBall (0 : ℂ) 1,
      ENNReal.ofReal (diskMapEnergyDensity G (diskExtension w) z) =
      ∫⁻ z in Metric.closedBall (0 : ℂ) 1,
        ENNReal.ofReal (riemannianAreaDensity G (diskExtension w) z) := by
    apply lintegral_congr_ae
    filter_upwards [ae_disk_interior] with z hz
    rw [diskMapEnergyDensity_eq_areaDensity_of_conformal_R7A G (hconfw z hz)]
  have hn : ∀ n, ∫⁻ z in Metric.closedBall (0 : ℂ) 1,
      ENNReal.ofReal (diskMapEnergyDensity (Gn n) (diskExtension (u n)) z) =
      ∫⁻ z in Metric.closedBall (0 : ℂ) 1,
        ENNReal.ofReal (riemannianAreaDensity (Gn n) (diskExtension (u n)) z) := by
    intro n
    apply lintegral_congr_ae
    filter_upwards [ae_disk_interior] with z hz
    rw [diskMapEnergyDensity_eq_areaDensity_of_conformal_R7A (Gn n) (hconfn n z hz)]
  rw [hw]
  simp only [hn]
  exact area_lsc_lintegral_R7A hrel huB hCk

end DifferentialGeometry.Geometry

end
