import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HistoryRescale_P6N
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAge_P6L

/-!
# G3（AD-age，R-C11-1 9.1）：records 层的重标度对象（`_P6N`，部分）

在 `HistoryRescale_P6N`（history / event / trace / 终端 slab 的重标度）之上，本文件给
`GeometricCutoffRecord` 重标度所需的参数与 neck 层：
* `CutoffParameters.rescale_P6N p μ`：`delta' t = delta (μ t)`、
  `neckRadius' t = neckRadius (μ t)/√μ`、
  `protectedRadius' t = protectedRadius (μ t)/√μ`；模型数据（`fixed`/`modelRadius`/`modelOrder`/
  `modelAccuracy`/`recenterConstant`）不变 ⇒ `IsCanonicalCutoffRecordFamily` 的五个等式字段原样。
* `NormalizedNeck.rescale_P6N`（`h ↦ μ⁻¹ h`，`scale ↦ μ · scale`，chart / normalized metric 不变）与
  沿 `IncomingSlab.rescale_terminalRegularOpen` 的 transport `NormalizedNeck.terminalRescale_P6N`。
* `IncomingBackwardNeck.rescale_P6N`：半径 `r ↦ r/√μ`，stage chart、normalized metric、jet、
  parabolic closeness 全不变（`(r/√μ)⁻² · μ⁻¹ g(μ(T/μ + (r²/μ) v)) = r⁻² g(T + r² v)`）。
* AD-age 消费（9.1 的 `Λ ≤ R'`、`Λ ≤ R'·t'`）：`R' = μ R`、`R'·t' = R·t`，`μ = a₀ + s_n` 时
  `(a₀ + s_n) Q_n → ∞`（`tendsto_age_mul_of_selection_P6L`）⇒ eventually `Λ ≤ R'`。
**未交（OPEN，精确）**：`GeometricCutoffRecord` 余下字段的重标度——`static : PresentedStaticCap`
（`StaticCapWitness` 的 `metric`/`retainedMetric`/`window_inner`、`collapse_locallyLipschitz`
（edist 乘 `√μ⁻¹`）、`collapse_length`（`riemannianCurveLength_scaleMetric`））、
`hasCanonicalWindow`（`normalizedDatum` +
`CanonicalStaticInsertionWitness.rescale`，树内 `StandardCap/StaticWitnessTransport:110`）、
`curvature_preserving`（Hamilton–Ivey 区域：`InFixedHamiltonIveyRegion (μ⁻¹ g) a x ↔ … g (a μ) x`）、
`protected_interior`/`retained_meets_protected`（terminal open 的 cast）。
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`_P6N`**：cutoff 参数的抛物重标度（时间 `t ↦ μ t`、半径 `÷ √μ`）。 -/
def CutoffParameters.rescale_P6N (p : CutoffParameters) (μ : ℝ) (hμ : 0 < μ) :
    CutoffParameters where
  delta t := p.delta (μ * t)
  neckRadius t := p.neckRadius (μ * t) / Real.sqrt μ
  protectedRadius t := p.protectedRadius (μ * t) / Real.sqrt μ
  delta_pos _ ht := p.delta_pos _ (mul_nonneg hμ.le ht)
  delta_lt_one _ ht := p.delta_lt_one _ (mul_nonneg hμ.le ht)
  neckRadius_pos _ ht :=
    div_pos (p.neckRadius_pos _ (mul_nonneg hμ.le ht)) (Real.sqrt_pos.mpr hμ)
  protectedRadius_pos _ ht :=
    div_pos (p.protectedRadius_pos _ (mul_nonneg hμ.le ht)) (Real.sqrt_pos.mpr hμ)
  fixed := p.fixed
  modelRadius := p.modelRadius
  modelRadius_pos := p.modelRadius_pos
  modelOrder := p.modelOrder
  modelAccuracy := p.modelAccuracy
  modelAccuracy_pos := p.modelAccuracy_pos
  recenterConstant := p.recenterConstant
  recenterConstant_ge_four := p.recenterConstant_ge_four

/-- 重标度参数在重标度事件时刻 `T/μ` 的值：`delta` 不变、半径 `÷ √μ`。 -/
theorem CutoffParameters.rescale_P6N_eval (p : CutoffParameters) (μ : ℝ) (hμ : 0 < μ) (T : ℝ) :
    (p.rescale_P6N μ hμ).delta (T / μ) = p.delta T ∧
    (p.rescale_P6N μ hμ).neckRadius (T / μ) = p.neckRadius T / Real.sqrt μ ∧
    (p.rescale_P6N μ hμ).protectedRadius (T / μ) = p.protectedRadius T / Real.sqrt μ := by
  simp only [CutoffParameters.rescale_P6N, mul_div_cancel₀ T hμ.ne', and_self]

section Neck

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **`_P6N`**：normalized neck 在 `h ↦ μ⁻¹ h` 下：`scale ↦ μ · scale`，chart / center /
normalized metric / closeness 不变。 -/
def NormalizedNeck.rescale_P6N {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck h δ k) (μ : ℝ) (hμ : 0 < μ) :
    NormalizedNeck (scaleMetric μ⁻¹ (inv_pos.mpr hμ) h) δ k where
  delta_pos := N.delta_pos
  delta_lt_one := N.delta_lt_one
  sphereMark := N.sphereMark
  center := N.center
  chart := N.chart
  chart_smooth := N.chart_smooth
  marked := N.marked
  scale := μ * N.scale
  scale_pos := mul_pos hμ N.scale_pos
  scale_scalar := by
    rw [metricScalarAt_scaleMetric, inv_inv, N.scale_scalar]
  normalizedMetric := N.normalizedMetric
  normalized_inner := by
    intro x V W
    rw [N.normalized_inner x V W, scaleMetric_inner]
    field_simp
  closeness := N.closeness

end Neck

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance stageSecondCountable_P6N : SecondCountableTopology P.Carrier :=
  ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier

private local instance opensLocallyCompact_P6N (U : TopologicalSpace.Opens P.Carrier) :
    LocallyCompactSpace U :=
  ChartedSpace.locallyCompactSpace ThreeSpace U

private theorem cast_val_heq_P6N {U V : TopologicalSpace.Opens P.Carrier} (h : U = V)
    (q : ∀ U : TopologicalSpace.Opens P.Carrier, SmoothRiemannianMetric ThreeModel U → Prop)
    (g : {g : SmoothRiemannianMetric ThreeModel U // q U g}) : HEq (h ▸ g).1 g.1 := by
  cases h
  rfl

/-- 重标度终端极限度量与 `μ⁻¹ ·` 原终端度量 `HEq`（terminal open 相等，`rescale_terminalRegularOpen`）。 -/
theorem TerminalLimitMetric.rescale_metric_heq_P6N (L : G.TerminalLimitMetric) (μ : ℝ)
    (hμ : 0 < μ) :
    HEq (L.rescale μ hμ).metric (scaleMetric μ⁻¹ (inv_pos.mpr hμ) L.metric) :=
  cast_val_heq_P6N (G.rescale_terminalRegularOpen μ hμ).symm
    (fun U gbar => ∀ K : Set U, IsCompact K → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ d ∈ Ico (a / μ) (s / μ), ∀ t ∈ Ioo d (s / μ), ∀ x ∈ K,
        DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm j
          (((G.rescale μ hμ).flow.base.metric t).restrictOpen U) gbar gbar x < ε)
    ⟨scaleMetric μ⁻¹ (inv_pos.mpr hμ) L.metric, L.rescale_converges μ hμ⟩

/-- neck 沿 terminal open 的相等与度量 `HEq` 搬运。 -/
def castNeck_P6N {U V : TopologicalSpace.Opens P.Carrier} (h : U = V)
    {g : SmoothRiemannianMetric ThreeModel U} {g' : SmoothRiemannianMetric ThreeModel V}
    (hg : HEq g g') {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) : NormalizedNeck g' δ k := by
  subst h
  exact (eq_of_heq hg) ▸ N

theorem castNeck_chart_val_P6N {U V : TopologicalSpace.Opens P.Carrier} (h : U = V)
    {g : SmoothRiemannianMetric ThreeModel U} {g' : SmoothRiemannianMetric ThreeModel V}
    (hg : HEq g g') {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) (x : neckBuffer δ) :
    ((castNeck_P6N h hg N).chart x).1 = (N.chart x).1 := by
  subst h
  obtain rfl := eq_of_heq hg
  rfl

theorem castNeck_normalizedMetric_P6N {U V : TopologicalSpace.Opens P.Carrier} (h : U = V)
    {g : SmoothRiemannianMetric ThreeModel U} {g' : SmoothRiemannianMetric ThreeModel V}
    (hg : HEq g g') {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) :
    (castNeck_P6N h hg N).normalizedMetric = N.normalizedMetric := by
  subst h
  obtain rfl := eq_of_heq hg
  rfl

theorem castNeck_scale_P6N {U V : TopologicalSpace.Opens P.Carrier} (h : U = V)
    {g : SmoothRiemannianMetric ThreeModel U} {g' : SmoothRiemannianMetric ThreeModel V}
    (hg : HEq g g') {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) :
    (castNeck_P6N h hg N).scale = N.scale := by
  subst h
  obtain rfl := eq_of_heq hg
  rfl

/-- **`_P6N`**：事件终端度量上的 neck 在重标度事件终端度量上的像（`scale ↦ μ · scale`）。 -/
def TerminalLimitMetric.rescaleNeck_P6N (L : G.TerminalLimitMetric) {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck L.metric δ k) (μ : ℝ) (hμ : 0 < μ) :
    NormalizedNeck (L.rescale μ hμ).metric δ k :=
  castNeck_P6N (G.rescale_terminalRegularOpen μ hμ).symm
    (L.rescale_metric_heq_P6N μ hμ).symm (N.rescale_P6N μ hμ)

theorem TerminalLimitMetric.rescaleNeck_chart_val_P6N (L : G.TerminalLimitMetric) {δ : ℝ}
    {k : ℕ} (N : NormalizedNeck L.metric δ k) (μ : ℝ) (hμ : 0 < μ) (x : neckBuffer δ) :
    ((L.rescaleNeck_P6N N μ hμ).chart x).1 = (N.chart x).1 :=
  castNeck_chart_val_P6N _ _ (N.rescale_P6N μ hμ) x

theorem TerminalLimitMetric.rescaleNeck_normalizedMetric_P6N (L : G.TerminalLimitMetric)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k) (μ : ℝ) (hμ : 0 < μ) :
    (L.rescaleNeck_P6N N μ hμ).normalizedMetric = N.normalizedMetric :=
  castNeck_normalizedMetric_P6N _ _ (N.rescale_P6N μ hμ)

theorem TerminalLimitMetric.rescaleNeck_scale_P6N (L : G.TerminalLimitMetric) {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck L.metric δ k) (μ : ℝ) (hμ : 0 < μ) :
    (L.rescaleNeck_P6N N μ hμ).scale = μ * N.scale :=
  castNeck_scale_P6N _ _ (N.rescale_P6N μ hμ)

end OrientedThreeStage.IncomingSlab

namespace ObservedHistory

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}

private theorem rescale_left_lt_iff_P6N {μ T r b : ℝ} (hμ : 0 < μ) :
    T / μ - (r / Real.sqrt μ) ^ 2 < b / μ ↔ T - r ^ 2 < b := by
  rw [div_pow, Real.sq_sqrt hμ.le, ← sub_div]
  exact div_lt_div_iff_of_pos_right hμ

private theorem rescale_time_mul_P6N {μ T r v : ℝ} (hμ : 0 < μ) :
    μ * (T / μ + (r / Real.sqrt μ) ^ 2 * v) = T + r ^ 2 * v := by
  rw [div_pow, Real.sq_sqrt hμ.le]
  field_simp

private theorem rescale_le_iff_P6N {μ T r v c : ℝ} (hμ : 0 < μ) :
    c / μ ≤ T / μ + (r / Real.sqrt μ) ^ 2 * v ↔ c ≤ T + r ^ 2 * v := by
  rw [div_pow, Real.sq_sqrt hμ.le, show T / μ + r ^ 2 / μ * v = (T + r ^ 2 * v) / μ by ring]
  exact div_le_div_iff_of_pos_right hμ

private theorem rescale_lt_iff_P6N {μ T r v c : ℝ} (hμ : 0 < μ) :
    T / μ + (r / Real.sqrt μ) ^ 2 * v < c / μ ↔ T + r ^ 2 * v < c := by
  rw [div_pow, Real.sq_sqrt hμ.le, show T / μ + r ^ 2 / μ * v = (T + r ^ 2 * v) / μ by ring]
  exact div_lt_div_iff_of_pos_right hμ

private theorem rescale_coeff_P6N {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r) (X : ℝ) :
    ((r / Real.sqrt μ) ^ 2)⁻¹ * (μ⁻¹ * X) = (r ^ 2)⁻¹ * X := by
  rw [div_pow, Real.sq_sqrt hμ.le]
  field_simp

/-- **`_P6N`**：backward neck 的抛物重标度（半径 `r ↦ r/√μ`；chart、normalized metric、jet 不变）。 -/
def IncomingBackwardNeck.rescale_P6N {δ : ℝ} {k : ℕ}
    {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}
    (B : IncomingBackwardNeck H i neck r) (μ : ℝ) (hμ : 0 < μ) :
    IncomingBackwardNeck (H.rescale μ hμ) i
      ((H.event i).terminal.rescaleNeck_P6N neck μ hμ) (r / Real.sqrt μ) where
  radius_pos := div_pos B.radius_pos (Real.sqrt_pos.mpr hμ)
  left_nonneg := by
    change 0 ≤ H.time i.succ / μ - (r / Real.sqrt μ) ^ 2
    rw [div_pow, Real.sq_sqrt hμ.le, ← sub_div]
    exact div_nonneg B.left_nonneg hμ.le
  stageChart := fun j hj ha => B.stageChart j hj ((rescale_left_lt_iff_P6N hμ).mp ha)
  stageChart_smooth := fun j hj ha => B.stageChart_smooth j hj _
  terminal_chart := by
    intro ha x
    exact (B.terminal_chart _ x).trans
      (OrientedThreeStage.IncomingSlab.TerminalLimitMetric.rescaleNeck_chart_val_P6N _ _ _ _ x).symm
  crossing := by
    intro j hj next ha hn x
    exact B.crossing j hj ((rescale_left_lt_iff_P6N hμ).mp ha)
      ((rescale_left_lt_iff_P6N hμ).mp hn) x
  metric := B.metric
  terminal_metric := by
    rw [B.terminal_metric]
    exact (OrientedThreeStage.IncomingSlab.TerminalLimitMetric.rescaleNeck_normalizedMetric_P6N
      _ _ _ _).symm
  metric_on_slab := by
    intro j hj ha v hv h1 h2 x V W
    have h1' := (rescale_le_iff_P6N hμ).mp h1
    have h2' := (rescale_lt_iff_P6N hμ).mp h2
    rw [B.metric_on_slab j hj ((rescale_left_lt_iff_P6N hμ).mp ha) v hv h1' h2' x V W]
    change _ = ((r / Real.sqrt μ) ^ 2)⁻¹ *
      (((H.event j).rescale μ hμ).incoming.flow.base.metric
        (H.time i.succ / μ + (r / Real.sqrt μ) ^ 2 * v)).inner _ _ _
    rw [MetricCutCapEvent.rescale_incoming_metric, rescale_time_mul_P6N hμ]
    change _ = ((r / Real.sqrt μ) ^ 2)⁻¹ * (μ⁻¹ * _)
    exact (rescale_coeff_P6N hμ B.radius_pos _).symm
  timeDifferenceJet := B.timeDifferenceJet
  timeDifferenceJet_eq := B.timeDifferenceJet_eq
  parabolic_closeness := B.parabolic_closeness
  metric_smooth := B.metric_smooth

end ObservedHistory

namespace RetainedCoreHistory

/-- **AD-age 消费（9.1）**：history 按 `μ_n = a₀ + s_n` 重标度后，终端 slab 在 `s_n/μ_n` 的标量
`R'_n = μ_n Q_n → ∞`（selection 给 `s_n ≥ t_n − r_n²/2`、`r_n² ≤ t_n`、`t_n Q_n → ∞`），且
`R'_n · (s_n/μ_n) = Q_n s_n`；于是 SLT 的 `Λ ≤ R'`、`1 ≤ R'` eventually 成立（任意 `Λ`）。 -/
theorem eventually_rescaled_scalar_ge_P6N {P : ℕ → OrientedThreeStage.{u}} {a s : ℕ → ℝ}
    (G : ∀ n, (P n).IncomingSlab (a n) (s n)) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) {t r : ℕ → ℝ}
    (σ : ℕ → ℝ) (y : ∀ n, (P n).Carrier) (hμ : ∀ n, 0 < a₀ + σ n)
    (hQ : ∀ n, 0 < (G n).flow.scalar (σ n) (y n))
    (hσ : ∀ n, t n - r n ^ 2 / 2 ≤ σ n) (hr : ∀ n, r n ^ 2 ≤ t n)
    (htQ : Tendsto (fun n => t n * (G n).flow.scalar (σ n) (y n)) atTop atTop) (Λ : ℝ) :
    ∀ᶠ n in atTop, Λ ≤ ((G n).rescale (a₀ + σ n) (hμ n)).flow.scalar (σ n / (a₀ + σ n)) (y n) ∧
      ((G n).rescale (a₀ + σ n) (hμ n)).flow.scalar (σ n / (a₀ + σ n)) (y n) *
          (σ n / (a₀ + σ n)) = (G n).flow.scalar (σ n) (y n) * σ n := by
  have hage := tendsto_age_mul_of_selection_P6L ha₀ hQ hσ hr htQ
  filter_upwards [hage.eventually_ge_atTop Λ] with n hn
  refine ⟨?_, rescale_scalar_mul_time_P6N (G n) _ (hμ n) (σ n) (y n)⟩
  rw [rescale_scalar_P6N, mul_div_cancel₀ _ (hμ n).ne']
  exact hn

end RetainedCoreHistory

/-- consumer（record 字段 `scale_eq` 的 transport 形）：`neck.scale = (r²)⁻¹` ⇒ 重标度事件终端上
`rescaleNeck.scale = ((r/√μ)²)⁻¹`，与 `IncomingBackwardNeck.rescale_P6N` 的半径 `r/√μ` 相容。 -/
example {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ : ℝ} {k : ℕ}
    (neck : NormalizedNeck (H.event i).terminal.metric δ k) {r : ℝ} (hr : 0 < r)
    (hscale : neck.scale = (r ^ 2)⁻¹) (μ : ℝ) (hμ : 0 < μ) :
    ((H.event i).terminal.rescaleNeck_P6N neck μ hμ).scale = ((r / Real.sqrt μ) ^ 2)⁻¹ := by
  rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.rescaleNeck_scale_P6N, hscale, div_pow,
    Real.sq_sqrt hμ.le]
  field_simp

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
