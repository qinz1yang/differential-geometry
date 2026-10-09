import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeStatic_P6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Curvature.OperatorScaling

/-!
# G3c（AD-age 收尾，part 2）：`GeometricCutoffRecord` 的抛物重标度（`_P6M`）

在 G3a（`HistoryRescale_P6N` / `AdapterAgeObject_P6N`）、G3b（`AdapterAgeCaps_P6N`）与 part 1
（`AdapterAgeStatic_P6M`：`PresentedStaticCap.rescale_P6M`）之上装配
**`GeometricCutoffRecord.rescale_P6M : GeometricCutoffRecord H i p →
GeometricCutoffRecord (H.rescale μ hμ) i (p.rescale_P6N μ hμ)`**（`ObservedHistory` 层；
`RetainedCoreHistory` 经 G3a `toHistory_rescale_P6N`（`rfl`）直接适用）。逐字段：
* `singular`：`rescale_singularEndpoint_P6M`（`riemannNorm' = μ · riemannNorm(μ ·)`）；
* `nominalRadius ↦ r/√μ`，`nominal_*` 由 `CutoffParameters.rescale_P6N_eval`；`delta`/`order` 原样；
* `neck` = G3a `rescaleNeck_P6N`，`scale_eq` 同 G3a consumer，`backward` = G3a
  `IncomingBackwardNeck.rescale_P6N`；`buffer_disjoint`/`tube_eq`/`recenter_chart` 走 chart 值；
* `retained_terminal`（`rescale_terminalRegularRegion`）、`protected_interior` /
  `retained_meets_protected`（terminal open cast：`R' = μ R`，`(ρ/√μ)⁻² = μ ρ⁻²`）；
* `curvature_preserving`：**`inFixedHamiltonIveyRegion_scaleMetric_inv_iff_P6M`**
  `InFixedHamiltonIveyRegion (μ⁻¹ g) a x ↔ InFixedHamiltonIveyRegion g (μ a) x`（树内
  `inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion` + 最小曲率算子特征值
  `leastCurvatureOperatorEigenvalueAt_scaleMetric` + `mem_fixedHamiltonIveyRegion_scale_iff`）；
* `scalar_preserving`：`L ↦ L/μ`；`static` = part 1；`recenter_*` 由 part 1 几何引理。
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section HamiltonIvey

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

/-- **Hamilton–Ivey 区域的缩放**：`μ⁻¹ g` 在年龄 `a` 的区域 ⇔ `g` 在年龄 `μ a` 的区域
（`R ↦ μ R`、最小曲率算子特征值 `ν ↦ μ ν`）。 -/
theorem inFixedHamiltonIveyRegion_scaleMetric_inv_iff_P6M
    {g : SmoothRiemannianMetric ThreeModel X} {μ : ℝ} (hμ : 0 < μ) {a : ℝ} {x : X} :
    InFixedHamiltonIveyRegion (scaleMetric μ⁻¹ (inv_pos.mpr hμ) g) a x ↔
      InFixedHamiltonIveyRegion g (μ * a) x := by
  rw [inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion,
    inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion, metricScalarAt_scaleMetric,
    DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_scaleMetric]
  have h := mem_fixedHamiltonIveyRegion_scale_iff (inv_pos.mpr hμ) (μ * a) (metricScalarAt g x)
    (2 * leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x))
  rw [inv_mul_cancel_left₀ hμ.ne'] at h
  rw [← h]
  have hp : ((μ⁻¹)⁻¹ * metricScalarAt g x, 2 * (leastCurvatureOperatorEigenvalueAt g x
      (metricAlgebraicCurvatureTensorAt g x) / μ⁻¹)) =
      (metricScalarAt g x / μ⁻¹, 2 * leastCurvatureOperatorEigenvalueAt g x
        (metricAlgebraicCurvatureTensorAt g x) / μ⁻¹) := by
    refine Prod.ext ?_ ?_
    · change (μ⁻¹)⁻¹ * metricScalarAt g x = metricScalarAt g x / μ⁻¹
      rw [div_eq_mul_inv, mul_comm]
    · change 2 * (leastCurvatureOperatorEigenvalueAt g x
        (metricAlgebraicCurvatureTensorAt g x) / μ⁻¹) = 2 * leastCurvatureOperatorEigenvalueAt g x
          (metricAlgebraicCurvatureTensorAt g x) / μ⁻¹
      rw [mul_div_assoc]
  rw [hp]

end HamiltonIvey

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

private local instance stageSecondCountable_P6M : SecondCountableTopology P.Carrier :=
  ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier

private local instance opensLocallyCompact_P6M (U : TopologicalSpace.Opens P.Carrier) :
    LocallyCompactSpace U :=
  ChartedSpace.locallyCompactSpace ThreeSpace U

/-- 重标度保持 singular endpoint（`riemannNorm' t = μ · riemannNorm (μ t)`）。 -/
theorem rescale_singularEndpoint_P6M (G : P.IncomingSlab a s) (μ : ℝ) (hμ : 0 < μ)
    (hG : G.SingularEndpoint) : (G.rescale μ hμ).SingularEndpoint := by
  intro L hL d hd
  have hd1 : a ≤ d * μ := (div_le_iff₀ hμ).mp hd.1
  have hd2 : d * μ < s := (lt_div_iff₀ hμ).mp hd.2
  have hd' : μ * d ∈ Ico a s := ⟨by linarith, by linarith⟩
  have hsing := hG (L / μ) (div_pos hL hμ) (μ * d) hd'
  obtain ⟨t, ht, x, hx⟩ := hsing
  refine ⟨t / μ, ⟨?_, div_lt_div_of_pos_right ht.2 hμ⟩, x, ?_⟩
  · rw [lt_div_iff₀ hμ]
    linarith [ht.1]
  · rw [rescale_riemannNorm, mul_div_cancel₀ t hμ.ne']
    have hx' := (div_lt_iff₀ hμ).mp hx
    linarith

theorem rescale_mem_terminalRegularOpen_P6M {G : P.IncomingSlab a s} (μ : ℝ) (hμ : 0 < μ)
    {y : P.Carrier} : y ∈ (G.rescale μ hμ).terminalRegularOpen ↔ y ∈ G.terminalRegularOpen := by
  rw [G.rescale_terminalRegularOpen μ hμ]

private theorem metricScalarAt_cast_P6M {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {g : SmoothRiemannianMetric ThreeModel U} {g' : SmoothRiemannianMetric ThreeModel V}
    (hg : HEq g g') (x : V) (hx : x.1 ∈ U) :
    metricScalarAt g' x = metricScalarAt g ⟨x.1, hx⟩ := by
  subst hUV
  obtain rfl := eq_of_heq hg
  rfl

private theorem inFixedHamiltonIveyRegion_cast_P6M {U V : TopologicalSpace.Opens P.Carrier}
    (hUV : U = V) {g : SmoothRiemannianMetric ThreeModel U}
    {g' : SmoothRiemannianMetric ThreeModel V} (hg : HEq g g') {c : ℝ} {x : V} (hx : x.1 ∈ U) :
    InFixedHamiltonIveyRegion g' c x ↔ InFixedHamiltonIveyRegion g c ⟨x.1, hx⟩ := by
  subst hUV
  obtain rfl := eq_of_heq hg
  rfl

private theorem castNeck_sphereMark_P6M {U V : TopologicalSpace.Opens P.Carrier} (h : U = V)
    {g : SmoothRiemannianMetric ThreeModel U} {g' : SmoothRiemannianMetric ThreeModel V}
    (hg : HEq g g') {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) :
    (castNeck_P6N h hg N).sphereMark = N.sphereMark := by
  subst h
  obtain rfl := eq_of_heq hg
  rfl

variable {G : P.IncomingSlab a s}

/-- 重标度终端度量的标量：`R'(x) = μ · R(x)`（terminal open 相等下的同一点）。 -/
theorem TerminalLimitMetric.rescale_metricScalarAt_P6M (L : G.TerminalLimitMetric) (μ : ℝ)
    (hμ : 0 < μ) (x : (G.rescale μ hμ).terminalRegularOpen) (hx : x.1 ∈ G.terminalRegularOpen) :
    metricScalarAt (L.rescale μ hμ).metric x = μ * metricScalarAt L.metric ⟨x.1, hx⟩ := by
  rw [metricScalarAt_cast_P6M (G.rescale_terminalRegularOpen μ hμ).symm
    (L.rescale_metric_heq_P6N μ hμ).symm x hx, metricScalarAt_scaleMetric, inv_inv]

/-- 重标度终端度量的 Hamilton–Ivey 区域：年龄 `a` ⇔ 原终端度量年龄 `μ a`。 -/
theorem TerminalLimitMetric.rescale_inFixedHamiltonIveyRegion_iff_P6M
    {L : G.TerminalLimitMetric} {μ : ℝ} {hμ : 0 < μ} {c : ℝ}
    {x : (G.rescale μ hμ).terminalRegularOpen} (hx : x.1 ∈ G.terminalRegularOpen) :
    InFixedHamiltonIveyRegion (L.rescale μ hμ).metric c x ↔
      InFixedHamiltonIveyRegion L.metric (μ * c) ⟨x.1, hx⟩ :=
  (inFixedHamiltonIveyRegion_cast_P6M (G.rescale_terminalRegularOpen μ hμ).symm
    (L.rescale_metric_heq_P6N μ hμ).symm hx).trans
    (inFixedHamiltonIveyRegion_scaleMetric_inv_iff_P6M hμ)

theorem TerminalLimitMetric.rescaleNeck_sphereMark_P6M (L : G.TerminalLimitMetric) {δ : ℝ}
    {k : ℕ} (N : NormalizedNeck L.metric δ k) (μ : ℝ) (hμ : 0 < μ) :
    (L.rescaleNeck_P6N N μ hμ).sphereMark = N.sphereMark :=
  castNeck_sphereMark_P6M _ _ (N.rescale_P6N μ hμ)

end OrientedThreeStage.IncomingSlab

namespace GeometricCutoffRecord

open OrientedThreeStage.IncomingSlab

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}

private theorem nominal_small_P6M {μ r δ ρ δ' ρ' : ℝ} (hμ : 0 < μ) (h : r < δ ^ 2 * ρ)
    (hd : δ' = δ) (hn : ρ' = ρ / Real.sqrt μ) : r / Real.sqrt μ < δ' ^ 2 * ρ' := by
  rw [hd, hn, mul_div_assoc']
  exact div_lt_div_of_pos_right h (Real.sqrt_pos.mpr hμ)

private theorem nominal_time_P6M {μ r T : ℝ} (hμ : 0 < μ) (h : r ^ 2 ≤ T) :
    (r / Real.sqrt μ) ^ 2 ≤ T / μ := by
  rw [div_pow, Real.sq_sqrt hμ.le]
  exact div_le_div_of_nonneg_right h hμ.le

private theorem scale_eq_P6M {μ n r n' : ℝ} (hμ : 0 < μ) (hn' : n' = μ * n)
    (h : n = (r ^ 2)⁻¹) : n' = ((r / Real.sqrt μ) ^ 2)⁻¹ := by
  rw [hn', h, div_pow, Real.sq_sqrt hμ.le, inv_div, div_eq_mul_inv]

private theorem protected_le_P6M {μ S S' ρ ρ' : ℝ} (hμ : 0 < μ) (h1 : S' = μ * S)
    (hp : ρ' = ρ / Real.sqrt μ) (h : S' ≤ (ρ' ^ 2)⁻¹) : S ≤ (ρ ^ 2)⁻¹ := by
  rw [h1, hp, div_pow, Real.sq_sqrt hμ.le, inv_div, div_eq_mul_inv] at h
  exact le_of_mul_le_mul_left h hμ

private theorem le_protected_P6M {μ S S' ρ ρ' : ℝ} (hμ : 0 < μ) (h1 : S' = μ * S)
    (hp : ρ' = ρ / Real.sqrt μ) (h : S ≤ (ρ ^ 2)⁻¹) : S' ≤ (ρ' ^ 2)⁻¹ := by
  rw [h1, hp, div_pow, Real.sq_sqrt hμ.le, inv_div, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left h hμ.le

private theorem abs_div_rescale_P6M {μ s n s' n' C : ℝ} (hμ : 0 < μ) (hs : s' = μ * s)
    (hn : n' = μ * n) (h : |s / n - 1| ≤ C) : |s' / n' - 1| ≤ C := by
  rw [hs, hn, mul_div_mul_left _ _ hμ.ne']
  exact h

private theorem div_le_iff_mul_P6M {μ L Y : ℝ} (hμ : 0 < μ) : L / μ ≤ Y ↔ L ≤ μ * Y := by
  rw [div_le_iff₀ hμ, mul_comm]

private theorem le_scaleMetric_P6M {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] (g : SmoothRiemannianMetric ThreeModel X) {μ L : ℝ}
    (hμ : 0 < μ) (x : X) (h : L / μ ≤ metricScalarAt g x) :
    L ≤ metricScalarAt (scaleMetric μ⁻¹ (inv_pos.mpr hμ) g) x := by
  rw [metricScalarAt_scaleMetric, inv_inv]
  exact (div_le_iff_mul_P6M hμ).mp h

/-- **`_P6M`（AD-age 收尾）**：geometric cutoff record 的抛物重标度（见文件头）。 -/
def rescale_P6M (R : GeometricCutoffRecord H i p) (μ : ℝ) (hμ : 0 < μ) :
    GeometricCutoffRecord (H.rescale μ hμ) i (p.rescale_P6N μ hμ) where
  singular := (H.event i).incoming.rescale_singularEndpoint_P6M μ hμ R.singular
  nominalRadius h := R.nominalRadius h / Real.sqrt μ
  nominal_pos h := div_pos (R.nominal_pos h) (Real.sqrt_pos.mpr hμ)
  nominal_small h := nominal_small_P6M hμ (R.nominal_small h)
    (p.rescale_P6N_eval μ hμ (H.time i.succ)).1 (p.rescale_P6N_eval μ hμ (H.time i.succ)).2.1
  nominal_time h := nominal_time_P6M hμ (R.nominal_time h)
  delta := R.delta
  delta_pos := R.delta_pos
  delta_le α := (R.delta_le α).trans_eq (p.rescale_P6N_eval μ hμ (H.time i.succ)).1.symm
  order := R.order
  order_lower := R.order_lower
  neck α := (H.event i).terminal.rescaleNeck_P6N (R.neck α) μ hμ
  scale_eq α := scale_eq_P6M hμ
    ((H.event i).terminal.rescaleNeck_scale_P6N (R.neck α) μ hμ) (R.scale_eq α)
  buffer_disjoint := fun α β hαβ => Set.disjoint_left.mpr (by
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    refine Set.disjoint_left.mp (R.buffer_disjoint hαβ) ⟨x, rfl⟩ ⟨y, Subtype.ext ?_⟩
    exact ((H.event i).terminal.rescaleNeck_chart_val_P6N (R.neck β) μ hμ y).symm.trans
      ((congrArg Subtype.val hy).trans
        ((H.event i).terminal.rescaleNeck_chart_val_P6N (R.neck α) μ hμ x)))
  tube_eq α x hx := (R.tube_eq α x hx).trans
    ((H.event i).terminal.rescaleNeck_chart_val_P6N (R.neck α) μ hμ _).symm
  tube_in_buffer := R.tube_in_buffer
  backward α := ObservedHistory.IncomingBackwardNeck.rescale_P6N (R.backward α) μ hμ
  retained_terminal x hx := by
    have h := R.retained_terminal x hx
    rw [← (H.event i).incoming.rescale_terminalRegularRegion μ hμ] at h
    exact h
  protected_interior x hx := by
    have hx0 : x.1 ∈ (H.event i).incoming.terminalRegularOpen :=
      (rescale_mem_terminalRegularOpen_P6M (G := (H.event i).incoming) μ hμ).mp x.2
    exact R.protected_interior ⟨x.1, hx0⟩ (protected_le_P6M hμ
      ((H.event i).terminal.rescale_metricScalarAt_P6M μ hμ x hx0)
      (p.rescale_P6N_eval μ hμ (H.time i.succ)).2.2 hx)
  retained_meets_protected c hc := by
    have hR := R.retained_meets_protected c hc
    obtain ⟨x, hx, hcx, hle⟩ := hR
    have hx1 : x.1 ∈ ((H.event i).incoming.rescale μ hμ).terminalRegularOpen :=
      (rescale_mem_terminalRegularOpen_P6M (G := (H.event i).incoming) μ hμ).mpr x.2
    exact ⟨⟨x.1, hx1⟩, hx, hcx, le_protected_P6M hμ
      ((H.event i).terminal.rescale_metricScalarAt_P6M μ hμ ⟨x.1, hx1⟩ x.2)
      (p.rescale_P6N_eval μ hμ (H.time i.succ)).2.2 hle⟩
  one_retained_side := R.one_retained_side
  no_cuts_discard := R.no_cuts_discard
  static b := (R.static b).rescale_P6M μ hμ
  recenter_scale b := ((R.static b).rescale_P6M μ hμ).neck.scale_scalar
  recenter_mark b := ((R.static b).rescale_P6M_sphereMark μ hμ).trans ((R.recenter_mark b).trans
    ((H.event i).terminal.rescaleNeck_sphereMark_P6M (R.neck b.1.1) μ hμ).symm)
  recenter_delta b := ((R.static b).rescale_P6M_delta μ hμ).trans (R.recenter_delta b)
  recenter_scale_comparison b := abs_div_rescale_P6M hμ ((R.static b).rescale_P6M_scale μ hμ)
    ((H.event i).terminal.rescaleNeck_scale_P6N (R.neck b.1.1) μ hμ)
    (R.recenter_scale_comparison b)
  recenter_chart b x hx := by
    have hx0 : x.1 ∈ neckBuffer (R.static b).delta := by
      rw [← (R.static b).rescale_P6M_delta μ hμ]
      exact x.2
    apply Subtype.ext
    exact ((R.static b).rescale_P6M_chart_val μ hμ x hx0).trans
      ((congrArg Subtype.val (R.recenter_chart b ⟨x.1, hx0⟩ hx)).trans
        ((H.event i).terminal.rescaleNeck_chart_val_P6N (R.neck b.1.1) μ hμ _).symm)
  recenter_in_buffer b x := by
    have hx0 : x.1 ∈ neckBuffer (R.static b).delta := by
      rw [← (R.static b).rescale_P6M_delta μ hμ]
      exact x.2
    exact R.recenter_in_buffer b ⟨x.1, hx0⟩
  old_eq_retained := R.old_eq_retained
  curvature_preserving a ha hall x := by
    apply (inFixedHamiltonIveyRegion_scaleMetric_inv_iff_P6M (g := (H.event i).outputMetric)
      hμ).mpr
    refine R.curvature_preserving (μ * a) (mul_pos hμ ha) (fun y => ?_) x
    have hy1 : y.1 ∈ ((H.event i).incoming.rescale μ hμ).terminalRegularOpen :=
      (rescale_mem_terminalRegularOpen_P6M (G := (H.event i).incoming) μ hμ).mpr y.2
    exact (TerminalLimitMetric.rescale_inFixedHamiltonIveyRegion_iff_P6M
      (L := (H.event i).terminal) (hμ := hμ) (x := ⟨y.1, hy1⟩) y.2).mp (hall ⟨y.1, hy1⟩)
  scalar_preserving L hL hall x := by
    have hall' : ∀ y : (H.event i).incoming.terminalRegularOpen,
        L / μ ≤ metricScalarAt (H.event i).terminal.metric y := by
      intro y
      have hy1 : y.1 ∈ ((H.event i).incoming.rescale μ hμ).terminalRegularOpen :=
        (rescale_mem_terminalRegularOpen_P6M (G := (H.event i).incoming) μ hμ).mpr y.2
      have h1 := (H.event i).terminal.rescale_metricScalarAt_P6M μ hμ ⟨y.1, hy1⟩ y.2
      exact (div_le_iff_mul_P6M hμ).mpr ((hall ⟨y.1, hy1⟩).trans_eq h1)
    have hL' : L / μ ≤ 0 := (div_le_iff_mul_P6M hμ).mpr (by rw [mul_zero]; exact hL)
    have h := R.scalar_preserving (L / μ) hL' hall' x
    exact le_scaleMetric_P6M (H.event i).outputMetric hμ x h

end GeometricCutoffRecord

/-- consumer：重标度 record 的 static cap 保持 canonical window、名义半径 `r/√μ`，且
`curvature_preserving` 在年龄 `a` 可用（原 record 在年龄 `μ a` 的版本）。 -/
example {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) (hcan : ∀ b, (R.static b).hasCanonicalWindow)
    (μ : ℝ) (hμ : 0 < μ) :
    (∀ b, ((R.rescale_P6M μ hμ).static b).hasCanonicalWindow) ∧
      (∀ h, (R.rescale_P6M μ hμ).nominalRadius h = R.nominalRadius h / Real.sqrt μ) ∧
      ∀ b, ((R.rescale_P6M μ hμ).static b).neck.scale = μ * (R.static b).neck.scale :=
  ⟨fun b => (R.static b).hasCanonicalWindow_rescale_P6M (hcan b) μ hμ, fun _ => rfl,
    fun b => (R.static b).rescale_P6M_scale μ hμ⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
