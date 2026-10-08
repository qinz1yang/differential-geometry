import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CapWindowStdCompLate_P6LL
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformCapWindowContinuation

/-!
# cap-window trace 点的局部 `|∂ₜR| ≤ C·R²`：late-records 孪生（O-CH11-HNOT-LOCALDT G1，后缀 `_P6HN`）

**核清（G0 更正）**：树内已有 cap-window trace 点上的导数界，但只有 full-family records 形
（`IsCanonicalCutoffRecordFamily` / `InitialIdentification`）：
* `exists_uniform_derivative_gradient_bounds_of_cap_window_trace`（`CapWindowDerivativeTransfer:68`）：
  固定 `Θ < 1`，常数 `c, C'` 选在输入 `Ctime` 与窗口半径 `D` **之前**（jets 路线：点态 jets 核
  `abs_scalar_derivatives_le_of_scaled_curvature_jets` + C⁴ closeness + 标准解 jets 比较
  `exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens`
  + pullback/scale 搬运）；
* `exists_uniform_capWindowPoint_bounds`（`UniformCapWindowContinuation:29`）：`Ctime₀` 选在
  `(Dcap, θcap)` **之前**，即对 `Dw → ∞`、`θcap → 1` 一致。两段：`T = scale·age ≤ Θ₃` 走上一条；
  `T ≥ Θ₃` 时 `τQ ≤ T·R_S`，标准解高曲率端点给 `OrientedWitness`
  （`exists_uniform_orientedWitness_of_standard_close_endpoint`），再由
  `exists_scalar_derivative_bounds_of_window_orientedWitness`（κ-model 窗）给 Dt。
所以 "θcap → 1 缺标准解一致 jets" 不成立；真正缺的只是 P6 kernel 用的 **late records** 形
（`records : ∀ i, T₀ ≤ time i⁺ → GeometricCutoffRecord`，full family `recordsF` 只交 late delta 界，
HI 显式）。本文件把两条都换到 late 底座 `exists_standard_comparison_of_cap_window_trace_late_P6LL`：
* `capWindow_trace_localDt_theta_P6HN`（固定 `Θ`；`c, C'` 在 `C, D` 之前）：证明逐字取自
  `CapWindowDerivativeBounds:217–287`（生成器切片，`records j ↦ records j hj`）。
* **`capWindow_trace_localDt_P6HN`（G1 主定理）**：`Ctime₀` 在输入 Dt 常数 `C`、`Dcap`、`θcap` 之前，
  结论 `|∂ₜ⁻R(t, y)| ≤ Ctime₀·R(t, y)²` 与梯度界。
**导数前提（未去掉，逐字保留）**：`H.EventSlabsDerivative C qcan k`（slab `< k`）与
`Gk.DerivativeBoundBefore C qcan t`（当前 slab 的 `Ioo (time k) t`）——全在 `t` 之前；它们是
`WindowPersistence:127` Riccati 步（`q·(s − time first) ≤ 1/(2·C·C₀ + 1)`）的结构性输入，
`0 < qcan ≤ Cbirth·scale` 之内 `qcan` 自由。不出现 `t` 处或 `t` 之后的导数界。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance capWindowSigmaCompactP6HN (D : ℝ) :
    SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

namespace RetainedCoreHistory

universe u

/-- **固定 `Θ` 的 late 孪生（`_P6HN`）**：`CapWindowDerivativeTransfer:68` 的 late-records 形。
`c, C'` 只依赖 `Θ`（选在 Dt 输入常数 `C` 与窗口半径 `D` 之前）。 -/
theorem capWindow_trace_localDt_theta_P6HN (Θ : ℝ) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧ ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ D : ℝ, 0 < D →
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      R ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord H.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        pF.delta (H.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ θcap : ℝ), 0 < qcan → θcap ≤ Θ →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative C qcan k →
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ k)
      (y : (H.stage k).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x →
      t - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹ →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records j hj).static b).neck.scale →
      1 ≤ a₀ * ((records j hj).static b).neck.scale →
    c * ((records j hj).static b).neck.scale ≤ Gk.flow.scalar t y ∧
      |derivWithin (fun v => Gk.flow.scalar v y) (Iic t) t| ≤ C' * Gk.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t y v| ≤
          C' * Gk.flow.scalar t y * Real.sqrt (Gk.flow.scalar t y) *
            Real.sqrt ((Gk.flow.base.metric t).inner y v v) := by
  obtain ⟨ε₀, A₀, hε₀, hA₀, hjet₀⟩ :=
    StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens
      Θ hΘ.le hΘ1 0
  obtain ⟨ε₁, A₁, hε₁, hA₁, hjet₁⟩ :=
    StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens
      Θ hΘ.le hΘ1 1
  obtain ⟨ε₂, A₂, hε₂, hA₂, hjet₂⟩ :=
    StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens
      Θ hΘ.le hΘ1 2
  obtain ⟨eta, heta, hlower⟩ := exists_uniform_standard_metric_scalar_lower_comparison Θ hΘ.le hΘ1
  obtain ⟨c₀, hc₀, hscalar₀⟩ := exists_standard_scalar_lower_bound
  set B : ℝ := A₀ + A₁ + A₂ with hBdef
  have hB : 0 ≤ B := by positivity
  set c : ℝ := c₀ / 2 with hcdef
  have hc : 0 < c := by positivity
  set ε : ℝ := min (min ε₀ ε₁) (min ε₂ eta) with hεdef
  have hε : 0 < ε := lt_min (lt_min hε₀ hε₁) (lt_min hε₂ heta)
  refine ⟨c, ((Module.finrank ℝ ThreeSpace : ℝ) ^ 6 * Real.sqrt B +
    2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 4 * B) / c ^ 2 +
    (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt B / (c * Real.sqrt c) + 1, hc,
    by positivity, fun C => ?_⟩
  obtain ⟨P, Creset, Cbirth, -, -, hCbirth, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace_late_P6LL.{u} Θ C hΘ hΘ1
  refine ⟨Cbirth, hCbirth, ?_⟩
  intro D hD
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hwindow⟩ := hbridge D ε ε hD hε hε 4
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro H p T₀ records hcan hRp hmp hζp pF recordsF δbound hdelta hδb qcan a₀ θcap hqcan hθ hHI
    hlow k s Gk hGk hderiv t hkt hts hcur j hj hl y A b x hanchor hage hxD hbirth haq
  obtain ⟨G, L, -, -, hL, -, -, -, -, -, -, -, z, -, hy, Ξ, -, -, hΞmark, hΞ, gflow, S, -, hS2,
      -, -, hS5, -, -, Q, -, hclose⟩ :=
    hwindow H records hcan hRp hmp hζp recordsF δbound hdelta hδb qcan a₀ θcap hqcan hθ hHI
      hlow k s Gk hGk hderiv t hkt hts hcur j hj hl y A b x hanchor hage hxD hbirth haq
  set q := ((records j hj).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j hj).static b).neck.scale_pos
  have hjt : H.time j.succ < t := (H.time_strictMono.monotone hl).trans_lt hkt
  set T := q * (t - H.time j.succ) with hTdef
  have hT0 : 0 ≤ T := mul_nonneg hq.le (sub_nonneg.mpr hjt.le)
  have hTΘ : T ≤ Θ := by
    have h1 : q * (t - H.time j.succ) ≤ q * (θcap * q⁻¹) := mul_le_mul_of_nonneg_left hage hq.le
    have h2 : q * (θcap * q⁻¹) = θcap := by field_simp
    linarith only [h1, h2, hTdef, hθ]
  have hTmem : T ∈ Icc 0 Θ := ⟨hT0, hTΘ⟩
  have hclT := (hclose T ⟨hT0, le_rfl⟩).1
  have hsmall : ∀ i ≤ 4, metricDerivNorm i (S.base.metric T)
      ((Q.val.metric T).restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) z ≤ ε :=
    fun i hi => (hclT i hi z).le
  have hjS : ∀ i ≤ 2, curvDerivNormSq i (S.base.metric T) z ≤ B := by
    intro i hi
    interval_cases i
    · have h := hjet₀ _ (S.base.metric T) Q T hTmem z (fun i hi => (hsmall i (by omega)).trans
        ((min_le_left _ _).trans (min_le_left _ _)))
      linarith only [h, hBdef, hA₁, hA₂]
    · have h := hjet₁ _ (S.base.metric T) Q T hTmem z (fun i hi => (hsmall i (by omega)).trans
        ((min_le_left _ _).trans (min_le_right _ _)))
      linarith only [h, hBdef, hA₀, hA₂]
    · have h := hjet₂ _ (S.base.metric T) Q T hTmem z (fun i hi => (hsmall i (by omega)).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
      linarith only [h, hBdef, hA₀, hA₁]
  have hRS : c ≤ metricScalarAt (S.base.metric T) z := by
    have h := (hlower Q (standardCapWindow D) (S.base.metric T) T hTmem z (fun i hi =>
      (hsmall i (by omega)).trans ((min_le_right _ _).trans (min_le_right _ _)))).2
    rw [metricScalarAt_restrictOpen] at h
    have hQ := hscalar₀ Q z.val T ⟨hT0, hTΘ.trans_lt hΘ1⟩
    have hdiv : c₀ ≤ c₀ / (1 - T) := by
      rw [le_div_iff₀ (by linarith only [hTΘ, hΘ1])]
      nlinarith only [mul_nonneg hc₀.le hT0]
    rw [hcdef]
    linarith only [h, hQ, hdiv]
  have htimeT : H.time j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST : S.base.metric T = localPullMetric (scaleMetric q hq (gflow t)) Ξ hΞ := by
    have h := hS5 T
    rwa [htimeT] at h
  have hgt : gflow t = H.toHistory.backwardSurvivorIncomingMetric j.succ k hl G L t :=
    hS2 t ⟨hkt.le, le_rfl⟩
  have hpoint : (Ξ z).val.val = y :=
    congrArg Subtype.val hΞmark
  have hscalarT : metricScalarAt (S.base.metric T) z = q⁻¹ * Gk.flow.scalar t y := by
    rw [hST, metricScalarAt_localPullMetric_scaleMetric, hgt,
      ObservedHistory.metricScalarAt_backwardSurvivorIncomingMetric_terminal _ _ _ _ _ _
        (Gk.flow.base.metric t) hL, hpoint]
    rfl
  have hjG : ∀ i ≤ 2, curvDerivNormSq i (Gk.flow.base.metric t) y ≤ q ^ (i + 2) * B := by
    intro i hi
    have h := curvDerivNormSq_localPullMetric_scaleMetric (gflow t) Ξ hΞ hq i z
    rw [← hST, hgt, ObservedHistory.curvDerivNormSq_backwardSurvivorIncomingMetric_terminal
      _ _ _ _ _ _ (Gk.flow.base.metric t) hL, hpoint] at h
    have h' : curvDerivNormSq i (Gk.flow.base.metric t) y =
        q ^ (i + 2) * curvDerivNormSq i (S.base.metric T) z := by
      rw [h, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq.ne', one_pow, one_mul]
    rw [h']
    exact mul_le_mul_of_nonneg_left (hjS i hi) (pow_nonneg hq.le _)
  have hRG : c * q ≤ Gk.flow.scalar t y := by
    have h : Gk.flow.scalar t y = q * metricScalarAt (S.base.metric T) z := by
      rw [hscalarT, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
    rw [h, mul_comm c q]
    exact mul_le_mul_of_nonneg_left hRS hq.le
  have hreg : t ∈ (RealTimeInterval.closedOpen (H.time k) s Gk.lt).regular := ⟨hkt, hts⟩
  obtain ⟨hd, hg⟩ := abs_scalar_derivatives_le_of_scaled_curvature_jets Gk.flow Gk.equation hreg
    hq hB hc y hjG hRG
  exact ⟨hRG, hd, hg⟩

/-- **G1 主定理（`_P6HN`，PROVED）**：late-records cap-window trace 点 `(t, y)` 上
`|∂ₜ⁻R(t, y)| ≤ Ctime₀·R(t, y)²`（及梯度界）。`Ctime₀` 选在 Dt 输入常数 `C`、窗口半径 `Dcap`、年龄
上界 `θcap < 1` **之前**——对 `Dw → ∞`、`θcap → 1` 一致、与 `C` 无关。`UniformCapWindowContinuation:29`
的 Dt / 梯度子句的 late 孪生（HI、birth 尺度显式；canonical witness 子句不取）。导数前提全在 `t` 之前。
`Cbirth` 只依赖 `(C, θcap)`（选在 `Dcap` 之前）。 -/
theorem capWindow_trace_localDt_P6HN :
    ∃ Ctime₀ : ℝ≥0, 0 < Ctime₀ ∧ ∀ C : ℝ≥0, ∀ θcap : ℝ, θcap < 1 →
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ Dcap : ℝ, 0 < Dcap →
    ∃ (Rcap : ℝ) (mcap : ℕ), Dcap + 1 < Rcap ∧
    ∃ ζcap δcap : ℝ, 0 < ζcap ∧ 0 < δcap ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      Rcap ≤ p.modelRadius → mcap ≤ p.modelOrder → p.modelAccuracy ≤ ζcap →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord H.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        pF.delta (H.time i.succ) ≤ δbound) →
      δbound ≤ δcap →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative C qcan k →
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ k)
      (y : (H.stage k).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x →
      t - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹ →
      ‖x.val‖ < Dcap + 1 →
      qcan ≤ Cbirth * ((records j hj).static b).neck.scale →
      1 ≤ a₀ * ((records j hj).static b).neck.scale →
    |derivWithin (fun v => Gk.flow.scalar v y) (Iic t) t| ≤
        (Ctime₀ : ℝ) * Gk.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t y v| ≤
          (Ctime₀ : ℝ) * Gk.flow.scalar t y * Real.sqrt (Gk.flow.scalar t y) *
            Real.sqrt ((Gk.flow.base.metric t).inner y v v) := by
  obtain ⟨τQ, hτQ, hL6⟩ :=
    exists_uniform_orientedWitness_of_standard_close_endpoint (δ := 1 / 4) (by norm_num)
      (by norm_num)
  obtain ⟨CA, hCA, hA⟩ :=
    OrientedThreeStage.IncomingSlab.exists_scalar_derivative_bounds_of_window_orientedWitness.{u}
  obtain ⟨c₀, hc₀, hQlow⟩ := exists_standard_scalar_lower_bound
  set Θ₃ := 2 * τQ / (c₀ + 2 * τQ) with hΘ₃def
  have hΘ₃ : 0 < Θ₃ := by positivity
  have hΘ₃1 : Θ₃ < 1 := by rw [hΘ₃def, div_lt_one (by positivity)]; linarith
  obtain ⟨cB, CB, hcB, hCB, hyoung⟩ := capWindow_trace_localDt_theta_P6HN.{u} Θ₃ hΘ₃ hΘ₃1
  set Ctime₀ : ℝ≥0 := ⟨max CA CB, le_max_of_le_left hCA.le⟩ with hC₀def
  have hC₀ : (Ctime₀ : ℝ) = max CA CB := rfl
  refine ⟨Ctime₀, by rw [← NNReal.coe_pos, hC₀]; exact lt_max_of_lt_left hCA, ?_⟩
  intro C θcap hθcap
  set Θ := max θcap (1 / 2) with hΘdef
  have hΘ1 : Θ < 1 := max_lt hθcap (by norm_num)
  have hΘ0 : 0 < Θ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨eta, heta, hlower⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison Θ hΘ0.le hΘ1
  obtain ⟨Pb, Creset, Cb1, -, -, hCb1, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace_late_P6LL.{u} Θ C hΘ0 hΘ1
  obtain ⟨Cb2, hCb2, hy2⟩ := hyoung C
  refine ⟨min Cb1 Cb2, lt_min hCb1 hCb2, fun Dcap hDcap => ?_⟩
  obtain ⟨DW, NW, eW, hDW, heW, hwit⟩ := hL6 Θ (Dcap + 1) hΘ1
  obtain ⟨R1, hR1, m1, -, ζ1, δ1, hζ1, -, hδ1', hbr⟩ :=
    hbridge DW eW eta (by linarith) heW heta NW
  obtain ⟨R2, hR2, m2, -, ζ2, δ2, hζ2, -, hδ2, hyc⟩ := hy2 Dcap hDcap
  refine ⟨max R1 R2, max m1 m2, hR2.trans_le (le_max_right _ _),
    min ζ1 ζ2, min δ1 δ2, lt_min hζ1 hζ2, lt_min hδ1' hδ2, ?_⟩
  intro H p T₀ records hcan hrad hord hacc pF recordsF δbound hdelta hδb qcan a₀ hqcan hHI1
    hHI2 k s Gk hGk hderiv t hkt hts hcur j hj hl y A b x hanchor hage hxD hbirth haq
  set q := ((records j hj).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j hj).static b).neck.scale_pos
  have hba : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hl
  have hθΘ : θcap ≤ Θ := le_max_left _ _
  have hxD' : ‖x.val‖ < DW + 1 := by linarith
  have hbirth1 : qcan ≤ Cb1 * q :=
    hbirth.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le)
  have hbirth2 : qcan ≤ Cb2 * q :=
    hbirth.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hq.le)
  obtain ⟨G, L, hG, -, hL, -, -, -, -, -, -, -, z, hzx, hy, Ξ, -, -, hΞmark, hΞ, gflow, S,
      -, hS2, hS3, -, hS5, -, -, Q, -, hclose⟩ :=
    hbr H records hcan ((le_max_left _ _).trans hrad) ((le_max_left _ _).trans hord)
      (hacc.trans (min_le_left _ _)) recordsF δbound hdelta (hδb.trans (min_le_left _ _))
      qcan a₀ θcap hqcan hθΘ hHI1 hHI2 k s Gk hGk hderiv t hkt hts hcur
      j hj hl y A b x hanchor hage hxD' hbirth1 haq
  have hyz : (Ξ z).val.val = y := congrArg Subtype.val hΞmark
  set T := q * (t - H.time j.succ) with hTdef
  have hjt : H.time j.succ < t := hba.trans_lt hkt
  have hT0 : 0 ≤ T := mul_nonneg hq.le (by linarith)
  have hTθ : T ≤ θcap := by
    have h1 := mul_le_mul_of_nonneg_left hage hq.le
    rwa [mul_comm θcap, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
  have hTmem : T ∈ Icc 0 T := ⟨hT0, le_rfl⟩
  have htT : H.time j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST := H.capWindow_flow_metric_eq Gk hl hΞ hq hG hL hS2 hS5 T hTmem
    (by rw [htT]; linarith)
  rw [htT] at hST
  have hΦ := H.toHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val j.succ k hl G hΞ
  have hCAt : CA ≤ (Ctime₀ : ℝ) := by rw [hC₀]; exact le_max_left _ _
  have hCBt : CB ≤ (Ctime₀ : ℝ) := by rw [hC₀]; exact le_max_right _ _
  by_cases hyng : t - H.time j.succ ≤ Θ₃ * q⁻¹
  · obtain ⟨hcR, hd, hg⟩ := hyc H records hcan ((le_max_right _ _).trans hrad)
      ((le_max_right _ _).trans hord) (hacc.trans (min_le_right _ _)) recordsF δbound hdelta
      (hδb.trans (min_le_right _ _)) qcan a₀ Θ₃ hqcan le_rfl hHI1 hHI2 k s Gk hGk hderiv t hkt
      hts hcur j hj hl y A b x hanchor hyng hxD hbirth2 haq
    have hR0 : 0 ≤ Gk.flow.scalar t y := le_trans (mul_nonneg hcB.le hq.le) hcR
    refine ⟨hd.trans (mul_le_mul_of_nonneg_right hCBt (sq_nonneg _)), fun v => (hg v).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCBt hR0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · have hTΘ₃ : Θ₃ ≤ T := by
      have h1 := mul_le_mul_of_nonneg_left (not_le.mp hyng).le hq.le
      rwa [mul_comm Θ₃, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
    have hT1 : T < 1 := by linarith only [hTθ, hθcap]
    have hlow := (hlower Q (standardCapWindow DW) (S.base.metric T) T
      ⟨hT0, hTθ.trans hθΘ⟩ z (fun i hi => ((hclose T hTmem).2 i hi z).le)).2
    rw [metricScalarAt_restrictOpen] at hlow
    have hτ := le_mul_of_half_standard_scalar_lower hτQ.le hc₀ hT1
      (hQlow Q z.val T ⟨hT0, hT1⟩) hlow hTΘ₃
    have hw : ∀ o, OrientedWitness S o (1 / 4) standardModelKappa z T := fun o =>
      hwit Q T hT0 (hTθ.trans hθΘ) S hS3 (fun τ hτ' => (hclose τ hτ').1) o z
        (by rw [hzx]; linarith) hτ
    have h := hA Gk S hS3 hΦ hq hkt hts le_rfl hST hw le_rfl Ctime₀ Ctime₀ hCAt hCAt
    subst hyz
    exact h

end RetainedCoreHistory

/-- consumer（`_P6HN`）：G1 主定理的 Dt 子句即 `HasSpatialCanonicalTimeControl` 时间半在 incoming
slab 上的形（`Ctime₀ ≤ Ctime'` 单调放大）。 -/
example {Ctime₀ Ctime' : ℝ≥0} (hC : Ctime₀ ≤ Ctime') {P : OrientedThreeStage.{0}} {a s : ℝ}
    (Gk : P.IncomingSlab a s) (t : ℝ) (y : P.Carrier)
    (h : |derivWithin (fun v => Gk.flow.scalar v y) (Iic t) t| ≤
      (Ctime₀ : ℝ) * Gk.flow.scalar t y ^ 2) :
    |derivWithin (fun v => Gk.flow.scalar v y) (Iic t) t| ≤
      (Ctime' : ℝ) * Gk.flow.scalar t y ^ 2 :=
  h.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hC) (sq_nonneg _))

/-- consumer（`_P6HN`）：主定理的常数 `Ctime₀` 在 `(C, Dcap, θcap)` 之前取定——对任意 `n`，`Dcap = n + 1`、
`θcap = 1 − 1/(n+2)` 用同一个 `Ctime₀`（这里取输入 `C = Ctime₀`）。 -/
example : ∃ Ctime₀ : ℝ≥0, 0 < Ctime₀ ∧ ∀ n : ℕ,
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∃ Rcap : ℝ, ((n : ℝ) + 1) + 1 < Rcap := by
  obtain ⟨Ctime₀, hC₀, hall⟩ := RetainedCoreHistory.capWindow_trace_localDt_P6HN.{0}
  refine ⟨Ctime₀, hC₀, fun n => ?_⟩
  have hθ : 1 - 1 / ((n : ℝ) + 2) < 1 := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  obtain ⟨Cbirth, hCb, hD⟩ := hall Ctime₀ (1 - 1 / ((n : ℝ) + 2)) hθ
  obtain ⟨Rcap, -, hR, -⟩ := hD ((n : ℝ) + 1) (by positivity)
  exact ⟨Cbirth, hCb, Rcap, hR⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
