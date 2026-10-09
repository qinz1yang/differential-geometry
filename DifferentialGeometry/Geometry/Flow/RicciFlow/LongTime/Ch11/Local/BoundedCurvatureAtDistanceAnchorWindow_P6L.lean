import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceAnchor_P6L

/-!
# **窗口 BCAD**（O-CH11-P6ANCH G2w，后缀 `_P6L`）：P6GEO 的 `hscal` ⇐ 窗口切片二分前提

lead 03:48：P6GEO（`Ch11/Dist/EndpointAssemblyC11G.lean`
`exists_hgeom_of_K0_pinching_C11G`）把相对 `hdist` 的几何输入归约后，唯一剩下的曲率输入是
BCAD 形 `hscal`（两分量：末 stage 窗口 `(s − T/R, s)` 内基点球中
`x` 的 `R^{-1/2}`-球、event slab 内 trace 点的 `R^{-1/2}`-球上 `R ≤ C R_n`），与本车道 G2 的 `hbcad` 是同一
事实（KL bounded curvature at bounded distance 在更早切片）。BCAD:375 只给固定 `σ`；本文件给**窗口一致**版：
* 标准解比较常数 `η₃ Cup Lc` 在序列前取（`exists_scalar_metric_comparison_of_standard_close (1/2)`）；
* 前提 `hW`（每个 `D T`，常数 `A ≥ 1, QB ≥ 0, Dcap, D₂` 先取，eventually）：每个窗口中心
  （分量 1：基点球中 `x` 在窗口时刻 `τ`；分量 2：trace 点在 event slab 时刻 `t'`）有 (i) **中心曲率**
  `R(center) ≤ A·R_n`（⇐ P6D2 G3 htraced 的 traced-region 曲率界 + pinching），(ii) **切片二分**：
  中心的 `R_n^{-1/2}`-球内非 cap-window 高曲率点 `w` 有 SLT 型有界曲率（半径 `(2√A+1)/√R(w)`，
  `≤ QB·R(w)`），cap-window 点有标准帽嵌入；
* 结论 = `exists_hgeom_of_K0_pinching_C11G` 的 `hscal` **逐字形**，`C = A·(QB + 2Cup + 1)`。
证明：逐点调 G2 的局部化二分 `scalar_le_of_rebase_capWindow_dichotomy_P6L`（`D = 1`）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

universe u

/-- **`_P6L`（窗口 BCAD）**：窗口切片二分前提 ⇒ P6GEO `exists_hgeom_of_K0_pinching_C11G` 的 `hscal`
（逐字形）。 -/
theorem ObservedHistory.hscal_of_window_dichotomy_P6L :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∀ (Hs : ℕ → ObservedHistory.{u}) (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
      (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
      (R : ℕ → ℝ), (∀ᶠ n in atTop, 0 < R n) →
    (∀ D T : ℝ, 0 < D → 0 < T → ∃ A QB Dcap D₂ : ℝ, 1 ≤ A ∧ 0 ≤ QB ∧
      Dcap + 1 + (2 * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x ≤ A * R n ∧
        ∃ CWP : ((Hs n).stageAt (s n)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
              (x) w <
              ENNReal.ofReal (1 / Real.sqrt (R n)) →
            ¬ CWP w → R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) w →
            ∀ x',
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) w x' <
              ENNReal.ofReal ((2 * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) w)) →
            metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x' ≤
              QB * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) w) ∧
          (∀ w, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
              (x) w <
              ENNReal.ofReal (1 / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((Hs n).stageAt (s n)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        metricScalarAt ((Hs n).stageMetric e.castSucc t')
          (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤ A * R n ∧
        ∃ CWP : ((Hs n).stage e.castSucc).Carrier → Prop,
          (∀ w, riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) w <
              ENNReal.ofReal (1 / Real.sqrt (R n)) →
            ¬ CWP w → R n ≤ metricScalarAt ((Hs n).stageMetric e.castSucc t') w →
            ∀ x',
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t') w x' <
              ENNReal.ofReal ((2 * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((Hs n).stageMetric e.castSucc t') w)) →
            metricScalarAt ((Hs n).stageMetric e.castSucc t') x' ≤
              QB * metricScalarAt ((Hs n).stageMetric e.castSucc t') w) ∧
          (∀ w, riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) w <
              ENNReal.ofReal (1 / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((Hs n).stage e.castSucc).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((Hs n).stageMetric e.castSucc t')) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃))) →
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
            ENNReal.ofReal (1 / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z ≤ C * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier,
          riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
            ENNReal.ofReal (1 / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n) := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, hP3⟩ :=
    exists_scalar_metric_comparison_of_standard_close (1 / 2) (by norm_num) (by norm_num)
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, ?_⟩
  intro Hs s y aSeed R hR hW D T hD hT
  obtain ⟨A, QB, Dcap, D₂, hA, hQB, hD₂, hev⟩ := hW D T hD hT
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  refine ⟨A * (QB + 2 * Cup + 1), by positivity, ?_⟩
  have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  have hsL : 0 ≤ Lc * Real.sqrt (2 * A) := mul_nonneg hLc.le (Real.sqrt_nonneg _)
  filter_upwards [hev, hR] with n hn hRn
  refine ⟨fun x hx τ h1 h2 h3 z hz => ?_, fun x hx v hav hvs hv tr e h3 h4 t' h5 h6 h7 z hz => ?_⟩
  · obtain ⟨hcen, CWP, hB3e, hP1⟩ := hn.1 x hx τ h1 h2 h3
    exact scalar_le_of_rebase_capWindow_dichotomy_P6L _ CWP x (AB := 2 * Real.sqrt A + 1)
      (r := 2 * Lc * Real.sqrt (2 * A) + 1) hRn hA one_pos hQB hCup hLc (by linarith)
      (by linarith) hD₂ hB3e hP1 hP3 z hcen hz
  · obtain ⟨hcen, CWP, hB3e, hP1⟩ := hn.2 x hx v hav hvs hv tr e h3 h4 t' h5 h6 h7
    exact scalar_le_of_rebase_capWindow_dichotomy_P6L _ CWP _ (AB := 2 * Real.sqrt A + 1)
      (r := 2 * Lc * Real.sqrt (2 * A) + 1) hRn hA one_pos hQB hCup hLc (by linarith)
      (by linarith) hD₂ hB3e hP1 hP3 z hcen hz

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
