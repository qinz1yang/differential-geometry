import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceAnchor_P6L

/-!
# `hbcad` ⇐ **窗口**切片二分（O-CH11-P6ANCH G2v，后缀 `_P6L`）

G2 `hbcad_of_slice_dichotomy_P6L` 的切片前提 `hslice` 按固定时间偏移 `σ'`（切片 `v = σ n + σ'/R n`）量化；
本文件把它换成**窗口一致**形 `hsliceW`（`∀ T > 0`，窗口 `[σ n − T/R n, σ n]` 内每个切片 `v`），与 G2w
（P6GEO `hscal` 的窗口切片二分）同一量化方式——窗口 BCAD 一份前提同时喂 `hbcad` 与 `hscal`（中心曲率
条件：`hbcad` 自带 `R(tr₁) ≤ A·R_n`；`hscal` 由 G2c traced region 给）。证明：`σ' < 0` 时取 `T := −σ'`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

universe u

/-- **`_P6L`（窗口版 `hbcad`）**：窗口一致的切片二分 `hsliceW` ⇒ K 层双 trace BCAD（G5c / P6ClosureP6D2
逐字形）。 -/
theorem ObservedHistory.hbcad_of_window_slice_dichotomy_P6L :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∀ (Kh : ℕ → ObservedHistory.{u}) (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R : ℕ → ℝ), (∀ n, 0 < R n) →
    (∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ T : ℝ, 0 < T → ∀ Dw : ℝ, 0 < Dw → ∀ᶠ n in atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁,
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        ∃ CWP : ((Kh n).stage ((Kh n).activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w → ∀ x,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) x ≤
              QB * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w) ∧
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((Kh n).stage ((Kh n).activeStage v)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((Kh n).stageMetric ((Kh n).activeStage v) v)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) →
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
      ∀ᶠ n in atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
      ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₂),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤
          C * R n := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, hG2⟩ := ObservedHistory.hbcad_of_slice_dichotomy_P6L.{u}
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, fun Kh σ y R hR hsliceW => hG2 Kh σ y R hR ?_⟩
  intro A Dd hA hDd
  obtain ⟨QB, Dcap, D₂, hQB, hD₂, hsl⟩ := hsliceW A Dd hA hDd
  refine ⟨QB, Dcap, D₂, hQB, hD₂, fun σ' hσ' Dw hDw => ?_⟩
  filter_upwards [hsl (-σ') (neg_pos.mpr hσ') Dw hDw] with n hn
  intro x₁ hx₁ v hvt hv tr₁ hA1
  refine hn x₁ hx₁ v hvt ?_ tr₁ hA1
  rw [hv, neg_div]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
