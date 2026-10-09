import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AlphaSecondScaleC11AL

/-!
# (α) 路线 G3：margin split 的 selection 输出形（O-CH11-ALPHA G3，后缀 `_C11AL`）

设计 `docs/geometrization/chapter8/design-C11-alpha-20261007.md` §1：hscalW / HU 的 ExitGuard 余量若与 hgood
同为 `L`，二次重标度集合在 ExitGuard 边界处零余量出域；修复 = 下游整体以 `L/2` 运行。本文件把这一点做成
**可直接替换的 selector 输出**：

* `selection_of_bad_sequence_retained_half_C11AL`：前提与 `selection_of_bad_sequence_retained_P6R2` 相同；
  结论 = P6R2 结论逐字，只是 `L n = √(R₀ r²)/4` 换成 `L n = √(R₀ r²)/8`（`L ↦ L/2`）。hgood 由
  `hgood_mono_C11AL` 降到 `L/2`；room `Tn − r²/2 ≤ σ − L²/R` 对 `L/2` 更弱；`Tendsto` 保持。
* 任何吃 P6R2 / P6X 输出的下游（P6CD、hdistW、hclosG）改吃本定理即得 `L/2` 版，ExitGuard(`L/2`) 与 hgood(`L`) 之间
  留出 `(L/2)/√R` 缓冲——`hgood_secondScale_C11AL`（G1）正是在此缓冲内工作。
* consumer `example`：本定理输出的第一合取分量逐字 = `selection_of_bad_sequence_P6X` 的结论（`L/2` 版仍是合法 P6X 输出）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **margin split 的 selector 输出（G3，`_C11AL`）**：前提 = `selection_of_bad_sequence_retained_P6R2` 逐字；
结论 = P6R2 结论逐字，`L n = √(R₀ r²)/8`（= P6R2 的 `L/2`）。 -/
theorem selection_of_bad_sequence_retained_half_C11AL {Kh : ℕ → ObservedHistory.{u}}
    (q : ℕ → CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : ∀ n, AntitoneOn (q n).neckRadius (Ici 0))
    (hcanonical : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      (Kh n).time ((Kh n).activeStage v) < (v : ℝ) → (v : ℝ) < (Kh n).horizon →
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z ^ 2)
    (Tn : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (r : ℕ → ℝ) (A : ℝ) (hr : ∀ n, 0 < r n) (hA : 0 < A)
    (aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (haSeed : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (x : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (hx : ∀ n, x n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n))
      (pT n) (A * r n))
    (hR : ∀ n, 0 < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n))
    (hbad : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (Tn n) (x n))
    (hdiv : Tendsto (fun n => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n))
      (Tn n)) (x n) * r n ^ 2) atTop atTop) :
    ∃ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n) (L : ℕ → ℝ),
      ((∀ n, R n = metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)) ∧
      (∀ n, 0 < R n) ∧
      (∀ n, metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n) ≤
        R n) ∧
      (∀ n, R n ≤ ((q n).neckRadius (Tn n) ^ 2)⁻¹) ∧
      Tendsto L atTop atTop ∧
      (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (σ n) (y n)) ∧
      (∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
        ∀ z : ((Kh n).stageAt v).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n) ∧
      Tendsto (fun n => R n * ((σ n : ℝ) - ((Tn n : ℝ) - r n ^ 2 / 2))) atTop atTop ∧
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop) ∧
      (∀ n, L n = Real.sqrt (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n))
        (Tn n)) (x n) * r n ^ 2) / 8) ∧
      (∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - L n ^ 2 / R n) ∧
      (∀ n, y n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) ((A + 1) * r n)) := by
  obtain ⟨σ, y, R, hsT, has, L, ⟨hRdef, hQ, hRQ, hQρ, hL, hsel, hgood, hwin, hwin', htend, h200⟩,
    hLdef, hroom, hball⟩ :=
    selection_of_bad_sequence_retained_P6R2 q hC1 hC2 hCtime hanti hcanonical hderivative Tn pT r A
      hr hA aSeed haT haSeed seedTrace x hx hR hbad hdiv
  have hL0 : ∀ n, 0 ≤ L n := fun n => by
    rw [hLdef n]
    positivity
  have hRpos : ∀ n, 0 < R n := hQ
  refine ⟨σ, y, R, hsT, has, fun n => L n / 2,
    ⟨hRdef, hQ, hRQ, hQρ, hL.atTop_div_const (by norm_num), hsel, fun n => ?_, hwin, hwin', htend,
      h200⟩, fun n => ?_, fun n => ?_, hball⟩
  · exact hgood_mono_C11AL (Kh n) (aSeed n) (Tn n) (σ n) (haT n) (hsT n) (has n) (seedTrace n)
      (y n) (hRpos n).le (div_nonneg (hL0 n) zero_le_two) (half_le_self (hL0 n)) (hgood n)
  · change L n / 2 = _
    rw [hLdef n]
    ring
  · have hsq : (L n / 2) ^ 2 ≤ L n ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (hL0 n) zero_le_two) (half_le_self (hL0 n)) 2
    have hdiv' : (L n / 2) ^ 2 / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hsq (hRpos n).le
    change (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - (L n / 2) ^ 2 / R n
    linarith [hroom n]

/-- consumer：本定理输出的第一个合取分量逐字 = `selection_of_bad_sequence_P6X` 的结论（`L/2` 版）。 -/
example : type_of% @selection_of_bad_sequence_P6X.{u} := by
  intro Kh q eps C1 C2 C1' C2' hC1 hC2 Ctime Ctime' hCtime hanti hcanonical hderivative Tn pT r A
    hr hA aSeed haT haSeed seedTrace x hx hR hbad hdiv
  obtain ⟨σ, y, R, hsT, has, L, hmain, -, -, -⟩ := selection_of_bad_sequence_retained_half_C11AL q
    hC1 hC2 hCtime hanti hcanonical hderivative Tn pT r A hr hA aSeed haT haSeed seedTrace x hx hR
    hbad hdiv
  exact ⟨σ, y, R, hsT, has, L, hmain⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
