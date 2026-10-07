import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.EarlierGoodTraceLocal_P6N

/-!
# selection 的 Good 区 + 相对 `hdist` ⇒ P6D G2 的 K 层 `hwit` / `hderiv`（序列形；O-CH11-P6ANCH G5c 续）

把 P6CON G4 的 L9（`hasSpatialCanonicalTimeControl_on_window_traces_P6N`）/ L10
（`derivative_footprint_on_window_traces_P6N`）逐 n 套进 P6D G2
（`exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D`）的 trace-local 前提形
`∀ D T > 0, ∀ᶠ n, ∀ x ∈ B(y n, D/√R n), ∀ v ∈ [σ n − T/R n, σ n), …`：
* `Rad := D`、`θ := T`、`Q := R n`（坏点标量）；阈值 `qs = qd = 4·R n`（`Cs = Cq = 4`）；witness 常数
  `C1s = C1'`、`C2s = C2'`、时间常数 `Ctime'`（selection 的带撇常数）；
* 数值前提 `T ≤ L n²` 由 `L n → ∞` eventually 给（`eventually_window_scale_le_P6N`）；窗口前提
  `aSeed n ≤ σ n − T/R n` 显式 eventually（selection 的 (D2) 余量，P6A3 AdapterAge 已给）；
* **`hdist`**（相对形，D-5 / DIST `hdist_rel_of_stage_bounds_C11D` 的出口）作为显式 eventually 前提。
输出与本车道 G5c `false_of_selection_eventSlab_P6M` 的 `hwit` / `hderivK` 绑定逐字同形。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped NNReal Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **`_P6M`**：selection 的 Good 区（逐 n）+ `L n → ∞` + 窗口余量 + 相对 `hdist` ⇒ P6D G2 形的
`hwit`（阈值 `4 R n`）与 `hderiv`（阈值 `4 R n`、常数 `Ctime'`）。 -/
theorem hwit_hderiv_of_selection_P6M {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (p : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (p n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
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
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1' C2'
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
          Wt.capTubeHasNeckChart eps) ∧
    (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
        |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
          (Iic (v : ℝ)) v| ≤
          Ctime' * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) := by
  have key : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvs : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) := by
    intro D T hD hT
    filter_upwards [eventually_window_scale_le_P6N hL T D, hwin T hT, hdist D T hD hT]
      with n hn hw hd
    exact (Kh n).hasSpatialCanonicalTimeControl_on_window_traces_P6N (haT n) (hsT n) (has n)
      (seedTrace n) (y n) (hR n) (hgood n) hn.1 hw hd
  refine ⟨fun D T hD hT => ?_, fun D T hD hT => ?_⟩
  · filter_upwards [key D T hD hT] with n hn
    intro x hx v hvt hTv _ _ tr hq
    exact (hn x hx v hvt hTv tr hq.le).1
  · filter_upwards [key D T hD hT] with n hn
    intro x hx v hvt hTv hvσ hage tr hq
    exact (Kh n).derivative_footprint_on_window_traces_P6N (y n) hn x hx v hvt hTv tr hage
      (hvσ.trans_le (σ n).2.2) hq

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
