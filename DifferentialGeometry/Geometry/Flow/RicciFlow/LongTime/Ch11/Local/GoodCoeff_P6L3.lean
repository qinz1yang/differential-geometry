import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.EarlierGoodTraceLocal_P6N

/-!
# L9 / L10 / L11 的阈值系数参数化（`4Q` → `Cg·Q`；O-CH11-P6ANCH3 G5，后缀 `_P6L3`）

`Local/EarlierGoodTraceLocal_P6N` 的三个 selection 引理逐字副本，只把 `hgood` 与结论里的阈值 `4 * Q`
换成任意系数 `Cg * Q`（证明体逐字：阈值只是透传）。用途：P6BND2 左移重跑给出的 `hgood` 阈值是 `8R`，
冻结主形与 P6M 级 selection 引理写死 `4R`（lead 派 G5）。
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

variable (H : ObservedHistory.{u})

/-- **L9（`_Cg_P6L3`，阈值 `Cg·Q`）**：selection 末项 `hgood` + 显式 `hdist` ⇒ 窗口 `[s − θ/Q, s]` 内、
`U = B_s(y, Rad/√Q)`
中点的 backward trace 点（`R ≥ 4Q`）全 Good。 -/
theorem hasSpatialCanonicalTimeControl_on_window_traces_Cg_P6L3
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) (hsT : s ≤ T) (has : aSeed ≤ s)
    {p : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q L θ Rad : ℝ} (hQ : 0 < Q)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ s),
      (s : ℝ) - L ^ 2 / Q ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage s) s)
              (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Q) →
        Cg * Q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hθ : θ ≤ L ^ 2) (hwin : (aSeed : ℝ) ≤ s - θ / Q)
    (hdist : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT)))
            (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) ≤
          riemannianEDistOf (H.stageMetric (H.activeStage s) s)
              (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Q)) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
        Cg * Q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) := by
  intro x hx v hvs hθv tr hR
  have hav : aSeed ≤ v := hwin.trans hθv
  have hLθ : (s : ℝ) - L ^ 2 / Q ≤ (s : ℝ) - θ / Q :=
    sub_le_sub_left (div_le_div_of_nonneg_right hθ hQ.le) _
  exact hgood v hav hvs (hLθ.trans hθv) _ (hdist x hx v hav hvs hθv tr) hR

/-- **L10（`_Cg_P6L3`，阈值 `Cg·Q`）**：L9 的时间导数分量 = 窗口形 footprint `hslabs`/`hder`（ObservedHistory 形，
stage 度量；`4Q < R`、`time (activeStage v) < v < horizon`）。 -/
theorem derivative_footprint_on_window_traces_Cg_P6L3
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ} {s : Icc (0 : ℝ) H.horizon}
    (y : (H.stageAt s).Carrier) {Q θ Rad : ℝ}
    (hgoodW : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
        Cg * Q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs))) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
        H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
        Cg * Q < metricScalarAt (H.stageMetric (H.activeStage v) v)
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) →
        |derivWithin (fun w => metricScalarAt (H.stageMetric (H.activeStage v) w)
            (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs))) (Iic (v : ℝ)) v| ≤
          Ctime' * metricScalarAt (H.stageMetric (H.activeStage v) v)
            (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) ^ 2 :=
  fun x hx v hvs hθv tr hage htop hR => (hgoodW x hx v hvs hθv tr hR.le).2 hage htop

/-- **L11（`_Cg_P6L3`，阈值 `Cg·Q`）**：终端时刻 `s`，`U = B_s(y, Rad/√Q)` 中 `R ≥ 4Q` 的点 Good——**不需 `hdist`**：
`Rad ≤ L` 时 `d_s(O, x) ≤ d_s(O, y) + d_s(y, x) < d_s(O, y) + L/√Q`。 -/
theorem hasSpatialCanonicalTimeControl_at_terminal_of_selection_Cg_P6L3
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) (hsT : s ≤ T) (has : aSeed ≤ s)
    {p : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q L Rad : ℝ} (hQ : 0 < Q)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ s),
      (s : ℝ) - L ^ 2 / Q ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage s) s)
              (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Q) →
        Cg * Q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hRad : Rad ≤ L) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      Cg * Q ≤ metricScalarAt (H.stageMetric (H.activeStage s) s) x →
      H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' s x := by
  intro x hx hR
  have hwin : (s : ℝ) - L ^ 2 / Q ≤ (s : ℝ) :=
    sub_le_self _ (div_nonneg (sq_nonneg L) hQ.le)
  refine hgood s has le_rfl hwin x ?_ hR
  have hyx : riemannianEDistOf (H.stageMetric (H.activeStage s) s) y x ≤
      ENNReal.ofReal (L / Real.sqrt Q) :=
    (le_of_lt hx).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hRad (Real.sqrt_nonneg Q)))
  exact (riemannianEDistOf_triangle _ _ y x).trans (add_le_add le_rfl hyx)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
