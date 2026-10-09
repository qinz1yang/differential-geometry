import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.P6ClosureConsumer_P6L

/-!
# G4：P6A L9–L11 —— selection 的"更早时刻 Good" ⇒ trace-local `hW` / `hder` / `hslabs`（`_P6N`）

输入 = 树内 point selection `ObservedHistory.exists_localized_canonical_time_control_point_selection`
（`ST/CanonicalTimeControlPointSelection:55`）末项（记 `hgood`）：对 `v ∈ [s − L²/Q, s]`、
`d_v(seed(v), z) ≤ d_s(O, y) + L/√Q`、`4Q ≤ R(v, z)` 的点 `Good(v, z)`
（`Good = HasSpatialCanonicalTimeControl eps C1' C2' Ctime'`，常数为 selection 的带撇常数）。
本文件（ObservedHistory 层，`U := B_s(y, Rad/√Q)`、窗口 `[s − θ/Q, s]`）：
* **L9** `hasSpatialCanonicalTimeControl_on_window_traces_P6N`：`θ ≤ L²`、`aSeed ≤ s − θ/Q` 与
  **显式前提 `hdist`**（窗口内 `U` 中点的每条 backward trace 的点到种子 trace 的距离
  `≤ d_s(O, y) + L/√Q`）⇒ 窗口内 trace 点（`R ≥ 4Q`）全 Good。
* **L10** `derivative_footprint_on_window_traces_P6N`：⇒ 窗口形 footprint 时间导数界
  （`time (activeStage v) < v < horizon`、`4Q < R` ⇒ `|∂_v R| ≤ Ctime' R²`）——即 SLT 的 `hslabs` / `hder`
  的 ObservedHistory 形（guard `s − θ/Q ≤ v`，与 G1/G2a 的窗口约定同）。
* **L11** `hasSpatialCanonicalTimeControl_at_terminal_of_selection_P6N`：**不需** `hdist`，`Rad ≤ L` +
  三角不等式 ⇒ 终端时刻 `U` 中 `R ≥ 4Q` 的点 Good（SLT 的 `hW`，`q = 4Q`）；
  `scalar_gradient_at_terminal_of_selection_P6N`：witness 的 `gradient` 字段 ⇒ `|∇R| ≤ C2' R^{3/2}`
  （SLT 的 `hgrad`，`Cgrad = C2'`）。
`hdist` 的形状说明（与 R-C11-2 D-5 的关系）见文件末 consumer 的 docstring。不写 sorry；无新 def。
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

/-- **L9（`_P6N`）**：selection 末项 `hgood` + 显式 `hdist` ⇒ 窗口 `[s − θ/Q, s]` 内、`U = B_s(y, Rad/√Q)`
中点的 backward trace 点（`R ≥ 4Q`）全 Good。 -/
theorem hasSpatialCanonicalTimeControl_on_window_traces_P6N
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
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
        4 * Q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
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
        4 * Q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) := by
  intro x hx v hvs hθv tr hR
  have hav : aSeed ≤ v := hwin.trans hθv
  have hLθ : (s : ℝ) - L ^ 2 / Q ≤ (s : ℝ) - θ / Q :=
    sub_le_sub_left (div_le_div_of_nonneg_right hθ hQ.le) _
  exact hgood v hav hvs (hLθ.trans hθv) _ (hdist x hx v hav hvs hθv tr) hR

/-- **L10（`_P6N`）**：L9 的时间导数分量 = 窗口形 footprint `hslabs`/`hder`（ObservedHistory 形，
stage 度量；`4Q < R`、`time (activeStage v) < v < horizon`）。 -/
theorem derivative_footprint_on_window_traces_P6N
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {s : Icc (0 : ℝ) H.horizon}
    (y : (H.stageAt s).Carrier) {Q θ Rad : ℝ}
    (hgoodW : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
        4 * Q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs))) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
        H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
        4 * Q < metricScalarAt (H.stageMetric (H.activeStage v) v)
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) →
        |derivWithin (fun w => metricScalarAt (H.stageMetric (H.activeStage v) w)
            (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs))) (Iic (v : ℝ)) v| ≤
          Ctime' * metricScalarAt (H.stageMetric (H.activeStage v) v)
            (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) ^ 2 :=
  fun x hx v hvs hθv tr hage htop hR => (hgoodW x hx v hvs hθv tr hR.le).2 hage htop

/-- **L11（`_P6N`）**：终端时刻 `s`，`U = B_s(y, Rad/√Q)` 中 `R ≥ 4Q` 的点 Good——**不需 `hdist`**：
`Rad ≤ L` 时 `d_s(O, x) ≤ d_s(O, y) + d_s(y, x) < d_s(O, y) + L/√Q`。 -/
theorem hasSpatialCanonicalTimeControl_at_terminal_of_selection_P6N
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
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
        4 * Q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hRad : Rad ≤ L) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      4 * Q ≤ metricScalarAt (H.stageMetric (H.activeStage s) s) x →
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

/-- **L11′（`_P6N`）**：终端 Good 的 witness `gradient` 字段 ⇒ 空间梯度界 `|dR(w)| ≤ C2' R^{3/2} |w|`
（SLT `hgrad` 在时刻 `s` 的形，`Cgrad = C2'`）。 -/
theorem scalar_gradient_at_terminal_of_good_P6N
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {s : Icc (0 : ℝ) H.horizon} {x : (H.stageAt s).Carrier}
    (hx : H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' s x)
    (w : TangentSpace ThreeModel x) :
    |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
        (metricScalarAt (H.stageMetric (H.activeStage s) s)) x w)| ≤
      C2' * metricScalarAt (H.stageMetric (H.activeStage s) s) x *
        Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage s) s) x) *
        Real.sqrt ((H.stageMetric (H.activeStage s) s).inner x w w) := by
  obtain ⟨⟨W, -⟩, -⟩ := hx
  exact W.gradient w

/-- 序列侧的平凡部分：`L_n → ∞` ⇒ eventually `θ ≤ L_n²` 且 `Rad ≤ L_n`（L9/L11 的两个数值前提）。 -/
theorem eventually_window_scale_le_P6N {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) (θ Rad : ℝ) :
    ∀ᶠ n in atTop, θ ≤ L n ^ 2 ∧ Rad ≤ L n := by
  filter_upwards [hL.eventually_ge_atTop (max (max θ Rad) 1)] with n hn
  have h1 : (1 : ℝ) ≤ L n := (le_max_right _ _).trans hn
  have hθ : θ ≤ L n := ((le_max_left θ Rad).trans (le_max_left _ _)).trans hn
  refine ⟨hθ.trans ?_, ((le_max_right θ Rad).trans (le_max_left _ _)).trans hn⟩
  nlinarith

/-- **consumer（G4 ↔ selection）**：树内 point selection 的输出直接喂 L9 / L11——eventually
（`θ ≤ L²`、`Rad ≤ L`）得坏点 `(s, y)`（`¬Good`）且 `U = B_s(y, Rad/√Q)` 的窗口 trace 点与终端点全 Good。
窗口前提 `aSeed ≤ s − θ/Q` 由 selection 的 (D2) 余量 `T − r²/2 ≤ s − L²/Q` 给（`aSeed = T − r²`）。
**`hdist` 的形状（审稿 R-C11-2 D-5 的对照，记录）**：selection 的 Good 区是**相对**形
`d_v(seed(v), z) ≤ d_s(O, y) + L/√Q`，故这里的 `hdist` 也取相对形（KL 的 point-picking + Perelman I.8.3(b)
距离畸变 + D-8 无捷径给出：窗口长 `θ/Q`、畸变率 `O(√Q)` ⇒ 误差 `O(θ/√Q) ≤ (L − Rad)/√Q`）。D-5 冻结的
**绝对**形 `d_v(O_v, x_v) < A_* r_n` 不蕴含相对形（`L/√Q ≤ r/√2 < A_* r`，且 `d_s(O, y)` 只有上界
`(A+1) r`）——D-5 形服务于 κ 线的种子 confinement，`hdist`（selection 侧）须单独以相对形生产。 -/
example (q : CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcanonical : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt (H.stageMetric (H.activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v) z ^ 2)
    (T : Icc (0 : ℝ) H.horizon) (p : (H.stageAt T).Carrier)
    (r A L : ℝ) (hr : 0 < r) (hA : 0 < A) (hL : 0 < L)
    (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ T)
    (haSeed : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (x : (H.stageAt T).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p (A * r))
    (hR : 0 < metricScalarAt (H.stageMetric (H.activeStage T) T) x)
    (hbad : ¬ H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' T x)
    (htime : 2 * L ^ 2 / metricScalarAt (H.stageMetric (H.activeStage T) T) x ≤ r ^ 2 / 2)
    (hspace : 2 * L / Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage T) T) x) ≤ r / 2)
    (θ Rad : ℝ) (hθ : θ ≤ L ^ 2) (hRad : Rad ≤ L)
    (hdist : ∀ (s : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ s) (hsT : s ≤ T)
      (y : (H.stageAt s).Carrier),
      ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y
          (Rad / Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage s) s) y)),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ s),
        (s : ℝ) - θ / metricScalarAt (H.stageMetric (H.activeStage s) s) y ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT)))
            (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) ≤
          riemannianEDistOf (H.stageMetric (H.activeStage s) s)
              (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage s) s) y))) :
    ∃ (s : Icc (0 : ℝ) H.horizon) (y : (H.stageAt s).Carrier),
      ¬ H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' s y ∧
      (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y
          (Rad / Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage s) s) y)),
        4 * metricScalarAt (H.stageMetric (H.activeStage s) s) y ≤
          metricScalarAt (H.stageMetric (H.activeStage s) s) x →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' s x) ∧
      ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y
          (Rad / Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage s) s) y)),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hvs : v ≤ s),
        (s : ℝ) - θ / metricScalarAt (H.stageMetric (H.activeStage s) s) y ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
        4 * metricScalarAt (H.stageMetric (H.activeStage s) s) y ≤
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) := by
  obtain ⟨s, has, hsT, y, hsel⟩ := H.exists_localized_canonical_time_control_point_selection q hC1
    hC2 hCtime hanti hcanonical hderivative T p r A L hr hA hL aSeed haT haSeed seedTrace x hx hR
    hbad htime hspace
  dsimp only at hsel
  obtain ⟨hnot, hQ, -, -, -, hmargin, -, -, hgood⟩ := hsel
  have hwin : (aSeed : ℝ) ≤ s - θ / metricScalarAt (H.stageMetric (H.activeStage s) s) y := by
    have h1 : θ / metricScalarAt (H.stageMetric (H.activeStage s) s) y ≤
        L ^ 2 / metricScalarAt (H.stageMetric (H.activeStage s) s) y :=
      div_le_div_of_nonneg_right hθ hQ.le
    have h2 : 0 ≤ r ^ 2 := sq_nonneg r
    linarith
  exact ⟨s, y, hnot,
    H.hasSpatialCanonicalTimeControl_at_terminal_of_selection_P6N haT hsT has seedTrace y hQ
      hgood hRad,
    H.hasSpatialCanonicalTimeControl_on_window_traces_P6N haT hsT has seedTrace y hQ hgood hθ
      hwin (hdist s has hsT y)⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
