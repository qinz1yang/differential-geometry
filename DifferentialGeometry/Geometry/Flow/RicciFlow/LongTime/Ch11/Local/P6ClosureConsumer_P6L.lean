import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceSliceTerminal_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterGood_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterTrunc_P6L

/-!
# G5 收口 consumer：L6 E-local 链 ↔ P6A point selection ↔ P6D 恢复定理（O-CH11-P6A3）

各层 `U = univ` 推回原全局形的 consumer 在各自文件末尾（G1 BTCC:358/409、G2 SL:73、G3 TP:33/97、
TL:47、G4 SLT:249）。本文件给两个跨层 example：
1. **selection ⇒ (D2) 时间余量**（R-C11-2 D-6）：树内 point selection
   `ObservedHistory.exists_localized_canonical_time_control_point_selection`
   （`ST/CanonicalTimeControlPointSelection:55`）在 `R0_n r_n² → ∞` 时，取 AD-age 的
   `L_n = (R0_n r_n²)^{1/4} → ∞`，eventually 输出坏点 `(s_n, y_n)`（`¬Good`）且
   `L_n² ≤ Q_n (s_n − (T_n − r_n²/2))`（`Q_n = R(s_n, y_n)`）。
2. **反证收口形**：selection 序列的 `¬Good` + P6D G2 的 eventual 完整 Good（预选常数）⇒ `False`
   （AD-good，D-9.2）。
**P6 反证收口仍缺（精确）**——把 selection 输出喂进 SLT:249_P6L / TP:97_P6L 还要：
(a) P6A L9–L11：selection 末项"窗口 `[s − L²/Q, s]` 内距种子 trace `≤ d(O, y) + L/√Q` 且 `R ≥ 4Q` 的点
    Good"⇒ SLT 的 `hW`（`U` 上，`q = 4Q`、`Cq ≥ 4`）、`hder`/`hgrad`、`hslabs` footprint（trace 点上）；
    其中 trace 点的距离控制 = R-C11-2 D-5 的 `hdist`（固定 `A_*`，新车道）；`hslabs` 在
    BTSC 中按整段 event slab `Ioo (time i.castSucc) (time i.succ)` 求值（[V]），而 Good 只在窗口内 ⇒
    需把 BTSC/BTCC 的 `hslabs` 时间域收窄到 `[u, t]`（rev1 §R2 改形标记，未做）。
(b) slice ↔ `RetainedCoreHistory` 终端 incoming slab：selection 在 `ObservedHistory` slice 上，SLT 在
    `RetainedCoreHistory` + `IncomingSlab G`（`hend`、`hG`）上（L-RS / `P6SliceTransportP6A`）。
(c) AD-age：`(a₀+s_n)Q_n → ∞`（已交）之外的全历史抛物重标度对象与 records / slab / pinching transport；
    AD-trunc：丢早期事件的 history 重置构造（或窗口部分 record family 的新 def）。
(d) `hnc`（`U` 中心 tested-ball κ）由 P6B / `Pre841` 的 `hKappaLocal` 供给（D-9.6）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped NNReal Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- consumer 1：selection（逐 `n`）+ AD-age 的 `L_n` 选取 ⇒ eventually 坏点 `(s_n, y_n)` 带 (D2) 余量
`L_n² ≤ Q_n (s_n − (T_n − r_n²/2))`，`L_n → ∞`。 -/
example (H : ℕ → ObservedHistory.{u}) (q : ℕ → CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : ∀ n, AntitoneOn (q n).neckRadius (Ici 0))
    (hcanonical : ∀ n (v : Icc (0 : ℝ) (H n).horizon) (z : ((H n).stageAt v).Carrier),
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ n (v : Icc (0 : ℝ) (H n).horizon) (z : ((H n).stageAt v).Carrier),
      (H n).time ((H n).activeStage v) < (v : ℝ) → (v : ℝ) < (H n).horizon →
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((H n).stageMetric ((H n).activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) z ^ 2)
    (T : ∀ n, Icc (0 : ℝ) (H n).horizon) (p : ∀ n, ((H n).stageAt (T n)).Carrier)
    (r A : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hA : ∀ n, 0 < A n)
    (aSeed : ∀ n, Icc (0 : ℝ) (H n).horizon) (haT : ∀ n, aSeed n ≤ T n)
    (haSeed : ∀ n, (aSeed n : ℝ) = (T n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (H n) ((H n).activeStage (aSeed n))
      ((H n).activeStage (T n)) ((H n).activeStage_mono (haT n)) (p n))
    (x : ∀ n, ((H n).stageAt (T n)).Carrier)
    (hx : ∀ n, x n ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (T n)) (T n)) (p n)
      (A n * r n))
    (hR : ∀ n, 0 < metricScalarAt ((H n).stageMetric ((H n).activeStage (T n)) (T n)) (x n))
    (hbad : ∀ n, ¬ (H n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (T n) (x n))
    (hX : Tendsto (fun n =>
      metricScalarAt ((H n).stageMetric ((H n).activeStage (T n)) (T n)) (x n) * r n ^ 2)
      atTop atTop) :
    ∃ L : ℕ → ℝ, Tendsto L atTop atTop ∧ ∀ᶠ n in atTop,
      ∃ (s : Icc (0 : ℝ) (H n).horizon) (y : ((H n).stageAt s).Carrier),
        ¬ (H n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' s y ∧
        L n ^ 2 ≤ metricScalarAt ((H n).stageMetric ((H n).activeStage s) s) y *
          ((s : ℝ) - ((T n : ℝ) - r n ^ 2 / 2)) := by
  obtain ⟨L, hL, hev⟩ := exists_selection_margin_scale_P6L hR hr hX
  refine ⟨L, hL, ?_⟩
  filter_upwards [hev, hL.eventually_gt_atTop 0] with n hn hLpos
  obtain ⟨s, has, hsT, y, hsel⟩ := (H n).exists_localized_canonical_time_control_point_selection
    (q n) hC1 hC2 hCtime (hanti n) (hcanonical n) (hderivative n) (T n) (p n) (r n) (A n) (L n)
    (hr n) (hA n) hLpos (aSeed n) (haT n) (haSeed n) (seedTrace n) (x n) (hx n) (hR n) (hbad n)
    hn.1 hn.2
  dsimp only at hsel
  obtain ⟨hnot, hQ, -, -, -, hmargin, -⟩ := hsel
  refine ⟨s, y, hnot, ?_⟩
  have h : L n ^ 2 / metricScalarAt ((H n).stageMetric ((H n).activeStage s) s) y ≤
      (s : ℝ) - ((T n : ℝ) - r n ^ 2 / 2) := by linarith
  rwa [div_le_iff₀ hQ, mul_comm] at h

/-- consumer 2（反证收口形，AD-good）：selection 坏点序列 + P6D G2 的 eventual 完整 Good（常数
`C ≤ C1'`、`C ≤ C2'`、`C.toNNReal ≤ Ctime'` 预选）⇒ `False`。 -/
example {eps C C1' C2' : ℝ} {Ctime' : ℝ≥0} (hC1 : C ≤ C1') (hC2 : C ≤ C2')
    (hCt : C.toNNReal ≤ Ctime') (H : ℕ → ObservedHistory.{u})
    (s : ∀ n, Icc (0 : ℝ) (H n).horizon) (y : ∀ n, ((H n).stageAt (s n)).Carrier)
    (hsel : ∀ n, ¬ (H n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (s n) (y n))
    (hP6D : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
      (H (ψ i)).HasSpatialCanonicalTimeControl eps C C C.toNNReal (s (ψ i)) (y (ψ i))) :
    False :=
  false_of_not_good_of_eventually_good_P6L hC1 hC2 hCt H s y hsel hP6D

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
