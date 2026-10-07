import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceSliceTerminalWindow_P6WB

/-!
# `SliceTerminal:336` 序列形的**窗口版**（O-CH11-P6ANCH G1w，后缀 `_P6M`）

P6WIN-B 已交 SLT:45/249 的时间窗形
`RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB`
（常数 `∃ Q Λ Dcap Rrad ζ₀ Rad Bw`，history 前取；late records 阈值 `T₀ ≤ t − Bw/R`；`hslabs` / `hder` /
`hgrad` / pinching / `hnc` 只在窗口 `[t − Bw/R, t]`）。本文件给它的 `filter_upwards` 序列形（同本车道 G1
对 `_P6L` 的做法），并把 U 侧改成**半径索引**形：
* `Rad`、`Bw` 都依赖 `A`（history 前取）⇒ U 侧前提写成 `∀ Rad (B), ∀ᶠ n, [在 B(y n, Rad/√R n) 上、窗口
  深度 B]`（逐 n 取 `U := B(y n, Rad/√R n)`，`hU` 平凡）；pinching 写成 `∀ B, ∀ᶠ n`；late records 阈值
  `T₀ n` 只要 `∀ B, ∀ᶠ n, T₀ n ≤ t n − B/R n`。这正是 selection Good 区（`Rad ≤ L n`、`B ≤ L n²`
  eventually）与 `Pre841`（`∀ D L B, ∀ᶠ n`）的输出形。
* consumer `hanchor0_of_closure_data_window_P6M`：P6ClosureP6D2 / G5c 的数据前提（全 family、全局
  `hslab` / `hderG` / pinching）+ 半径索引的 `hW` / `hgrad` / 窗口 `hnc` + `hρ` ⇒ `hanchor0` 逐字形（`Q ≥ 2`）。
  与 G1（`_P6L`）相比，`hnc` 只要窗口内——可由 `Pre841` 经 G3 桥给出。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`_P6M`（SLT:336 序列形，窗口版）**：底层 `…_window_P6WB`；U 侧半径索引 + 窗口深度索引
（`∀ Rad B, ∀ᶠ n`），late records 阈值 `T₀ n`（`∀ B, ∀ᶠ n, T₀ n ≤ t n − B/R n`）。 -/
theorem RetainedCoreHistory.eventually_scalar_bound_at_distance_window_P6M
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cq θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (t : ℕ → ℝ) (ht : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n)
    (hts : ∀ n, t n < s n) (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hqy : ∀ n, q n ≤ Cq * ((G n).flow.scalar (t n) (y n)))
    (hR : Tendsto (fun n => ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (hRt : Tendsto (fun n => ((G n).flow.scalar (t n) (y n)) * t n) atTop atTop)
    {p : ℕ → CutoffParameters} (T₀ : ℕ → ℝ)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / ((G n).flow.scalar (t n) (y n)))
    (records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n))
    (hcan : ∀ n i hT b, ((records n i hT).static b).hasCanonicalWindow)
    (hradius : Tendsto (fun n => (p n).modelRadius) atTop atTop)
    (horder : ∀ n, 2 ≤ (p n).modelOrder)
    (haccuracy : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ)
    (hW : ∀ Rad : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))), q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hslabs : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ Btr : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < ((H n).toHistory.event j).incoming.flow.scalar v
        (Btr.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
        (Btr.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hder : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x →
      |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
        Ctime * (G n).flow.scalar v x ^ 2)
    (hgrad : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x → ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt (((G n).flow.base.metric v).inner x w w))
    (hpinch : ∀ B : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩
          Ici (t n - B / ((G n).flow.scalar (t n) (y n)))) phi)
    (hpinchG : ∀ B : ℝ, ∀ᶠ n in atTop, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩
        Ici (t n - B / ((G n).flow.scalar (t n) (y n)))) phi)
    (hnc : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
        t n - B / ((G n).flow.scalar (t n) (y n)) ≤ T →
        let Bh := (H n).extendHorizon T (hend n ▸ hT.le) ((G n).closedPrefix T hT hTs) (hG n)
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, (H n).horizon_nonneg.trans (hend n ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ n →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b))
    (hρ : Tendsto (fun n => ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (D θ : ℕ → ℝ) (hD : Tendsto D atTop atTop) (hθ : ∀ n, θ₀ ≤ θ n)
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hT : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (Btr : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      Btr.point j.succ le_rfl hl = ((records n j hT).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θ n * (((records n j hT).static b).neck.scale)⁻¹) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * ((G n).flow.scalar (t n) (y n)) := by
  intro A hA
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, _, _, _, hζ₀, _, hmain⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB
      hεle κ C1 C2 hκ Ctime Cgrad hphi A hA Cq θ₀ hθ₀
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hradius.eventually_ge_atTop Rrad, haccuracy ζ₀ hζ₀, hR.eventually_ge_atTop Λ,
    hRt.eventually_ge_atTop Λ, hρ.eventually_ge_atTop Λ, hD.eventually_ge_atTop Dcap, hT₀ Bw,
    hW Rad, hslabs Rad Bw, hder Rad Bw, hgrad Rad Bw, hpinch Bw, hpinchG Bw, hnc Rad Bw]
    with n hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9 hn10 hn11 hn12 hn13 hn14
  refine hmain (H n) (hend n) (G n) (hG n) (ht n) (hts n) (y n) (q n) (ρ n) (hq n) (hqy n) hn3
    hn4 (T₀ n) hn7 (records n) (hcan n) hn1 (horder n) hn2 _ (fun _ hw => hw) hn8 hn9 hn10 hn11
    hn12 hn13 hn14 hn5 ?_
  rintro ⟨j, hT, hl, Btr, b, x, h1, h2, h3⟩
  refine hnot n ⟨j, hT, hl, Btr, b, x, h1, by linarith, h3.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (hθ n)
    (inv_nonneg.mpr ((records n j hT).static b).neck.scale_pos.le)

/-- **consumer（窗口版 ⇒ P6ClosureP6D2 / G5c 的 `hanchor0`）**：数据前提（全 family、全局 `hslab` /
`hderG` / pinching、`hnot`、`hRt`）+ 半径索引 `hW` / `hgrad`（阈值 `2·qcan`）+ 窗口 `hnc` + `hρ` ⇒
`hanchor0` 逐字形（`∃ Q ≥ 2`）。late 阈值取 `T₀ = 0`（`hRt` ⇒ eventually `0 ≤ t − B/R`）。 -/
theorem RetainedCoreHistory.hanchor0_of_closure_data_window_P6M
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t ρ : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < ((G n).flow.scalar (t n) (y n)))
    (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n)
      (D n) (θcap n))
    (hRt : Tendsto (fun n => ((G n).flow.scalar (t n) (y n)) * t n) atTop atTop)
    (hW : ∀ Rad : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))), 2 * qcan n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hgrad : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      2 * qcan n < (G n).flow.scalar v x → ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt (((G n).flow.base.metric v).inner x w w))
    (hnc : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
        t n - B / ((G n).flow.scalar (t n) (y n)) ≤ T →
        let Bh := (H n).extendHorizon T (hend n ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, (H n).horizon_nonneg.trans (hend n ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ n →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b))
    (hρ : Tendsto (fun n => ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * ((G n).flow.scalar (t n) (y n)) := by
  have hq0 (n : ℕ) : 0 < qcan n := by
    have := hqcan n
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun n => ((G n).flow.scalar (t n) (y n))) atTop atTop :=
    tendsto_atTop_mono (fun n => (hqcan n).trans (hqR n).le) hnat
  have hradius : Tendsto (fun n => (p n).modelRadius) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) hnat
    rw [(hrec n).2.1]
    exact (hpar n).2.1.trans (hpar n).2.2.1
  have hDt : Tendsto D atTop atTop := tendsto_atTop_mono (fun n => (hpar n).2.1) hnat
  have hacc : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ := by
    intro ζ hζ
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hζ)] with n hn
    rw [(hrec n).2.2.2.1]
    exact (hpar n).1.trans hn
  have hθ (n : ℕ) : (1 : ℝ) / 2 ≤ θcap n := by
    refine le_trans ?_ (hθcap n)
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith
  have hord (n : ℕ) : 2 ≤ (p n).modelOrder := by
    rw [(hrec n).2.2.1]
    exact le_trans (by omega) (hpar n).2.2.2.1
  have hctime : ((2 * Ctime : ℝ≥0) : ℝ) = 2 * (Ctime : ℝ) := by push_cast; ring
  have hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, (0 : ℝ) ≤ t n - B / ((G n).flow.scalar (t n) (y n)) := by
    intro B
    filter_upwards [hRt.eventually_ge_atTop B] with n hn
    have hRn : 0 < ((G n).flow.scalar (t n) (y n)) := (hq0 n).trans (hqR n)
    rw [sub_nonneg, div_le_iff₀ hRn]
    linarith [mul_comm ((G n).flow.scalar (t n) (y n)) (t n)]
  intro A hA
  obtain ⟨Q, hQ, hev⟩ := RetainedCoreHistory.eventually_scalar_bound_at_distance_window_P6M
    (Ctime := 2 * Ctime) (Cq := 2) hεle hκ hphi (by norm_num : (0 : ℝ) < 1 / 2) H hend s G hGi t
    hat hts y (fun n => 2 * qcan n) ρ (fun n => by have := hq0 n; positivity)
    (fun n => by have := hqR n; linarith) hR hRt (fun _ => 0) hT₀ (fun n i _ => records n i)
    (fun n i _ b => (hrec n).2.2.2.2.2.1 i b) hradius hord hacc hW
    (fun Rad B => Eventually.of_forall fun n j first hf z _ Btr v hv _ hRv => by
      have hlt : qcan n < ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) := by
        have := hq0 n
        linarith
      have h := hslab n j (Fin.castSucc_lt_last j) _ v hv hlt
      rw [hctime]
      have h0 : 0 ≤ (Ctime : ℝ) * ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) ^ 2 :=
        mul_nonneg Ctime.coe_nonneg (sq_nonneg _)
      linarith)
    (fun Rad B => Eventually.of_forall fun n x _ v hv _ hRv => hderG n x v hv hRv) hgrad
    (fun B => Eventually.of_forall fun n j v hv w => (hpinch n).1 j v hv.1 w)
    (fun B => Eventually.of_forall fun n v hv w => (hpinch n).2 v hv.1 w) hnc hρ D θcap hDt hθ
    (fun n => by
      rintro ⟨j, _, hl, Btr, b, x, h1, h2, h3⟩
      exact hnot n ⟨j, hl, Btr, b, x, h1, h2, h3⟩) A hA
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  filter_upwards [hev] with n hn z hz
  refine (hn z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact ((hq0 n).trans (hqR n)).le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
