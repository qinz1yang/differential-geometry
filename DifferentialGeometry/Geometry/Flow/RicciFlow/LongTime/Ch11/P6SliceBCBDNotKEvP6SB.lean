import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDNotKP6SB

/-!
# 切片 BCBD：surgery 避让只需 eventually（O-CH11-SLICE-BCBD G5，后缀 `_P6SB`）

G4 的 `hceil` 上游（CXJD 跨 slab ceiling）只能 eventually 成立（`haS / haL` 走 `hwin`、`L → ∞`），
但 G2 / G3 的 kernel 帧 `hnotK` 写成 `∀ n`。WA2 窗口核只在 `filter_upwards` 里用 `hnot n`，所以三层机械孪生
就能把它换成 `∀ᶠ n`：
* `RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_star_ev_P6SB`（WBADAPT 窗口核）；
* `RetainedCoreHistory.hanchor0_lateW_local_star_theta_ev_P6SB`（G3 θ kernel）；
* **`ObservedHistory.sliceBCBD_kernel_fresh_theta_ev_P6SB`**（G3 主定理）。
consumer：G4 的结论（`∀ n`）经 `Filter.Eventually.of_forall` 喂进来；G3 主定理由本文件推出（`example`）。
生成器 `build-logs/scratch/O-CH11-SLICE-BCBD/gen/gen5.py`（WBADAPT `P6WBAdaptStarP6WA2` + 本车道 G3
切片，assert）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **SLT 窗口核，`hnot` 只需 eventually（`_P6SB`）**：WBADAPT
`eventually_scalar_bound_at_distance_window_local_star_P6WA2` 逐字，`hnot : ∀ n` → `∀ᶠ n`（原证明只在
`filter_upwards` 内用 `hnot n`，故并入过滤列表）。 -/
theorem RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_star_ev_P6SB
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
    (hslabsLocStar : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ Btr : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      (t n - v) * max (q n) ((G n).flow.scalar (t n) z) ≤
        1 / (2 * max (Ctime : ℝ) 1) →
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
    (hnot : ∀ᶠ n in atTop, ¬ ∃ (j : Fin (H n).eventCount) (hT : T₀ n ≤ (H n).time j.succ)
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
    hWBlocStar_of_shortSLT_guarded_P6WA2 ε hεle κ C1 C2 hκ Ctime Cgrad phi hphi A hA Cq θ₀ hθ₀
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hradius.eventually_ge_atTop Rrad, haccuracy ζ₀ hζ₀, hR.eventually_ge_atTop Λ,
    hRt.eventually_ge_atTop Λ, hρ.eventually_ge_atTop Λ, hD.eventually_ge_atTop Dcap, hT₀ Bw,
    hW Rad, hslabsLocStar Rad Bw, hder Rad Bw, hgrad Rad Bw, hpinch Bw, hpinchG Bw, hnc Rad Bw,
    hnot]
    with n hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9 hn10 hn11 hn12 hn13 hn14 hn15
  refine hmain (H n) (hend n) (G n) (hG n) (ht n) (hts n) (y n) (q n) (ρ n) (hq n) (hqy n) hn3
    hn4 (T₀ n) hn7 (records n) (hcan n) hn1 (horder n) hn2 _ (fun _ hw => hw) hn8 hn9 hn10 hn11
    hn12 hn13 hn14 hn5 ?_
  rintro ⟨j, hT, hl, Btr, b, x, h1, h2, h3⟩
  refine hn15 ⟨j, hT, hl, Btr, b, x, h1, by linarith, h3.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (hθ n)
    (inv_nonneg.mpr ((records n j hT).static b).neck.scale_pos.le)

/-- **anchor 核，任意 `θ₀`、`hnot` eventually（`_P6SB`）**：G3 `hanchor0_lateW_local_star_theta_P6SB` 逐字，
`hnot : ∀ n` → `∀ᶠ n`，内层换 `…_window_local_star_ev_P6SB`。 -/
theorem RetainedCoreHistory.hanchor0_lateW_local_star_theta_ev_P6SB
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {D θcap s t ρ T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, θ₀ ≤ θcap n)
    (hpinch : ∀ n, (∀ j : Fin (H n).eventCount, Perelman.PhiAlmostNonnegative
        ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩ Ici (T₀ n)) phi)
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hnot : ∀ᶠ n in atTop, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / ((G n).flow.scalar (t n) (y n)))
    (hRt : Tendsto (fun n => ((G n).flow.scalar (t n) (y n)) * t n) atTop atTop)
    (hR : Tendsto (fun n => ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (hRpos : ∀ n, 0 < (G n).flow.scalar (t n) (y n))
    {Cq : ℝ} (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hqC : ∀ n, q n ≤ Cq * ((G n).flow.scalar (t n) (y n)))
    (hslabsLocStar : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ Btr : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      (t n - v) * max (q n) ((G n).flow.scalar (t n) z) ≤
        1 / (2 * max (Ctime : ℝ) 1) →
      q n < ((H n).toHistory.event j).incoming.flow.scalar v
        (Btr.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
        (Btr.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hderSel : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n))
        (y n) (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x →
      |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
        Ctime * (G n).flow.scalar v x ^ 2)
    (hW : ∀ Rad : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))), q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hgrad : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x → ∀ w : TangentSpace ThreeModel x,
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
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hradius : Tendsto (fun n => (p n).modelRadius) atTop atTop :=
    tendsto_atTop_mono (fun n => (hpar n).2.1.trans (hpar n).2.2.1) hnat
  have hDt : Tendsto D atTop atTop := tendsto_atTop_mono (fun n => (hpar n).2.1) hnat
  have hacc : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ := by
    intro ζ hζ
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hζ)] with n hn
    exact (hpar n).1.trans hn
  have hord (n : ℕ) : 2 ≤ (p n).modelOrder := le_trans (by omega) (hpar n).2.2.2.1
  intro A hA
  obtain ⟨Q, hQ, hev⟩ :=
    RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_star_ev_P6SB
    (Ctime := Ctime) (Cq := Cq) hεle hκ hphi hθ₀ H hend s G hGi t
    hat hts y q ρ hq hqC hR hRt T₀ hT₀
    records hcan hradius hord hacc hW hslabsLocStar hderSel hgrad
    (fun B => (hT₀ B).mono fun n hn j v hv w => (hpinch n).1 j v ⟨hv.1, hn.trans hv.2⟩ w)
    (fun B => (hT₀ B).mono fun n hn v hv w => (hpinch n).2 v ⟨hv.1, hn.trans hv.2⟩ w) hnc hρ D θcap
    hDt hθcap
    hnot A hA
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  filter_upwards [hev] with n hn z hz
  refine (hn z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact (hRpos n).le

namespace ObservedHistory

/-- **切片 BCBD，任意 `θ₀`、`hnotK` eventually（`_P6SB`）**：G3 `sliceBCBD_kernel_fresh_theta_P6SB` 逐字，
kernel 帧 `hnotK : ∀ n` → `∀ᶠ n`。结论 = G3d 结论逐字。PROVISIONAL[同 G3；`hnotK` 只要 eventually、
年龄 `≤ θ₀/scale`]。 -/
theorem sliceBCBD_kernel_fresh_theta_ev_P6SB
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hnotK : ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤
          θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) {Cg : ℝ} (hCg : 2 ≤ Cg)
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
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)))
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon)
      (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (qX : ℕ → CutoffParameters) (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (recordsX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      GeometricCutoffRecord (Kh n) e (qX n))
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hcanX : ∀ n (e : Fin (Kh n).eventCount) (he : T₀X n ≤ (Kh n).time e.succ) b,
      ((recordsX n e he).static b).hasCanonicalWindow)
    (haccX : ∀ n, (qX n).modelAccuracy ≤ 1 / 2)
    (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (qX n).modelRadius)
    (hprotC : ∀ n (v' : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v')
      (hvs : v' ≤ σ n) (z'' : ((Kh n).stageAt (σ n)).Carrier)
      (A : BackwardPointTrace (Kh n) ((Kh n).activeStage v')
          ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono hvs) z'')
      (e : Fin (Kh n).eventCount) (h1 : (Kh n).activeStage (aSeed n) ≤ e.castSucc)
      (h2 : e.succ ≤ (Kh n).activeStage (Tn n))
      (h3 : (Kh n).activeStage v' ≤ e.castSucc)
      (h4 : e.succ ≤ (Kh n).activeStage (σ n))
      (he : T₀X n ≤ (Kh n).time e.succ),
      (∀ (w : Icc (0 : ℝ) (Kh n).horizon) (hw : v' ≤ w) (hwσ : w ≤ σ n),
        (Kh n).time e.succ ≤ (w : ℝ) →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage w) w)
            ((seedTrace n).point ((Kh n).activeStage w)
              ((Kh n).activeStage_mono (hav.trans hw))
              ((Kh n).activeStage_mono (hwσ.trans (hsT n))))
            (A.point ((Kh n).activeStage w) ((Kh n).activeStage_mono hw)
              ((Kh n).activeStage_mono hwσ)) <
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n))
                ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) → ∀ b,
      (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
          ((recordsX n e he).static b).window ''
            {w : standardCapWindow (qX n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
        A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
          ((recordsX n e he).static b).window ''
            {w : standardCapWindow (qX n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hdσ : ∀ n, riemannianEDistOf ((Kh n).stageMetric
        ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    {nr : ℝ → ℝ} {Aκ κ Tκ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (Kh n))
    (hTκ : ∀ n, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
  subst hKh
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have h1 := hRlt n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono (fun n => (hRlt n).le) hnat
  have hRlimG : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
      atTop atTop := hRlim.congr fun n => hRn n
  have hRt := tendsto_scalar_mul_time_of_window_P6LS hσ hRn hRpos hwin
  obtain ⟨-, -, Dp, -, -, hD, -, -, -, hDn⟩ := exists_params_P6D (fun _ => (0 : ℝ))
  have hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ Dp n ∧
      Dp n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨hacc n, hDn n, by rw [hD n]; exact hrad n, hord n, le_rfl⟩
  have hnot' : ∀ᶠ n in atTop, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < Dp n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤ θ₀ *
          ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale
            )⁻¹ :=
    hnotK.mono fun n hn => by
      rw [hD n]
      exact (K n).not_capWindowPoint_prefix_of_late_P6N (j n).castSucc (recordsK n) (yG n) hn
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun B => (hT₀ B).mono fun n hn => by
      rw [← hRn n, ← hσ n]
      exact hn
  have hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi :=
    fun n => ⟨fun i => hpinchK0 n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i),
      hpinchK0 n (j n)⟩
  have hcan := fun n => (K n).prefixLateRecords_hcan_P6N (j n).castSucc (recordsK n) (hcanK n)
  have hstay := hstayLocStar_of_firstExit_P6SP hC20 (by linarith) hjt htj σ hσ y yG hyG R hRpos
    hR1 hRn Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀ hpin hRa qX T₀X
    hT₀X recordsX hOldX hcanX haccX hDmX hprotC hdσ
  have hslabs := hslabsLoc_cstar_of_hgood_P6SP (by linarith) hjt htj σ hσ y yG R hRpos Tn aSeed
    haT hsT has pT seedTrace L hL hgood hwin hstay
  obtain ⟨hρ, hnc⟩ := hnc_window_of_fresh_P6SB hjt htj σ hσ y yG hyG R hRpos hRlim hRn hκ hr hWK
    Tn aSeed haT hsT has pT seedTrace L hL hTκ htimeS hsmall hvolS hnrS hclock hwinF hgate hdistW
  have hW := hW_of_selection_Cg_P6M3 hjt htj σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT has pT
    seedTrace L hL hgood
  have hgrad := hgrad_of_selection_sameSlab_Cg_P6CD hC20 hjt htj σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistW
  have hder := hderSel_of_selection_sameSlab_Cg_P6JG3 hjt htj σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistW
  have hR0 : ∀ n, 0 < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun n => (hRn n) ▸ hRpos n
  have hCg0 : ∀ n, 0 < Cg * R n := fun n => mul_pos (by linarith) (hRpos n)
  have hqC : ∀ n, Cg * R n ≤
      Cg * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := fun n => by
    rw [hRn n]
  exact RetainedCoreHistory.hanchor0_lateW_local_star_theta_ev_P6SB (θcap := fun _ => θ₀)
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) (ρ := fun _ => r / 200) hεcone hκ hphi hθ₀
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hpar
    (fun _ => le_rfl) hpinch hjt htj hnot' hT₀' hRt hRlimG hR0 (Cq := Cg)
    (fun n => Cg * R n) hCg0 hqC
    hslabs hder hW hgrad hnc hρ

end ObservedHistory

/-- consumer：`∀ n` 形 `hnotK`（G3）⇒ eventually 形（`Filter.Eventually.of_forall`），
故 G3 主定理由本文件推出。 -/
example : type_of% @ObservedHistory.sliceBCBD_kernel_fresh_theta_P6SB.{u} := by
  intro ε C1' C2' Ctime' hεcone hC20 phi hphi θ₀ hθ₀ K j t hjt htj T₀ p recordsK yG hcanK hacc hrad
    hord hpinchK0 hnotK Kh hKh σ hσ y hyG R hRpos hRn hRlt hT₀ Tn aSeed haT hsT has pT seedTrace L
    hL Cg hCg hgood hwin hdistW r hr hsmall hclock a₀ ha₀ hpin hRa qX T₀X hT₀X recordsX hOldX hcanX
    haccX hDmX hprotC hdσ nr Aκ κ Tκ hκ hWK hTκ htimeS hvolS hnrS hwinF hgate
  exact ObservedHistory.sliceBCBD_kernel_fresh_theta_ev_P6SB (hεcone := hεcone) (hC20 := hC20)
    (hphi := hphi) (hθ₀ := hθ₀) (hjt := hjt) (htj := htj) (hcanK := hcanK) (hacc := hacc)
    (hrad := hrad) (hord := hord) (hpinchK0 := hpinchK0)
    (hnotK := Filter.Eventually.of_forall hnotK) (Kh := Kh) (hKh := hKh) (σ := σ) (hσ := hσ)
    (y := y) (hyG := hyG) (R := R) (hRpos := hRpos) (hRn := hRn) (hRlt := hRlt) (hT₀ := hT₀)
    (Tn := Tn) (aSeed := aSeed) (haT := haT) (hsT := hsT) (has := has) (pT := pT)
    (seedTrace := seedTrace) (L := L) (hL := hL) (hCg := hCg) (hgood := hgood) (hwin := hwin)
    (hdistW := hdistW) (hr := hr) (hsmall := hsmall) (hclock := hclock) (a₀ := a₀) (ha₀ := ha₀)
    (hpin := hpin) (hRa := hRa) (qX := qX) (T₀X := T₀X) (hT₀X := hT₀X) (recordsX := recordsX)
    (hOldX := hOldX) (hcanX := hcanX) (haccX := haccX) (hDmX := hDmX) (hprotC := hprotC)
    (hdσ := hdσ) (hκ := hκ) (hWK := hWK) (hTκ := hTκ) (htimeS := htimeS) (hvolS := hvolS)
    (hnrS := hnrS) (hwinF := hwinF) (hgate := hgate)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
