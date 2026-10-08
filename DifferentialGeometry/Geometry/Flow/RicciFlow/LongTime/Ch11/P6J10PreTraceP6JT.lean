import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10PreTraceCeilingCXJT0
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedDepthHIP6LT

/-!
# J10T0：ceiling 的消费对照 + (b) 路线跨 slab 形（O-CH11-J10T0，后缀 `_P6JT`）

R-C11-16 D-2 / D-4 第一步。T1 / T0 本体由 CX-J10T0 交付
（`P6J10{CeilingODE,PreTrace,PreTraceCeiling}CXJT0`），本文件只做不重叠的部分：

* **(b) 路线跨 slab，`hscal` 形（PROVISIONAL）** `ObservedHistory.hscal_of_stopped_ceiling_P6JT`：
  以 `scalar_le_two_mul_stopped_ceiling_CXJT0` 为核，把 `P6LL` 的 `hscal` 前提（球内每点、窗口
  `[σ − T/R, σ]` 内每个起点 `w` 的每条 backward trace 上 `R ≤ 2·Q·R*`）整体产出；跨 slab 的定位是显式
  binder `hstopX`。**repair target**（`hstopX`）：trace 穿过 event 时刻之后仍落在 selected 邻域
  （`d_v(seed(v), B(v)) ≤ d_σ(seed(σ), y) + L/√R`）——first-exit bootstrap（用本 ceiling 的曲率界驱动
  I.8.3(b) 距离畸变，不以目标 traced region 为前提）或跨 RegularCrossing 的距离畸变；owner = DIST /
  CX-J10DIST（`hdistW` 的跨 slab 版）。
* **同 slab，`hscal` 形（PROVISIONAL：binder `hslabW`）**
  `ObservedHistory.hscal_of_sameSlab_ceiling_P6JT`：
  `scalar_le_two_mul_sameSlab_ceiling_CXJT0`（`hdistW` 付定位）+ 窗口不跨 event（`hslabW`：
  `time(activeStage σ) ≤ σ − T/R`，即坏点年龄 `≥ T/R`）⇒ `hscal`。`hslabW` 不成立的 `n`（年轻坏点）
  归上一条（`hstopX`）。
* **G4 消费对照** `RetainedCoreHistory.hsurvive_of_extendAt_lateHI_ceiling_P6JT`：
  `P6TracedDepthHIP6LT.lean:320–331`（`hsurvive_of_extendAt_lateHI_P6LT`）的孪生——那里
  `scalar_le_two_mul_along_backward_traces_of_scalar_le_on_ball` 用 `nlinarith [hqR n]` 付
  `2·qcan ≤ Q·R`（"2·qcap ≤ Q_ball·R_bad"），并用 `hdin`（`hderG` 的 `2·qcan` 阈值导数）付 trace ODE；
  孪生改为吃任意 ceiling producer 形 `hceil`（球上界 `≤ Cball·R` ⇒ `hscal`，常数 `Q_b`、`2·Ctime'·Q_b·T ≤ 1`），
  证明里**不再出现** `2·qcan ≤ Q·R`，也不再为 trace ODE 用 `hdin`。`hqR` / `hderG` / `hslab` 仍作为
  `exists_eventually_isTracedRegion_extendAt_lateHI_P6LL` 自身的前提原样传入（`CrossingTracedHI_P6LL:195`
  的 `R > 0` 与 `:226` 的 B5 前提 `1 ≤ Q·R` 由 `hqR` 付；那是 T2 = J10CORE 的包装改动，不在本车道）。
  `hsurvive_of_extendAt_lateHI_sameSlabCeiling_P6JT`：`hceil` 由同 slab 形实例化（`Cg` 通用，`Cg = 4 / 8`
  取 `Q_b := max (max Cball Cg) 1` 即可）。
无 `qcap < R` 形（`hqR` 只是透传给 P6LL），无 traced region 前提，无 `hderivKC`，max-ceiling（含 qcap）不用。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **(b) 路线跨 slab ceiling 的 `hscal` 形（`_P6JT`，PROVISIONAL，binder `hstopX`）**：
`scalar_le_two_mul_stopped_ceiling_CXJT0` 逐 trace 应用。`hstopX` = 球内每点、窗口内每个起点的每条
backward trace 留在 selected 邻域（**跨 slab**，可穿过 event 时刻）。repair target 见文件头：first-exit
bootstrap 或跨 crossing 距离畸变，owner DIST / CX-J10DIST。 -/
theorem hscal_of_stopped_ceiling_P6JT {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T ρ : ℝ}
    (Kh : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) Kh.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {p : (Kh.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace Kh (Kh.activeStage aSeed) (Kh.activeStage Tn)
      (Kh.activeStage_mono haT) p)
    (y : (Kh.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) Kh.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (Kh.stageAt v).Carrier,
        riemannianEDistOf (Kh.stageMetric (Kh.activeStage v) v)
            (seedTrace.point (Kh.activeStage v) (Kh.activeStage_mono hav)
              (Kh.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (Kh.stageMetric (Kh.activeStage σ) σ)
              (seedTrace.point (Kh.activeStage σ) (Kh.activeStage_mono has)
                (Kh.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (Kh.stageMetric (Kh.activeStage v) v) z →
        Kh.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hQb : max (max Cball Cg) 1 ≤ Qb) (hstep : 2 * Ctime' * Qb * T ≤ 1)
    (uu : Icc (0 : ℝ) Kh.horizon) (huu : (uu : ℝ) = σ - T / R) (huS : aSeed ≤ uu)
    (huL : (σ : ℝ) - L ^ 2 / R ≤ uu)
    (hball : ∀ x ∈ riemannianBallOf (Kh.stageMetric (Kh.activeStage σ) σ) y ρ,
      metricScalarAt (Kh.stageMetric (Kh.activeStage σ) σ) x ≤ Cball * R)
    (hstopX : ∀ x ∈ riemannianBallOf (Kh.stageMetric (Kh.activeStage σ) σ) y ρ,
      ∀ (w : Icc (0 : ℝ) Kh.horizon) (huw : uu ≤ w) (hwσ : w ≤ σ)
        (B : BackwardPointTrace Kh (Kh.activeStage w) (Kh.activeStage σ)
          (Kh.activeStage_mono hwσ) x)
        (v : Icc (0 : ℝ) Kh.horizon) (hwv : w ≤ v) (hvσ : v ≤ σ),
        riemannianEDistOf (Kh.stageMetric (Kh.activeStage v) v)
            (seedTrace.point (Kh.activeStage v)
              (Kh.activeStage_mono ((huS.trans huw).trans hwv))
              (Kh.activeStage_mono (hvσ.trans hsT)))
            (B.point (Kh.activeStage v) (Kh.activeStage_mono hwv) (Kh.activeStage_mono hvσ)) ≤
          riemannianEDistOf (Kh.stageMetric (Kh.activeStage σ) σ)
              (seedTrace.point (Kh.activeStage σ) (Kh.activeStage_mono has)
                (Kh.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R)) :
    ∀ x ∈ riemannianBallOf (Kh.stageMetric (Kh.activeStage σ) σ) y ρ,
      ∀ (w : Icc (0 : ℝ) Kh.horizon) (_ : uu ≤ w) (hwσ : w ≤ σ)
        (B : BackwardPointTrace Kh (Kh.activeStage w) (Kh.activeStage σ)
          (Kh.activeStage_mono hwσ) x)
        (v : Icc (0 : ℝ) Kh.horizon) (hwv : w ≤ v) (hvσ : v ≤ σ),
        metricScalarAt (Kh.stageMetric (Kh.activeStage v) v)
          (B.point (Kh.activeStage v) (Kh.activeStage_mono hwv) (Kh.activeStage_mono hvσ)) ≤
          2 * (Qb * R) := by
  intro x hx w huw hwσ B v hwv hvσ
  have huw' : (uu : ℝ) ≤ w := huw
  have hdepth : (σ : ℝ) - w ≤ T / R := by linarith
  exact scalar_le_two_mul_stopped_ceiling_CXJT0 Kh haT hsT has seedTrace y L hR hgood hQb hstep
    hwσ le_rfl (huS.trans huw) (huL.trans huw') hdepth (hball x hx) B
    (fun v' hwv' hv'σ => hstopX x hx w huw hwσ B v' hwv' hv'σ) v hwv hvσ

/-- **同 slab ceiling 的 `hscal` 形（`_P6JT`，PROVISIONAL，binder `hslabW`）**：
`scalar_le_two_mul_sameSlab_ceiling_CXJT0`（`hdistW` 付定位）+ `hslabW`（深度窗不跨 event：
`time(activeStage σ) ≤ σ − T/R`）⇒ `P6LL` 的 `hscal` 前提（`Q := Q_b`）。`Cg` 通用（`Cg = 4 / 8`）。 -/
theorem hscal_of_sameSlab_ceiling_P6JT {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb : ℝ}
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
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v → (Kh n).activeStage v = (Kh n).activeStage (σ n) →
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
    (hQb : max (max Cball Cg) 1 ≤ Qb)
    (hslabW : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      ((Kh n).time ((Kh n).activeStage (σ n)) : ℝ) ≤ σ n - T / R n) :
    ∀ D T : ℝ, 0 < D → 0 < T → 2 * Ctime' * Qb * T ≤ 1 → ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) x ≤ Cball * R n) →
      ∀ uu : Icc (0 : ℝ) (Kh n).horizon, (uu : ℝ) = σ n - T / R n →
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (Kh n).horizon) (_ : uu ≤ w) (hwσ : w ≤ σ n)
        (B : BackwardPointTrace (Kh n) ((Kh n).activeStage w) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hwσ) x)
        (v : Icc (0 : ℝ) (Kh n).horizon) (hwv : w ≤ v) (hvσ : v ≤ σ n),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (B.point ((Kh n).activeStage v) ((Kh n).activeStage_mono hwv)
            ((Kh n).activeStage_mono hvσ)) ≤ 2 * (Qb * R n) := by
  intro D T hD hT hstep
  filter_upwards [scalar_le_two_mul_sameSlab_ceiling_CXJT0 Kh Tn aSeed σ haT hsT has p seedTrace
    y R L hR hL hgood hwin hdistW hQb D T hD hT hstep, hslabW T hT] with n hn hsl
  intro hball uu huu x hx w huw hwσ B v hwv hvσ
  have huw' : (uu : ℝ) ≤ w := huw
  have hTa : (σ n : ℝ) - T / R n ≤ w := by linarith
  have hact : (Kh n).activeStage w = (Kh n).activeStage (σ n) :=
    le_antisymm ((Kh n).activeStage_mono hwσ)
      ((Kh n).le_activeStage w _ (by linarith))
  exact hn x hx (hball x hx) w hwσ hTa hact B v hwv hvσ

end ObservedHistory

namespace RetainedCoreHistory

/-- **G4 消费对照（`_P6JT`）**：`hsurvive_of_extendAt_lateHI_P6LT`（`P6TracedDepthHIP6LT.lean:245`）
的孪生。原证明 :320–331 用 `scalar_le_two_mul_along_backward_traces_of_scalar_le_on_ball`
（`2·qcan ≤ Q·R` 由 `nlinarith [hqR n]` 付，trace ODE 由 `hdin` = `hderG` 的 `2·qcan` 阈值导数付）产出
`P6LL` 的 `hscal`；这里 `hscal` 改由任意 ceiling producer `hceil`（球上界 `≤ Cball·R` ⇒ 沿 trace
`≤ 2·Q_b·R`）给出，证明不再用 `2·qcan ≤ Q·R`。`hqR` / `hderG` / `hslab` 只透传给 `P6LL` 本身
（其 :195 / :226 的用途属 T2）。 -/
theorem hsurvive_of_extendAt_lateHI_ceiling_P6JT
    {Ctime Ctime' : ℝ≥0} {phi : ℝ → ℝ} {Cball Qb : ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n))
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    {a₀ : ℕ → ℝ} (hHI : ∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((H n).initialMetric 0) x)
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      (pF n).delta ((H n).time i.succ) ≤ δb n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ j : Fin (H n).eventCount, Perelman.PhiAlmostNonnegative
        ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩ Ici (T₀ n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (y n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n)) (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n))
    (hR : ∀ n, 0 < R n) (hQ1 : 1 ≤ Qb)
    (hceil : ∀ A T : ℝ, 0 < A → 0 < T → 2 * Ctime' * Qb * T ≤ 1 → ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) x ≤ Cball * R n) →
      ∀ uu : Icc (0 : ℝ) (Hs n).horizon, (uu : ℝ) = ts n - T / R n →
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (Hs n).horizon) (_ : uu ≤ w) (hwσ : w ≤ ts n)
        (B : BackwardPointTrace (Hs n) ((Hs n).activeStage w) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hwσ) x)
        (v : Icc (0 : ℝ) (Hs n).horizon) (hwv : w ≤ v) (hvσ : v ≤ ts n),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (B.point ((Hs n).activeStage v) ((Hs n).activeStage_mono hwv)
            ((Hs n).activeStage_mono hvσ)) ≤ 2 * (Qb * R n)) :
    ∀ A T : ℝ, 0 < A → 0 < T → 2 * (Ctime' : ℝ) * Qb * T ≤ 1 →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Cball * R n) →
      (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n) := by
  intro A T hA hT hstep
  have hev0 := hceil A T hA hT hstep
  subst hHs
  obtain rfl := eq_of_heq hts'
  obtain ⟨K₀, hK₀, hev⟩ :=
    RetainedCoreHistory.exists_eventually_isTracedRegion_extendAt_lateHI_P6LL hphi recordsF hHI
      hend hGi hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hat hts hderG hqR hnot hT₀
      (A := A) (T := T) (Q := Qb) hA hT hQ1
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hev, hRt.eventually_ge_atTop T, hev0] with n hn hRtn hc hball
  have hcn := hc hball
  have hR0 : 0 < (G n).flow.scalar (t n) (y n) := by
    rw [← hRn n]
    exact hR n
  rw [hRn n] at hcn ⊢
  have hTR : T / (G n).flow.scalar (t n) (y n) ≤ t n := by
    rw [div_le_iff₀ hR0]
    linarith
  let uu : Icc (0 : ℝ) ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon :=
    ⟨t n - T / (G n).flow.scalar (t n) (y n), by linarith,
      (sub_le_self _ (div_pos hT hR0).le).trans
        ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)).2.2⟩
  exact hn (ys n) (hys n) uu rfl (hcn uu rfl)

/-- **G4 consumer（`_P6JT`）**：`hceil` 由同 slab ceiling（`hscal_of_sameSlab_ceiling_P6JT`，`Cg` 通用，
`Cg = 4 / 8` 取 `Q_b := max (max Cball Cg) 1`）实例化 ⇒ :320–331 的 traced-region 结论，不经
`2·qcan ≤ Q·R`。PROVISIONAL：binder `hslabW`（深度窗不跨 event）。 -/
theorem hsurvive_of_extendAt_lateHI_sameSlabCeiling_P6JT
    {Ctime Ctime' : ℝ≥0} {phi : ℝ → ℝ} {eps C1' C2' Cg Cball Qb : ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n))
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    {a₀ : ℕ → ℝ} (hHI : ∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((H n).initialMetric 0) x)
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      (pF n).delta ((H n).time i.succ) ≤ δb n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ j : Fin (H n).eventCount, Perelman.PhiAlmostNonnegative
        ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩ Ici (T₀ n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (y n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n)) (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, ts n ≤ Tn n) (has : ∀ n, aSeed n ≤ ts n)
    (pT : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ ts n),
      (ts n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Hs n).stageAt v).Carrier,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hsT n))) (ys n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) z →
        (Hs n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ ts n - T / R n)
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ ts n),
        (ts n : ℝ) - T / R n ≤ v → (Hs n).activeStage v = (Hs n).activeStage (ts n) →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvs) x,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hsT n))) (ys n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hQb : max (max Cball Cg) 1 ≤ Qb)
    (hslabW : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      ((Hs n).time ((Hs n).activeStage (ts n)) : ℝ) ≤ ts n - T / R n) :
    ∀ A T : ℝ, 0 < A → 0 < T → 2 * (Ctime' : ℝ) * Qb * T ≤ 1 →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Cball * R n) →
      (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n) :=
  hsurvive_of_extendAt_lateHI_ceiling_P6JT hphi recordsF hHI hend hGi hcan hδF hqcan hpar hscale
    hbirthA hθcap hpinch hslab hat hts hderG hqR hnot hT₀ hRt Hs ts ys R hHs hts' hys hRn hR
    ((le_max_right _ _).trans hQb)
    (ObservedHistory.hscal_of_sameSlab_ceiling_P6JT Hs Tn aSeed ts haT hsT has pT seedTrace ys R L
      hR hL hgood hwin hdistW hQb hslabW)

end RetainedCoreHistory

/-- consumer（`_P6JT`）：`Cg = 8`、`Q_b = max (max Cball 8) 1` 时 `hQb` 自动成立（`Cg = 4` 同理）。 -/
example (Cball : ℝ) : max (max Cball 8) 1 ≤ max (max Cball 8) 1 ∧
    max (max Cball 4) 1 ≤ max (max Cball 8) 1 :=
  ⟨le_rfl, max_le_max (max_le_max le_rfl (by norm_num)) le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
