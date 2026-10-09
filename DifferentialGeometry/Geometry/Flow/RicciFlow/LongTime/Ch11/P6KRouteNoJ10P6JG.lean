import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteHICondP6CD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireCeilP6JW

/-!
# J10GEN G1：KRouteHICond driver 去 J10（O-CH11-J10GEN，后缀 `_P6JG`）

R-C11-16 D-4 第三步前置（= J10CORE HANDOVER 第 1 项）。`P6KRouteHICondP6CD.lean:148–168` 的三处 J10 用法：
* `hR`（`0 < R n`，由 `qcan < R` 推）→ binder `hR : ∀ n, 0 < R n`（与 J10WIRE (B) 族的 `hR` **同名同式**，
  只付一次；`Tendsto R atTop atTop` 推不出逐 `n` 正性）；
* `hRlim`（由 `n + 1 ≤ qcan < R` 推）→ binder `hRlim : Tendsto R atTop atTop`；
* `hqcan2`（`2·qcan ≤ 2·R`，J10 型阈值支配）→ **删**：driver 取 `qcan := Cg·R`、`Cq := Cg`（`le_rfl`），
  `hderivC` 由 hgood good-region 导数供给：`hwitC_hderivC_of_hdistC_Cg_P6CD`.2（hgood / hwin / `L → ∞`
  与 J10WIRE (B) 同一族；`hdistC` 条件形 binder，PROVISIONAL[hdistC ← HDISTC2 / FINCOND]）。
  不经 `hderiv_of_extendAt_P6D2`（slab 阈值 `2·qcan`），也不借 `hderivKC`。
* `hsurvive` 槽：driver 要 `∀ Q ≥ 2`（球上界 `≤ Q·R`，`4·Cst·Q·T ≤ 1`）；J10WIRE
  `hsurvive_noJ10_firstExit_P6JW` 是固定 `Cball`、`hscaleX` 为 `∀ n`，不能逐 `Q` 实例化。故吃 J10CORE 核
  `hsurvive_noJ10_P6JC`（`Cball := Q`、`Q_b := max (max Q Cg) 1`）+ binder 族 `hceilQ`
  （PROVISIONAL[hceilQ ← `hceil_of_firstExit_extendAt_P6JW` 的 `∀ Q, ∀ᶠ n` hscaleX 版，见 G1b]）。
* `hextend` 槽：保留旧形（常数 `Cext`），PROVISIONAL[hextend-noJ10 ← CX-J10EXT]；经
  `DepthExtendable.mono_depth` 降到 `Cst := Cext + Ctime'·max(Cg,1)`（`sideCond_noJ10_P6JG` /
  `depthStep_mono_P6JG`）。旧 `hextend_of_extendAt_lateHI_P6LT`（带 `hqR`）以 `Cext := Ctime` 填此槽
  （兼容 example 在审计 `O-CH11-J10GENG1Audit.lean`，不进本模块）。
由 build-logs/scratch/O-CH11-J10GEN/gen1.py 从 tracked 文本生成（binder 逐字，改动见上）。
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

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- 数值（`_P6JG`，PROVED）：driver 的 `4·Cst·Q·T ≤ 1`（`Cst := Cext + Ctime'·max(Cg,1)`、`Q ≥ 2`）⇒
J10CORE 核的 `2·Ctime'·Q_b·T ≤ 1`（`Q_b := max (max Q Cg) 1`）。 -/
theorem sideCond_noJ10_P6JG {Cext Ctime' : ℝ≥0} {Cg Q T : ℝ} (hQ : 2 ≤ Q) (hT : 0 < T)
    (h : 4 * ((Cext + Ctime' * Real.toNNReal (max Cg 1) : ℝ≥0) : ℝ) * Q * T ≤ 1) :
    2 * (Ctime' : ℝ) * max (max Q Cg) 1 * T ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ max Cg 1 := le_max_right _ _
  have hcoe : ((Cext + Ctime' * Real.toNNReal (max Cg 1) : ℝ≥0) : ℝ) =
      (Cext : ℝ) + Ctime' * max Cg 1 := by
    rw [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ (by linarith)]
  rw [hcoe] at h
  have hQm : 0 ≤ (Q - 2) * (max Cg 1 - 1) := mul_nonneg (by linarith) (by linarith)
  have hmax : max (max Q Cg) 1 ≤ Q * max Cg 1 := by
    refine max_le (max_le ?_ ?_) ?_
    · nlinarith
    · nlinarith [le_max_left Cg 1]
    · nlinarith
  have hC0 : (0 : ℝ) ≤ Ctime' := Ctime'.2
  have hE0 : (0 : ℝ) ≤ Cext := Cext.2
  have h1 : 0 ≤ (Cext : ℝ) * Q * T := mul_nonneg (mul_nonneg hE0 (by linarith)) hT.le
  have h2 : 0 ≤ (Ctime' : ℝ) * max Cg 1 * Q * T :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 (by linarith)) (by linarith)) hT.le
  have hst : 2 * (Ctime' : ℝ) * max (max Q Cg) 1 * T ≤ 2 * Ctime' * (Q * max Cg 1) * T :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax (by positivity)) hT.le
  have hid : 4 * ((Cext : ℝ) + Ctime' * max Cg 1) * Q * T - 2 * Ctime' * (Q * max Cg 1) * T =
      4 * ((Cext : ℝ) * Q * T) + 2 * ((Ctime' : ℝ) * max Cg 1 * Q * T) := by ring
  linarith

/-- 数值（`_P6JG`，PROVED）：`Cst ≥ Cext` ⇒ 深度增量 `1/(32(Cst+1)(M+1)) ≤ 1/(32(Cext+1)(M+1))`。 -/
theorem depthStep_mono_P6JG {Cext Ctime' : ℝ≥0} {Cg M : ℝ} (hM : 0 ≤ M) :
    1 / (32 * (((Cext + Ctime' * Real.toNNReal (max Cg 1) : ℝ≥0) : ℝ) + 1) * (M + 1)) ≤
      1 / (32 * ((Cext : ℝ) + 1) * (M + 1)) := by
  have hle : (Cext : ℝ) ≤ ((Cext + Ctime' * Real.toNNReal (max Cg 1) : ℝ≥0) : ℝ) :=
    NNReal.coe_le_coe.2 le_self_add
  have hM1 : 0 < M + 1 := by linarith
  apply one_div_le_one_div_of_le (mul_pos (by positivity) hM1)
  exact mul_le_mul_of_nonneg_right (by linarith) hM1.le

/-- `hextend` 槽降常数（`_P6JG`，PROVED）：旧形（常数 `Cext`）⇒ driver 用的 `Cst := Cext + Ctime'·max(Cg,1)`
形（`DepthExtendable.mono_depth`）。 -/
theorem hextend_lower_P6JG (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    {Cext Ctime' : ℝ≥0} {Cg : ℝ}
    (hextend : ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Hs (σ i)).stageMetric
          ((Hs (σ i)).activeStage (ts (σ i))) (ts (σ i))) (ys (σ i))
          (A / Real.sqrt (R (σ i))),
      ∀ (w : Icc (0 : ℝ) (Hs (σ i)).horizon),
        (w : ℝ) = ts (σ i) - T' / R (σ i) →
      ∀ (hwt : w ≤ ts (σ i))
        (Bt : BackwardPointTrace (Hs (σ i)) ((Hs (σ i)).activeStage w)
          ((Hs (σ i)).activeStage (ts (σ i)))
          ((Hs (σ i)).activeStage_mono hwt) x),
        metricScalarAt ((Hs (σ i)).stageMetric ((Hs (σ i)).activeStage w) w)
          (Bt.point ((Hs (σ i)).activeStage w) le_rfl
            ((Hs (σ i)).activeStage_mono hwt)) ≤
          M * R (σ i)) →
      DepthExtendable Hs ts ys R σ (Tstar + 1 / (32 * ((Cext : ℝ) + 1) * (M + 1)))) :
    ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T) →
    (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
    ∀ x ∈ riemannianBallOf ((Hs (σ i)).stageMetric
        ((Hs (σ i)).activeStage (ts (σ i))) (ts (σ i))) (ys (σ i))
        (A / Real.sqrt (R (σ i))),
    ∀ (w : Icc (0 : ℝ) (Hs (σ i)).horizon),
      (w : ℝ) = ts (σ i) - T' / R (σ i) →
    ∀ (hwt : w ≤ ts (σ i))
      (Bt : BackwardPointTrace (Hs (σ i)) ((Hs (σ i)).activeStage w)
        ((Hs (σ i)).activeStage (ts (σ i)))
        ((Hs (σ i)).activeStage_mono hwt) x),
      metricScalarAt ((Hs (σ i)).stageMetric ((Hs (σ i)).activeStage w) w)
        (Bt.point ((Hs (σ i)).activeStage w) le_rfl
          ((Hs (σ i)).activeStage_mono hwt)) ≤
        M * R (σ i)) →
      DepthExtendable Hs ts ys R σ (Tstar + 1 /
        (32 * (((Cext + Ctime' * Real.toNNReal (max Cg 1) : ℝ≥0) : ℝ) + 1) * (M + 1))) := by
  intro σ hσ Tstar M hT hM hext hanc
  have hpos : 0 < 32 * (((Cext + Ctime' * Real.toNNReal (max Cg 1) : ℝ≥0) : ℝ) + 1) * (M + 1) :=
    mul_pos (by positivity) (by linarith)
  exact (hextend σ hσ Tstar M hT hM hext hanc).mono_depth hR
    (add_pos hT (one_div_pos.2 hpos)) (add_le_add le_rfl (depthStep_mono_P6JG hM))

/-- **G1（`_P6JG`，PROVISIONAL：`hceilQ` / `hdistC` / `hextend`）**：
`exists_subseq_htraced_extendAt_lateHI_cond_P6CD`（KRouteHICond driver）的无 J10 孪生，结论逐字。
删 `hqR : qcan n < R_n` 与 `hqcan2`；`hR` / `hRlim` 为 binder（`hR` 与 J10WIRE (B) 族同名同式，
只付一次）；driver 阈值 `qcan := Cg·R`、`Cq := Cg`，`hderivC` ⇐ hgood + hwin + `hdistC`
（`hwitC_hderivC_of_hdistC_Cg_P6CD`.2）；`hsurvive` ⇐ J10CORE 核 `hsurvive_noJ10_P6JC` 逐 `Q`
（`Cball := Q`、`Q_b := max (max Q Cg) 1`、`hceil := hceilQ Q`）；`hextend` 旧形（`Cext`）经
`hextend_lower_P6JG`。`hslab` / `hderG` / `hqcan` / `hscale` 只作 B5 的 cap 输入。 -/
theorem kRouteHICond_noJ10_P6JG
    {Ctime : ℝ≥0} {phi : ℝ → ℝ}
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
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (y n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n))
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n)) (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) ε C1s C2s
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε)
    (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₂),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n)
    (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    {eps C1' C2' Cg : ℝ} {Ctime' : ℝ≥0}
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, ts n ≤ Tn n) (has : ∀ n, aSeed n ≤ ts n)
    (pT : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
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
    (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
        (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ ts n),
        (ts n : ℝ) - T / R n ≤ v →
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
    (hceilQ : ∀ Q : ℝ, 2 ≤ Q → ∀ A T : ℝ, 0 < A → 0 < T →
      2 * Ctime' * max (max Q Cg) 1 * T ≤ 1 → ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) x ≤ Q * R n) →
      ∀ uu : Icc (0 : ℝ) (Hs n).horizon, (uu : ℝ) = ts n - T / R n →
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (Hs n).horizon) (_ : uu ≤ w) (hwσ : w ≤ ts n)
        (B : BackwardPointTrace (Hs n) ((Hs n).activeStage w) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hwσ) x)
        (v : Icc (0 : ℝ) (Hs n).horizon) (hwv : w ≤ v) (hvσ : v ≤ ts n),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (B.point ((Hs n).activeStage v) ((Hs n).activeStage_mono hwv)
            ((Hs n).activeStage_mono hvσ)) ≤ 2 * (max (max Q Cg) 1 * R n))
    {Cext : ℝ≥0}
    (hextend : ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Hs (σ i)).stageMetric
          ((Hs (σ i)).activeStage (ts (σ i))) (ts (σ i))) (ys (σ i))
          (A / Real.sqrt (R (σ i))),
      ∀ (w : Icc (0 : ℝ) (Hs (σ i)).horizon),
        (w : ℝ) = ts (σ i) - T' / R (σ i) →
      ∀ (hwt : w ≤ ts (σ i))
        (Bt : BackwardPointTrace (Hs (σ i)) ((Hs (σ i)).activeStage w)
          ((Hs (σ i)).activeStage (ts (σ i)))
          ((Hs (σ i)).activeStage_mono hwt) x),
        metricScalarAt ((Hs (σ i)).stageMetric ((Hs (σ i)).activeStage w) w)
          (Bt.point ((Hs (σ i)).activeStage w) le_rfl
            ((Hs (σ i)).activeStage_mono hwt)) ≤
          M * R (σ i)) →
      DepthExtendable Hs ts ys R σ (Tstar + 1 / (32 * ((Cext : ℝ) + 1) * (M + 1)))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T := by
  refine exists_subseq_forall_depthExtendable_bcadC_P6L2 Hs ts ys R hR hRlim
    (Cst := Cext + Ctime' * Real.toNNReal (max Cg 1)) (fun A T Q hA hT hQ hstep => ?_)
    (hanchor0_of_extendAt_P6D2 hend hGi hat hts hanchor0 Hs ts ys R hHs hts' hys hRn)
    (hextend_lower_P6JG Hs ts ys R hR hextend)
    hr₀ hw hseed hκ ρnc hradii hkappa hphi
    (hpinch_of_extendAt_win_P6LT hend hGi hat hts hpinch hT₀ Hs ts ys R hHs hts' hRn)
    hε hεX hεN hqs hwitC (Ctime := Ctime') (Cq := Cg) (qcan := fun n => Cg * R n) (fun _ => le_rfl)
    (hwitC_hderivC_of_hdistC_Cg_P6CD Hs Tn aSeed ts haT hsT has pT seedTrace ys R L hR hL hgood
      hwin hdistC).2 hbcadC
  exact RetainedCoreHistory.hsurvive_noJ10_P6JC (Cball := Q) hphi recordsF hHI hend hGi hcan hδF
    hqcan hpar hscale hbirthA hθcap hpinch hslab hat hts hderG hnot hT₀ hRt Hs ts ys R hHs hts' hys
    hRn hRlim (le_max_right _ _) (hceilQ Q hQ) A T hA hT (sideCond_noJ10_P6JG hQ hT hstep)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
