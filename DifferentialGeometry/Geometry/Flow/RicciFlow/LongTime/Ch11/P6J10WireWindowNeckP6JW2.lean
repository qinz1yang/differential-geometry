import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireCeilP6JW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WindowScaleP6HS

/-!
# J10WIRE2 G2：hsurvive 链的 `hscale` 槽接 HSCALE 装配（O-CH11-J10WIRE2，后缀 `_P6JW2`）

J10WIRE G1 `RetainedCoreHistory.hsurvive_noJ10_firstExit_P6JW` 的 PROVISIONAL binder `hscaleX`
（窗口内每个 event `2·max{3/r², 2·Q_b·R_n} < static neck.scale`，**∀ n**）换成 HSCALE 的装配输入：
* `ObservedHistory.hceil_of_firstExit_extendAt_ev_P6JW2`（G2a）：J10WIRE G1″
  `hceil_of_firstExit_extendAt_P6JW` 的副本，`hscale` 只要求 `∀ᶠ n`（结论本来就是 `∀ᶠ n`，
  `filter_upwards` 多吃一项）。HSCALE 只给 ∀ᶠ 形，故需此副本。
* **`RetainedCoreHistory.hsurvive_noJ10_firstExit_windowNeck_P6JW2`**（G2，PROVISIONAL）：结论与其余 binder
  **逐字**同 J10WIRE G1；`hscaleX` ⇐ HSCALE G1c `hscale_eventually_of_windowNeck_P6HS`
  （`H := Hs`、`p := qX`、`a := aSeed`、`r_n := r`、`Q_b := max (max Cball Cg) 1`），输入：
  - `hΛX : ∀ n, (qX n).recenterConstant ≤ Λ`（records 参数族一致有界，owner = records / P6GEO）；
  - `hδWX`：窗口 δ 一致小（`∀ ε > 0, ∀ᶠ n`，窗口内 event 时刻 `(qX n).delta ≤ ε`；producer =
    HRECDELTA `hδlim` + `eventually_windowDelta_le_P6HS` / `_rescale_P6HS`，δ 函数与 n 无关时直接给）；
  - 合同 **`hWX : ∀ᶠ n, WindowNeckScaleBudget_P6HS (Hs n) (qX n) (T₀X n) (aSeed n) (R n)`**（显式，owner =
    selection / P6GEO records；`not_windowBudget_of_TnLine_P6HS` 说明 Tn 行推不出它）；
  - `3/r²` 项（`3/r² ≤ 2·Q_b·R_n`）由 `R_n → ∞`（`hRlim`）内部付，不是 binder。
单位：hsurvive 链在 Ho 单位（`R_n = R(G n, t n, y n) → ∞`，`Hs n = extendAt`，未重标度），故用 HSCALE 的
一般序列形 G1c，不用 K 单位 `hscale_eventually_rescale_P6HS`（后者在 G1 塔层用）。
非循环：不含 J10（`qcan < R`）、`hslabW`、`hstopX`、`hdistW`、`isTracedRegion` 前提。
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

/-- **G2a（`_P6JW2`，PROVISIONAL：CXJD / CXJF2 族；`hscale` 改 ∀ᶠ）**：J10WIRE G1″
`hceil_of_firstExit_extendAt_P6JW` 的副本，唯一改动：`hscale` 只要求最终成立（`filter_upwards` 多吃一项）。 -/
theorem hceil_of_firstExit_extendAt_ev_P6JW2 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb r : ℝ}
    {s t : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    (hC2 : 0 ≤ C2') (hr : 0 < r)
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (Kh : ℕ → ObservedHistory.{u})
    (hKh : Kh = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (t : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt t).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage t) t) (a₀ n + t) x)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) (hL : Tendsto L atTop atTop)
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
    (hQb : max (max Cball Cg) 1 ≤ Qb)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ) (hT₀ : ∀ n, T₀ n ≤ aSeed n)
    (records : ∀ n (e : Fin (Kh n).eventCount), T₀ n ≤ (Kh n).time e.succ →
      GeometricCutoffRecord (Kh n) e (q n))
    (hOld : ∀ n (e : Fin (Kh n).eventCount), T₀ n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hcan : ∀ n (e : Fin (Kh n).eventCount) (he : T₀ n ≤ (Kh n).time e.succ) b,
      ((records n e he).static b).hasCanonicalWindow)
    (hDm : ∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hacc : ∀ n : ℕ, (q n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hm : ∀ n, 2 ≤ (q n).modelOrder)
    (hscale : ∀ᶠ n in atTop, ∀ (e : Fin (Kh n).eventCount) (he : T₀ n ≤ (Kh n).time e.succ) b,
      (aSeed n : ℝ) < (Kh n).time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R n)) < ((records n e he).static b).neck.scale)
    (hfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) :
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
  subst hKh
  obtain ⟨ε₀, hε₀, hCX⟩ := exists_extendAt_ceiling_CXJF2.{u}
  have hQ1 : 1 ≤ Qb := (le_max_right _ _).trans hQb
  obtain ⟨c, hc, hnum⟩ := crossSlab_numerics_P6JW (C2' := C2') hC2 hQ1 hr
  intro D T hD hT hstep
  have hacc0 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ ε₀ :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hε₀)
  filter_upwards [hscale, hacc0, hwin T hT, hRlim.eventually_ge_atTop 1,
    hL.eventually_gt_atTop (2 * (D + 8 * T / c)),
    hL.eventually_ge_atTop (4 * (localPropagationRadius C2' / Real.sqrt (2 * Qb))),
    hL.eventually_ge_atTop (T + 1)] with n hscn hεn hwn hRn hL1 hL2 hL3
  intro hball uu huu x hx w huw hwσ B v hwv hvσ
  have huw' : (uu : ℝ) ≤ w := huw
  obtain ⟨ℓ, K, hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hmarg⟩ :=
    hnum (R := R n) (L := L n) (D := D) (T := T) hRn (by linarith) (by linarith)
  have haS : (aSeed n : ℝ) ≤ w := by linarith
  have hTL : T ≤ L n ^ 2 := by nlinarith [sq_nonneg (L n - 1)]
  have haL : (σ n : ℝ) - L n ^ 2 / R n ≤ w := by
    have h := (div_le_div_iff_of_pos_right (hR n)).2 hTL
    linarith
  have hdepth : (σ n : ℝ) - w ≤ T / R n := by linarith
  have hRa' : 1 ≤ R n * w := (hRa n).trans (mul_le_mul_of_nonneg_left haS (hR n).le)
  exact hCX hC2 (H n) (hend n) (G n) (hGi n) (hat n) (hts n) (haT n) (hsmall n) (hclock n)
    (seedTrace n) (ha₀ n) (hpin n) (hsT n) (has n) (y n) (L n) (hR n) (hgood n) hQb hstep haS hwσ
    haL hdepth hRa'
    (hball x hx) B hℓ hKℓ hℓr hKr hKC hℓρ hρL ((hT₀ n).trans haS) (records n) (hOld n)
    (hcan n) (hDm n) ((hacc n).trans hεn) (hm n)
    (fun e he b hlt => hscn e he b (lt_of_le_of_lt haS hlt)) hx (hfin n) hmarg v hwv hvσ

end ObservedHistory

namespace RetainedCoreHistory

/-- **G2（`_P6JW2`，PROVISIONAL：CXJD / CXJF2 族 + HSCALE 装配输入 `hΛX`、`hδWX` + 合同 `hWX`）**：
J10WIRE G1 `hsurvive_noJ10_firstExit_P6JW` 的 `hscaleX` 槽由 HSCALE
`hscale_eventually_of_windowNeck_P6HS` 付（`3/r²` 项由 `R → ∞` 内部付）；其余 binder 与结论逐字。 -/
theorem hsurvive_noJ10_firstExit_windowNeck_P6JW2
    {Ctime Ctime' : ℝ≥0} {phi : ℝ → ℝ} {eps C1' C2' Cg Cball r : ℝ}
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
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n)) (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n))
    (hC2 : 0 ≤ C2') (hr : 0 < r)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, ts n ≤ Tn n) (has : ∀ n, aSeed n ≤ ts n)
    (pT : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (pT n))
    (a₀X : ℕ → ℝ) (ha₀X : ∀ n, 0 ≤ a₀X n)
    (hpinX : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀X n + τ) x)
    (L : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
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
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (qX : ℕ → CutoffParameters) (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (qX n))
    (hOldX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      ((Hs n).event e).old = ((Hs n).event e).transition.trace.retainedCore)
    (hcanX : ∀ n (e : Fin (Hs n).eventCount) (he : T₀X n ≤ (Hs n).time e.succ) b,
      ((recordsX n e he).static b).hasCanonicalWindow)
    (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (qX n).modelRadius)
    (haccX : ∀ n : ℕ, (qX n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hmX : ∀ n, 2 ≤ (qX n).modelOrder)
    {Λ : ℝ} (hΛX : ∀ n, (qX n).recenterConstant ≤ Λ)
    (hδWX : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ e : Fin (Hs n).eventCount,
      (aSeed n : ℝ) < (Hs n).time e.succ → (qX n).delta ((Hs n).time e.succ) ≤ ε)
    (hWX : ∀ᶠ n in atTop, WindowNeckScaleBudget_P6HS (Hs n) (qX n) (T₀X n) (aSeed n) (R n))
    (hfinX : ∀ n, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
        ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
          ((Hs n).activeStage_mono (hsT n))) (ys n) ≠ ⊤) :
    ∀ A T : ℝ, 0 < A → 0 < T → 2 * (Ctime' : ℝ) * max (max Cball Cg) 1 * T ≤ 1 →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Cball * R n) →
      (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n) := by
  have h3 : ∀ᶠ n in atTop, 3 / r ^ 2 ≤ 2 * (max (max Cball Cg) 1 * R n) := by
    filter_upwards [hRlim.eventually_ge_atTop (3 / r ^ 2 / 2)] with n hn
    have hQ1 : (1 : ℝ) ≤ max (max Cball Cg) 1 := le_max_right _ _
    have hRQ : R n ≤ max (max Cball Cg) 1 * R n := le_mul_of_one_le_left (hR n).le hQ1
    linarith
  have hscE := hscale_eventually_of_windowNeck_P6HS Hs (r := fun _ => r)
    (Qb := max (max Cball Cg) 1) (le_max_right _ _) hΛX recordsX hδWX hWX h3
  exact hsurvive_noJ10_P6JC hphi recordsF hHI hend hGi hcan hδF hqcan hpar hscale hbirthA hθcap
    hpinch
    hslab hat hts hderG hnot hT₀ hRt Hs ts ys R hHs hts' hys hRn hRlim (le_max_right _ _)
    (ObservedHistory.hceil_of_firstExit_extendAt_ev_P6JW2 hC2 hr hend hGi hat hts Hs hHs Tn aSeed ts
      haT hsT has pT hsmall hclock seedTrace a₀X ha₀X hpinX ys R L hR hRlim hL hgood le_rfl hwin
      hRa qX T₀X hT₀X recordsX hOldX hcanX hDmX haccX hmX hscE hfinX)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
