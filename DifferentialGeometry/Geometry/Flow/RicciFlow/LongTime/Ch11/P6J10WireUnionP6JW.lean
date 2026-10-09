import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireCeilP6JW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireStayProdP6JW

/-!
# J10WIRE G3：两条链的 binder 并集（O-CH11-J10WIRE，后缀 `_P6JW`；供 skeleton v4）

* consumer `example`（G1 event slab）：`hceil_of_firstExit_P6JW` 在 `Q_b := max (max Cball Cg) 1` 处给出
  J10CORE G2 `hscal_noJ10_P6JC` 的**结论逐字**，但不要 `hslabW` / `hdistW`（换成 CXJD 族 + `hσlast`）。
* **G3 `example`（并集）**：链 1 `hsurvive_noJ10_firstExit_P6JW`（无 J10、无 hslabW 的 hsurvive）与链 2
  `hderivL_of_hgood_firstExit_P6JW`（FOOT3 hderivL ⇐ hgood + `hstopE`）的 binder 并集 ⇒ 两个结论的合取。
  FOOT3 的 `Ctime`（HSCTC 常数）改名 `CtimeF`，以免与 hsurvive 的 `Ctime`（B5 slab 导数常数）冲突。
**binder 并集（去重后）**：
(A) J10CORE hsurvive 核（B5 / cap 输入，非 J10）：`hphi`、`recordsF`、`hHI`（`a₀` 初始 HI）、`hend`、`hGi`、
  `hcan`、`hδF`、`hqcan`、`hpar`、`hscale`（`(n+1)·qcan ≤ scale`）、`hbirthA`、`hθcap`、`hpinch`、`hslab`、
  `hat`、`hts`、`hderG`、`hnot`、`hT₀`、`hRt`、`Hs/ts/ys/R` + `hHs`/`hts'`/`hys`/`hRn`、`hRlim`。
(B) CXJD / CXJF2 first-exit 族（两条链共用）：`hC2`、seed K0（`Tn`、`aSeed`、`pT`、`r`、`hsmall`、`hclock`、
  `seedTrace`）、Hamilton–Ivey `hpinX`（`a₀X`）、`hgood`（阈值 `Cg·R`）、`L → ∞`、`hwin`、`hRa`
  （`1 ≤ R·aSeed`）、records 族（`qX`、`T₀X ≤ aSeed`、`recordsX`、`hOldX`、`hcanX`、`hDmX`、
  `haccX ≤ 1/(n+1)`、`hmX ≥ 2`）、`hscaleX`（aSeed 之后的 event：`2·max{3/r², 2Q_bR} < scale`）、`hfinX`。
  数值 `ℓ, K` 已由 `crossSlab_numerics_P6JW` 付清（不是 binder）。
(C) 链 2 独有：`hstopE`（`hstayΩ` 前缀 + CXJD 逐 trace 体）。其单 k 体由 G2b
  `hstopE_body_of_firstExit_P6JW` 产出，额外要 **端点球控制** `hball`（`B_t(p′, r/√R)` 上 `R ≤ Cball·R`，
  `t ↑ σ`）、`hRy`（= 前缀的 `hRdef`）、`T ≤ (L/2)²` 与 `L/2` 处数值；塔层打包（把 (B) 提升到
  `∀ T r ind c … i hi, ∀ᶠ k`）未做，见 state HANDOVER。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- consumer（G1 event slab，`_P6JW`）：J10CORE G2 `hscal_noJ10_P6JC` 的结论逐字，无 `hslabW` / `hdistW`。 -/
example {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball r : ℝ}
    (hC2 : 0 ≤ C2') (hr : 0 < r)
    (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
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
    (hσlast : ∀ n, (Kh n).activeStage (σ n) < Fin.last (Kh n).eventCount)
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
    (hscale : ∀ n (e : Fin (Kh n).eventCount) (he : T₀ n ≤ (Kh n).time e.succ) b,
      (aSeed n : ℝ) < (Kh n).time e.succ →
      2 * max (3 / r ^ 2) (2 * (max (max Cball Cg) 1 * R n)) <
        ((records n e he).static b).neck.scale)
    (hfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) :
    ∀ D T : ℝ, 0 < D → 0 < T → 2 * Ctime' * max (max Cball Cg) 1 * T ≤ 1 →
    ∀ᶠ n in atTop,
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
            ((Kh n).activeStage_mono hvσ)) ≤ 2 * (max (max Cball Cg) 1 * R n) :=
  hceil_of_firstExit_P6JW hC2 hr Kh Tn aSeed σ haT hsT has pT hsmall hclock seedTrace a₀ ha₀ hpin
    y R L hR hRlim hL hgood le_rfl hσlast hwin hRa q T₀ hT₀ records hOld hcan hDm hacc hm hscale
    hfin

end ObservedHistory

/-- **G3（`_P6JW`）**：链 1（`hsurvive_noJ10_firstExit_P6JW`）与链 2（`hderivL_of_hgood_firstExit_P6JW`）的
binder 并集 ⇒ 两个结论的合取（逐字）。并集清单见文件头。 -/
example
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
    (hscaleX : ∀ n (e : Fin (Hs n).eventCount) (he : T₀X n ≤ (Hs n).time e.succ) b,
      (aSeed n : ℝ) < (Hs n).time e.succ →
      2 * max (3 / r ^ 2) (2 * (max (max Cball Cg) 1 * R n)) <
        ((recordsX n e he).static b).neck.scale)
    (hfinX : ∀ n, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
        ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
          ((Hs n).activeStage_mono (hsT n))) (ys n) ≠ ⊤)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {CtimeF : ℝ≥0}
    (hstopE :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 CtimeF (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 CtimeF v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t → ∀ (htσ : tt ≤ σ k)
              (a : Icc (0 : ℝ) (Kh k).horizon) (haS' : aSeed k ≤ a) (hat : a ≤ tt),
              t - T / R k ≤ (a : ℝ) →
            ∀ z' : ((Kh k).stageAt tt).Carrier,
              (∀ z : ((Kh k).stage (i k).castSucc).Carrier, HEq z' z →
                z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k))) →
            ∀ (A : BackwardPointTrace (Kh k) ((Kh k).activeStage a) ((Kh k).activeStage tt)
                ((Kh k).activeStage_mono hat) z')
              (v : Icc (0 : ℝ) (Kh k).horizon) (hav : a ≤ v) (hvt : v ≤ tt),
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v)
                    ((Kh k).activeStage_mono (haS'.trans hav))
                    ((Kh k).activeStage_mono ((hvt.trans htσ).trans (hsT k))))
                  (A.point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono hvt)) ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k))) :
    (
    ∀ A T : ℝ, 0 < A → 0 < T → 2 * (Ctime' : ℝ) * max (max Cball Cg) 1 * T ≤ 1 →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Cball * R n) →
      (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n)
    ) ∧ (
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 CtimeF (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 CtimeF v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            (∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
              ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
                (i' : Fin (Kh k).eventCount) (hf : first ≤ i'.castSucc)
                (hij : i'.castSucc < (i k).castSucc),
              ∀ v' ∈ Ioo ((Kh k).time i'.castSucc) ((Kh k).time i'.succ), t - T / R k ≤ v' →
                4 * R k < ((Kh k).event i').incoming.flow.scalar v'
                  (B.point i'.castSucc hf hij.le) →
                |derivWithin (fun w' => ((Kh k).event i').incoming.flow.scalar w'
                    (B.point i'.castSucc hf hij.le)) (Iic v') v'| ≤
                  CtimeF * ((Kh k).event i').incoming.flow.scalar v'
                    (B.point i'.castSucc hf hij.le) ^ 2) ∧
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                4 * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                |derivWithin (fun w' => ((Kh k).event (i k)).incoming.flow.scalar w' z)
                    (Iic v') v'| ≤
                  CtimeF * ((Kh k).event (i k)).incoming.flow.scalar v' z ^ 2
    ) :=
    ⟨RetainedCoreHistory.hsurvive_noJ10_firstExit_P6JW hphi recordsF hHI hend hGi hcan hδF hqcan
      hpar hscale hbirthA hθcap hpinch hslab hat hts hderG hnot hT₀ hRt Hs ts ys R hHs hts' hys
      hRn hC2 hr Tn aSeed haT hsT has pT hsmall hclock seedTrace a₀X ha₀X hpinX L hR hRlim hL
      hgood hwin hRa qX T₀X hT₀X recordsX hOldX hcanX hDmX haccX hmX hscaleX hfinX,
      hderivL_of_hgood_firstExit_P6JW hstopE⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
