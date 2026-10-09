import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalStaySeqP6SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WBAdaptStayP6WA2

/-!
# anchor 处 c⋆ 档局部导数槽的完整链（O-CH11-SLTPROD G3d，后缀 `_P6SP`）

**anchor 处 c⋆ 档局部导数槽的完整链**：`hWBloc` ⇐ `shortSLT_guarded`（WBADAPT，PROVED）+
`hslabsLocStar` ⇐ hgood + `hstayLocStar`（G1 c⋆ producer）+ `hstayLocStar` ⇐ CXJD 结构输入
（G3 / G3b / G3c，PROVED）⇒ anchor 两层孪生 PROVISIONAL[hgood, CXJD 结构输入族]，**无新 binder**。
* `ObservedHistory.hanchor0_eventSlab_star_firstExit_P6SP`：WBADAPT
  `hanchor0_eventSlab_prod_star_P6WA2`（`P6WBAdaptStayP6WA2` G4）逐字，`hstayLocStar` 槽删去、由 G3c
  `hstayLocStar_of_firstExit_P6SP` 付；追加 CXJD 结构输入族（K0 seed `hsmall` / `hclock`、HI `hpin`、
  `hRa`、records 族 `qX` / `T₀X` / `recordsX` / `hOldX` / `hcanX` / `haccX` / `hDmX`（与 kernel
  `records` 区分）、`hprotC`、`hdσ`）；`1 ≤ R` 由 `hRlt` 给。
前提里无 `hWBloc` / `hstayLoc*` / `hslabsLoc` / `hslabSel` / `hslabsSel` / `EventSlabsDerivative` /
anchor 球界。**不声称 J10 已去**：∀ `c` 档、slice birth 比较（J10GEN3 4(ii)）、final 对应件、
hctrl survival 槽、CXJD 结构输入族的 kernel 帧供给均未做。生成器
`build-logs/scratch/O-CH11-SLTPROD/gen/gen3d.py`（WBADAPT G4 源 sha256 `6b858373…`、G3c binder 块
assert 切出）。
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

namespace ObservedHistory

/-- **anchor（kernel 帧，c⋆ 档，`_P6SP`，PROVISIONAL[hgood, CXJD 结构输入族]）**：WBADAPT star anchor
的 `hstayLocStar` 由 G3c 付清。结论 = kernel 内 `hanchor0` 逐字形。 -/
theorem hanchor0_eventSlab_star_firstExit_P6SP
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {D θcap T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi)
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
      t n) atTop atTop)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    {κd : ℝ} (hκd : 0 < κd)
    (hvolK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        (Kh n).isParabolicallyRmControlledBall v
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (ϱ / Real.sqrt (R n)) →
        ENNReal.ofReal (κd * ϱ ^ 3) ≤
          Geometry.Collapse.ballVolume
            (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ)
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
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) :
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
  exact hanchor0_eventSlab_prod_star_P6WA2 hεcone hC20 hphi hjt htj hcan hpar hθcap hpinch hnot
    hT₀ hRt (fun n => (K n).toHistory) rfl σ hσ y hyG R hRpos hRn hRlt hκd hvolK Tn aSeed haT hsT
    has pT seedTrace L hL hCg hgood hwin hdistW
    (hstayLocStar_of_firstExit_P6SP hC20 (by linarith) hjt htj σ hσ y yG hyG R hRpos hR1 hRn Tn
      aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀ hpin hRa qX T₀X hT₀X
      recordsX hOldX hcanX haccX hDmX hprotC hdσ)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
