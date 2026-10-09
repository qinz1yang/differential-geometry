import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10DepthExtendCXJP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteNoJ10CeilP6JG

/-!
# J10GEN2A G1a：具名合成 driver（O-CH11-J10GEN2A，后缀 `_P6JA`）

`kRouteHICond_noJ10_full_P6JA` = J10GEN G1b `kRouteHICond_noJ10_firstExit_P6JG` 的 `hextend` 槽
由 CX-J10DEPTH G3 `crossingDepthHI_extend_noJ10_CXJP` 填入（`Cext := Ctime′·max(Cg,1)`）。
无 `hqR`、无 `hceilQ` 槽、无 `hextend` 槽；binder 与 CXJP G4 consumer example 逐字
（= G1b 删 `hextend` / `Cext`），全部按名传参。结论 = KRouteHICond driver 结论逐字
（`∃ σ, StrictMono σ ∧ ∀ T > 0, DepthExtendable Hs ts ys R σ T`）。
PROVISIONAL[E 层 binder：`hdistC`（HDISTC2 / FINCOND；K→E 桥 `hdistC_seq_of_eventPrefix_P6JA`）、
J10WIRE (B) 族（`hsmall` `hclock` `a₀X` `hpinX` `hRa` records-X 族 `hfinX`）、
`hsepX`（HSCALE `WindowNeckScaleBudget_P6HS`）]。
由 build-logs/scratch/O-CH11-J10GEN2A/gen0.py 从 `P6J10DepthConsumerCXJP.lean` 的 example 生成。
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

/-- **G1a（`_P6JA`，PROVISIONAL：E 层 `hdistC` / J10WIRE (B) 族 / `hsepX`）**：
KRouteHICond driver 的无 J10 合成形（G1b + CXJP hextend）。
相对旧 driver `exists_subseq_htraced_extendAt_lateHI_cond_P6CD`：删 `hqR`、`hqcan2`、
`hderivC`（由 hgood + `hdistC` 产）、`hsurvive`（J10CORE 核 + first-exit ceiling）、
`hextend`（CXJP）；加 `hR` / `hRlim` / hgood 族 / (B) 族 / `hsepX`。 -/
theorem kRouteHICond_noJ10_full_P6JA
    {Ctime : ℝ≥0}
    {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t T₀ : ℕ → ℝ}
    {p pF : ℕ → CutoffParameters}
    {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n))
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) (a₀ n) x ∧
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
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n)
    (hts : ∀ n, t n < s n)
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
    (Hs : ℕ → ObservedHistory.{u})
    (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier)
    (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n))
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n))
    {r₀ w : ℝ}
    (hr₀ : 0 < r₀)
    (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ}
    (hκ : 0 < κ)
    (ρnc : ℕ → ℝ)
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
    {ε : ℝ}
    (hε : 0 < ε)
    (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u})
    {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ}
    (hqs : ∀ n, qs n ≤ Cs * R n)
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
    (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    {eps C1' C2' Cg : ℝ}
    {Ctime' : ℝ≥0}
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, ts n ≤ Tn n)
    (has : ∀ n, aSeed n ≤ ts n)
    (pT : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ)
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
    {r : ℝ}
    (hC2 : 0 ≤ C2')
    (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀X : ℕ → ℝ)
    (ha₀X : ∀ n, 0 ≤ a₀X n)
    (hpinX : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀X n + τ) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (qX : ℕ → CutoffParameters)
    (T₀X : ℕ → ℝ)
    (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (qX n))
    (hOldX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      ((Hs n).event e).old = ((Hs n).event e).transition.trace.retainedCore)
    (hcanX : ∀ n (e : Fin (Hs n).eventCount) (he : T₀X n ≤ (Hs n).time e.succ) b,
      ((recordsX n e he).static b).hasCanonicalWindow)
    (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (qX n).modelRadius)
    (haccX : ∀ n : ℕ, (qX n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hmX : ∀ n, 2 ≤ (qX n).modelOrder)
    (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, (aSeed n : ℝ) < (Hs n).time e.succ →
        M * R n < ((recordsX n e he).static b).neck.scale)
    (hfinX : ∀ n, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
        ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
          ((Hs n).activeStage_mono (hsT n))) (ys n) ≠ ⊤) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T  :=
  kRouteHICond_noJ10_firstExit_P6JG (Cext := Ctime' * (max Cg 1).toNNReal) (hphi := hphi)
    (recordsF := recordsF) (hHI := hHI) (hend := hend) (hGi := hGi) (hcan := hcan) (hδF := hδF)
    (hqcan := hqcan) (hpar := hpar) (hscale := hscale) (hbirthA := hbirthA) (hθcap := hθcap)
    (hpinch := hpinch) (hslab := hslab) (hat := hat) (hts := hts) (hderG := hderG) (hnot := hnot)
    (hT₀ := hT₀) (hRt := hRt) (hanchor0 := hanchor0) (Hs := Hs) (ts := ts) (ys := ys) (R := R)
    (hHs := hHs) (hts' := hts') (hys := hys) (hRn := hRn) (hr₀ := hr₀) (hw := hw) (hseed := hseed)
    (hκ := hκ) (ρnc := ρnc) (hradii := hradii) (hkappa := hkappa) (hε := hε) (hεX := hεX)
    (hεN := hεN) (hqs := hqs) (hwitC := hwitC) (hbcadC := hbcadC) (hR := hR) (hRlim := hRlim)
    (Tn := Tn) (aSeed := aSeed) (haT := haT) (hsT := hsT) (has := has) (pT := pT)
    (seedTrace := seedTrace) (L := L) (hL := hL) (hgood := hgood) (hwin := hwin) (hdistC := hdistC)
    (hC2 := hC2) (hr := hr) (hsmall := hsmall) (hclock := hclock) (a₀X := a₀X) (ha₀X := ha₀X)
    (hpinX := hpinX) (hRa := hRa) (qX := qX) (T₀X := T₀X) (hT₀X := hT₀X) (recordsX := recordsX)
    (hOldX := hOldX) (hcanX := hcanX) (hDmX := hDmX) (haccX := haccX) (hmX := hmX) (hsepX := hsepX)
    (hfinX := hfinX)
    (hextend := crossingDepthHI_extend_noJ10_CXJP hphi recordsF hHI hend hGi hcan hδF hqcan hpar
      hscale hbirthA hθcap hpinch hslab hat hts hderG hnot hT₀ hRt Hs ts ys R hHs hts' hys hRn hR
      hRlim Tn aSeed haT hsT has pT seedTrace L hL hgood hwin hC2 hr hsmall hclock a₀X ha₀X hpinX
      hRa qX T₀X hT₀X recordsX hOldX hcanX hDmX haccX hmX hsepX hfinX)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
