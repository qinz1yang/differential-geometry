import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorSecondP6AN2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteNoJ10FullP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteBridgeP6JA

/-!
# J10GEN2A G4b：ANCHOR5 `hdepthA` 槽 final 支去 J10（O-CH11-J10GEN2A，后缀 `_P6JA`）

`hdepth_toHistory_finalSlab_P6AN2`（`P6AnchorSecondP6AN2.lean:1474`，
lateHI 形：逐 n `a₀`、`hbirthA`、窗口 pinching）的
无 J10 孪生：删 `hqR`；结论逐字；新 binder = full driver 族（final 截断帧：E 对象 `hHs` / `hts'`、K seed + `hgood` +
`hdistC`、E seed 兼容、J10WIRE (B) 族 + `hsepX` + `hfinX`）；
证明 = AN2 遗传重索引逐字 + `kRouteHICond_noJ10_full_P6JA`
（E 层 hgood / hdistC 由 final 桥、hwin ⇐ `hclock`）+ `depthExtendable_final_P6M`。
由 build-logs/scratch/O-CH11-J10GEN2A/gen_g.py 生成。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **G4b（`_P6JA`，PROVISIONAL：E seed 兼容 / J10WIRE (B) 族 / `hsepX` / `hfinX`）**：
`hdepth_toHistory_finalSlab_P6AN2` 的无 J10 孪生（无 `hqR`），结论逐字 = ANCHOR5 `hdepthA` 槽（final 支）
在 supplies 固定后的形。 -/
theorem hdepth_toHistory_finalSlab_noJ10_P6JA :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (Fin.last (K
        n).eventCount)).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) (a₀
          n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) x)
          →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        (pF n).delta (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
        (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / (G n).flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
          (G n).flow.scalar (t n) z ≤
            Q * (G n).flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      (hR : ∀ n, 0 < R n) → (hRlim : Tendsto R atTop atTop) →
      (Hs : ℕ → ObservedHistory.{u}) →
      (hHs : Hs = fun n => (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
        ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
          le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
        (htl n) (htK n)).toHistory) →
      (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon) →
      (hts' : HEq ts (fun n => ((K n).prefixAt (Fin.last (K n).eventCount)).extendAtTime
        ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
          le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
        (htl n) (htK n))) →
      (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) → (hys : ∀ n, HEq (ys n) (yG n)) →
      {epsG C1G C2G Cg : ℝ} → {CtG : ℝ≥0} →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
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
          (Kh n).HasSpatialCanonicalTimeControl epsG C1G C2G CtG v z) →
      (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvs) x,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (TnE aE : ∀ n, Icc (0 : ℝ) (Hs n).horizon) → (haTE : ∀ n, aE n ≤ TnE n) →
      (hsTE : ∀ n, ts n ≤ TnE n) → (hasE : ∀ n, aE n ≤ ts n) →
      (pTE : ∀ n, ((Hs n).stageAt (TnE n)).Carrier) →
      (seedE : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aE n))
        ((Hs n).activeStage (TnE n)) ((Hs n).activeStage_mono (haTE n)) (pTE n)) →
      (haa : ∀ n, (aSeed n : ℝ) ≤ aE n) →
      (hseedC : ∀ n (v : Icc (0 : ℝ) (Hs n).horizon) (v' : Icc (0 : ℝ) (Kh n).horizon),
        (v : ℝ) = v' →
        ∀ (h1 : (Hs n).activeStage (aE n) ≤ (Hs n).activeStage v)
          (h2 : (Hs n).activeStage v ≤ (Hs n).activeStage (TnE n))
          (h1' : (Kh n).activeStage (aSeed n) ≤ (Kh n).activeStage v')
          (h2' : (Kh n).activeStage v' ≤ (Kh n).activeStage (Tn n)),
          HEq ((seedE n).point ((Hs n).activeStage v) h1 h2)
            ((seedTrace n).point ((Kh n).activeStage v') h1' h2')) →
      {rX : ℝ} →
      (hC2G : 0 ≤ C2G) →
      (hrX : 0 < rX) →
      (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (TnE n) (pTE n) rX) →
      (hclock : ∀ n, (aE n : ℝ) = (TnE n : ℝ) - rX ^ 2) →
      (a₀X : ℕ → ℝ) →
      (ha₀X : ∀ n, 0 ≤ a₀X n) →
      (hpinX : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
        InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀X n + τ) x) →
      (hRa : ∀ n, 1 ≤ R n * aE n) →
      (qX : ℕ → CutoffParameters) →
      (T₀X : ℕ → ℝ) →
      (hT₀X : ∀ n, T₀X n ≤ aE n) →
      (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
        GeometricCutoffRecord (Hs n) e (qX n)) →
      (hOldX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
        ((Hs n).event e).old = ((Hs n).event e).transition.trace.retainedCore) →
      (hcanX : ∀ n (e : Fin (Hs n).eventCount) (he : T₀X n ≤ (Hs n).time e.succ) b,
        ((recordsX n e he).static b).hasCanonicalWindow) →
      (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (qX n).modelRadius) →
      (haccX : ∀ n : ℕ, (qX n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hmX : ∀ n, 2 ≤ (qX n).modelOrder) →
      (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
        (he : T₀X n ≤ (Hs n).time e.succ) b, (aE n : ℝ) < (Hs n).time e.succ →
          M * R n < ((recordsX n e he).static b).neck.scale) →
      (hfinX : ∀ n, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
          ((seedE n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (hasE n))
            ((Hs n).activeStage_mono (hsTE n))) (ys n) ≠ ⊤) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T := by
  intro Ctime phi ε hε hεX hεN hphi K t htl htK G hG D θcap qcan T₀ p pF δb records recordsF yG a₀
    hHI hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hnot hT₀ hRt hanchor0 Kh hKh
    σ y R hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC
    hR hRlim Hs hHs ts hts' ys hys epsG C1G C2G Cg CtG Tn aSeed haT hsT has pT seedTrace L hL hgood
    hdistC TnE aE haTE hsTE hasE pTE seedE haa hseedC
    rX hC2G hrX hsmall hclock a₀X ha₀X hpinX hRa qX
    T₀X hT₀X recordsX hOldX hcanX hDmX haccX hmX hsepX hfinX φ hφ
  subst hKh
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  subst hHs
  obtain rfl := eq_of_heq hts'
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hφn := natCast_le_strictMono_P6AN2 hφ
  have hqcan' : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan (φ n) := fun n => by linarith [hqcan (φ n), hφn n]
  have hpar' : ∀ n : ℕ, (p (φ n)).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D (φ n) ∧
      D (φ n) ≤ (p (φ n)).modelRadius ∧ n + 2 ≤ (p (φ n)).modelOrder ∧
      δb (φ n) ≤ 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpar (φ n)
    have hdiv : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [hφn n])
    exact ⟨h1.trans hdiv, by linarith [hφn n], h3, (Nat.add_le_add_right (hφ.id_le n) 2).trans h4,
      h5.trans hdiv⟩
  have hscale' : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan (φ n) ≤ ((records (φ n) i hi).static b).neck.scale := fun n i hi b => by
    have hq0 : 0 ≤ qcan (φ n) := by
      linarith [hqcan (φ n), (Nat.cast_nonneg (φ n) : (0 : ℝ) ≤ φ n)]
    exact (mul_le_mul_of_nonneg_right (by linarith [hφn n]) hq0).trans (hscale (φ n) i hi b)
  have hθcap' : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap (φ n) := fun n => by
    have hdiv : 1 / ((φ n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [hφn n])
    linarith [hθcap (φ n)]
  have haccX' : ∀ n : ℕ, (qX (φ n)).modelAccuracy ≤ 1 / ((n : ℝ) + 1) := fun n =>
    (haccX (φ n)).trans (one_div_le_one_div_of_le (by positivity) (by linarith [hφn n]))
  -- E 层（final 截断帧，沿 φ）
  let Hs' : ℕ → ObservedHistory.{u} := fun n =>
    (((K (φ n)).prefixAt (Fin.last (K (φ n)).eventCount)).extendAt
      ((K (φ n)).prefixAt_time_last _)
      (((K (φ n)).finalSlab ((htl (φ n)).trans (htK (φ n)))).restrictIncoming le_rfl
        ((htl (φ n)).trans (htK (φ n))) le_rfl)
      ((K (φ n)).final_initial ((htl (φ n)).trans (htK (φ n)))) (htl (φ n))
      (htK (φ n))).toHistory
  let ts' : ∀ n, Icc (0 : ℝ) (Hs' n).horizon := fun n =>
    ((K (φ n)).prefixAt (Fin.last (K (φ n)).eventCount)).extendAtTime
      ((K (φ n)).prefixAt_time_last _)
      (((K (φ n)).finalSlab ((htl (φ n)).trans (htK (φ n)))).restrictIncoming le_rfl
        ((htl (φ n)).trans (htK (φ n))) le_rfl)
      ((K (φ n)).final_initial ((htl (φ n)).trans (htK (φ n)))) (htl (φ n)) (htK (φ n))
  have hσ' : ∀ n, (ts' n : ℝ) = σ (φ n) := fun n => (hσ (φ n)).symm
  have hysK : ∀ n, HEq (ys (φ n)) (y (φ n)) := fun n => (hys (φ n)).trans (hyG (φ n)).symm
  have hHs' : ∀ n, Hs' n =
    (((K (φ n)).prefixAt (Fin.last (K (φ n)).eventCount)).extendAt
      ((K (φ n)).prefixAt_time_last _)
      (((K (φ n)).finalSlab ((htl (φ n)).trans (htK (φ n)))).restrictIncoming le_rfl
        ((htl (φ n)).trans (htK (φ n))) le_rfl)
      ((K (φ n)).final_initial ((htl (φ n)).trans (htK (φ n)))) (htl (φ n))
      (htK (φ n))).toHistory := fun _ => rfl
  obtain ⟨ψ, hψ, hall⟩ := kRouteHICond_noJ10_full_P6JA
    (H := fun n => (K (φ n)).prefixAt (Fin.last (K (φ n)).eventCount))
    (G := fun n => ((K (φ n)).finalSlab ((htl (φ n)).trans (htK (φ n)))).restrictIncoming le_rfl
      ((htl (φ n)).trans (htK (φ n))) le_rfl)
    (s := fun n => (K (φ n)).horizon) (y := fun n => yG (φ n)) (a₀ := fun n => a₀ (φ n))
    (records := fun n => records (φ n)) (D := fun n => D (φ n)) (θcap := fun n => θcap (φ n))
    (qcan := fun n => qcan (φ n)) (t := fun n => t (φ n)) (T₀ := fun n => T₀ (φ n))
    (p := fun n => p (φ n)) (pF := fun n => pF (φ n)) (δb := fun n => δb (φ n))
    hphi (fun n => recordsF (φ n)) (fun n => hHI (φ n))
    (fun n => (K (φ n)).prefixAt_time_last _)
    (fun n => (K (φ n)).final_initial ((htl (φ n)).trans (htK (φ n))))
    (fun n => hcan (φ n)) (fun n => hδF (φ n)) hqcan' hpar' hscale' (hφt.eventually hbirthA)
    hθcap' (fun n => hpinch (φ n))
    (fun n => hslab (φ n)) (fun n => htl (φ n)) (fun n => htK (φ n)) (fun n => hderG (φ n))
    (fun n => hnot (φ n)) (fun B => hφt.eventually (hT₀ B)) (hRt.comp hφt)
    (fun A hA => by
      obtain ⟨Q, hQ, hev⟩ := hanchor0 A hA
      exact ⟨Q, hQ, hφt.eventually hev⟩)
    Hs' ts' (fun n => ys (φ n)) (fun n => R (φ n)) rfl HEq.rfl (fun n => hys (φ n))
    (fun n => hRn (φ n)) hr₀ hw
    (hseed_seq_final_P6M hHs' hσ' hysK (hφt.eventually hseed)) hκ (fun n => ρnc (φ n))
    (hradii.comp hφt)
    (hkappa_seq_final_P6M hHs' hσ' hysK
      (fun D T hD hT => hφt.eventually (hkappa D T hD hT))) hε hεX hεN
    (qs := fun n => qs (φ n)) (fun n => hqs (φ n))
    (hwitC_seq_final_P6FC hHs' hσ' hysK (fun φ' hφ' => hwitC (φ ∘ φ') (hφ.comp hφ')))
    (hbcadC_seq_final_P6FC hHs' hσ' hysK (fun A Dd hA hDd => by
      obtain ⟨C, hC⟩ := hbcadC A Dd hA hDd
      exact ⟨C, fun φ' hφ' => hC (φ ∘ φ') (hφ.comp hφ')⟩))
    (fun n => hR (φ n)) (hRlim.comp hφt) (fun n => TnE (φ n)) (fun n => aE (φ n))
    (fun n => haTE (φ n)) (fun n => hsTE (φ n)) (fun n => hasE (φ n)) (fun n => pTE (φ n))
    (fun n => seedE (φ n)) (fun n => L (φ n)) (hL.comp hφt)
    (hgood_seq_final_P6JA (haTK := fun n => haT (φ n)) (hsTK := fun n => hsT (φ n))
      (hasK := fun n => has (φ n)) (haTE := fun n => haTE (φ n)) (hsTE := fun n => hsTE (φ n))
      (hasE := fun n => hasE (φ n)) hHs' hσ' hysK (fun n => haa (φ n)) (fun n => hseedC (φ n))
      (fun n => hgood (φ n)))
    (hwinE_of_clock_P6JA (fun n => hsTE (φ n)) (fun _ => rfl) hrX (fun n => hclock (φ n))
      (hRlim.comp hφt))
    (hdistC_seq_final_P6JA (haTK := fun n => haT (φ n)) (hsTK := fun n => hsT (φ n))
      (hasK := fun n => has (φ n)) (haTE := fun n => haTE (φ n)) (hsTE := fun n => hsTE (φ n))
      (hasE := fun n => hasE (φ n)) hHs' hσ' hysK (fun n => haa (φ n)) (fun n => hseedC (φ n))
      (fun φ' hφ' => hdistC (φ ∘ φ') (hφ.comp hφ')))
    hC2G hrX (fun n => hsmall (φ n)) (fun n => hclock (φ n)) (fun n => a₀X (φ n))
    (fun n => ha₀X (φ n)) (fun n => hpinX (φ n)) (fun n => hRa (φ n)) (fun n => qX (φ n))
    (fun n => T₀X (φ n)) (fun n => hT₀X (φ n)) (fun n => recordsX (φ n)) (fun n => hOldX (φ n))
    (fun n => hcanX (φ n)) (fun n => hDmX (φ n)) haccX' (fun n => hmX (φ n))
    (fun M => hφt.eventually (hsepX M)) (fun n => hfinX (φ n))
  exact ⟨ψ, hψ, fun T hT => depthExtendable_final_P6M hHs' hσ' hysK (hall T hT)⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
