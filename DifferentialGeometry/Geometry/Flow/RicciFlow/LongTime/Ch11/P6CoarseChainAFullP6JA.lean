import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CoarseChainACXOU2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRoutePrefixNoJ10P6JG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteNoJ10FullP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteBridgeP6JA

/-!
# J10GEN2A G2c：CoarseChainA（C 暴露）prefix 主形 full 孪生（O-CH11-J10GEN2A，后缀 `_P6JA`）

`false_of_selection_eventSlab_lateHI_prefix_cond_exp_CXOU2`（`P6CoarseChainACXOU2.lean:64`）的无 J10 孪生，
结论逐字（`∀ C, 1 ≤ C → Body_0 C → Body_A C` 形不变）。J10GEN G2 五处模板：`hqR` 槽删（:190）；E 层对象
`Hs` / `ts` / `ys` 升为 binder；K 层 seed / `hgood` / `hdistC` + E seed 兼容 + J10WIRE (B) 族 +
`hsepX` / `hfinX` 加在 `hsel` 前；driver（:330）
换 `kRouteHICond_noJ10_full_P6JA`（E 层 hgood / hdistC 由 event 桥付，hwin ⇐ `hclock`）；
P6D 段（:346/:349）`hR` / `hRlim` 用 binder；私有 helper `scalar_eq_of_eventPrefix_P6CDH` 换
`scalar_eq_of_eventPrefix_P6JGH`（同陈述）。由 build-logs/scratch/O-CH11-J10GEN2A/gen_c.py 生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- **G2c（`_P6JA`，PROVISIONAL：E seed 兼容 / J10WIRE (B) 族 / `hsepX` / `hfinX`）**：
C 暴露 prefix 主形无 J10 full 孪生（无 `hqR`）；结论逐字。 -/
theorem false_of_selection_eventSlab_lateHI_prefix_full_exp_P6JA :
    ∀ epsW : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} →
    ∀ C : ℝ, 1 ≤ C →
    (∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n),
      (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) = R n) →
      Tendsto R atTop atTop →
      (∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) →
      ∀ {r₀ w : ℝ}, 0 < r₀ → 0 < w →
      (∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
            ((H n).stageMetric ((H n).activeStage (t n)) (t n))
            (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      ∀ {κ : ℝ}, 0 < κ → ∀ ρnc : ℕ → ℝ,
      Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (H n).isParabolicallyRmControlledBall v
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'') →
      ∀ {Phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction Phi →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))))) →
      ∀ {C1s C2s Cs Cq : ℝ} {Ctime : ℝ≥0} {qs qcan : ℕ → ℝ},
      (∀ n, qs n ≤ Cs * R n) → (∀ n, qcan n ≤ Cq * R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        (v : ℝ) < t n → (H n).time ((H n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) ε C1s C2s
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        (v : ℝ) < t n → (H n).time ((H n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v')
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ^ 2) →
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    (∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (_ : PointedRiemannianConvergenceMaps X P f)
        (G : ℝ → SmoothRiemannianMetric ThreeModel P.M)
        (hG : IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
          ancientTimeInterval)),
        IsAncientKappaSolution (κ / 250 / 30 ^ 3) (flowOfMetric ancientTimeInterval P G hG) ∧
        PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval P G hG) 1) ∧
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
      (H (ψ i)).HasSpatialCanonicalTimeControl ε C C C.toNNReal (t (ψ i)) (y (ψ i))) →
    ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
              (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
            Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
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
      {Phi : ℝ → ℝ} → (hPhi : Perelman.AdmissiblePinchingFunction Phi) →
      (hpinchK : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))))) →
      {C1s C2s Cs Cq : ℝ} → {Ctr : ℝ≥0} → {qs qd : ℕ → ℝ} →
      (hqs : ∀ n, qs n ≤ Cs * R n) → (hqd : ∀ n, qd n ≤ Cq * R n) →
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
      (hderivKC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qd n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctr * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) →
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
      (hHs : Hs = fun n => ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory) →
      (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon) →
      (hts' : HEq ts (fun n => ((K n).prefixAt (j n).castSucc).extendAtTime
        ((K n).prefixAt_time_last _) ((K n).toHistory.event (j n)).incoming
        ((K n).event_initial (j n)) (hjt n) (htj n))) →
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
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  intro epsW ε hε hsmall hεW hεX hεN C hC hB'
  refine fun hC1 hC2 hCt => ?_
  intro Ctime phi hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ hHI hcan hδF
    hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hnot hT₀ hRt hanchor0 Kh hKh σ y R hσ
    hyG hRn r₀
    w hr₀ hw hseed κ hκ ρnc hradii hkappa Phi hPhi hpinchK C1s C2s Cs Cq Ctr qs qd hqs hqd hwitC
    hderivKC hbcadC hR hRlim Hs hHs ts hts' ys hys epsG C1G C2G Cg CtG Tn aSeed haT hsT has pT
    seedTrace L hL hgood hdistC TnE aE haTE hsTE hasE pTE seedE haa hseedC
    rX hC2G hrX hsmall hclock a₀X ha₀X hpinX hRa qX
    T₀X hT₀X recordsX hOldX hcanX hDmX haccX hmX hsepX hfinX
    hsel
  subst hKh
  -- E 层（`Hs n = (K n).eventPrefix (j n) (t n)`）的基点对象
  subst hHs
  obtain rfl := eq_of_heq hts'
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (j n).castSucc).extendAtTime ((K n).prefixAt_time_last _)
      ((K n).toHistory.event (j n)).incoming ((K n).event_initial (j n)) (hjt n) (htj n)
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun n => (hσ n).symm
  have hysK : ∀ n, HEq (ys n) (y n) := fun n => (hys n).trans (hyG n).symm
  have hHs' : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory :=
    fun _ => rfl
  -- 1. P6D2 G3 在 E 上给 htraced（E 层 trace-local 前提由 G3 桥从 K 层拉回）
  obtain ⟨ψ, hψ, hall⟩ := kRouteHICond_noJ10_full_P6JA
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) hphi recordsF hHI
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hδF hqcan hpar
    hscale hbirthA hθcap hpinch hslab hjt htj hderG hnot hT₀ hRt hanchor0 Hs ts ys R rfl
    HEq.rfl hys
    hRn
    hr₀ hw (hseed_seq_of_eventPrefix_P6M hHs' hσ' hysK hseed) hκ ρnc hradii
    (hkappa_seq_of_eventPrefix_P6M hHs' hσ' hysK hkappa) hε hεX hεN hqs
    (hwitC_seq_of_eventPrefix_P6CD hHs' hσ' hysK hwitC)
    (hbcadC_seq_of_eventPrefix_P6CD hHs' hσ' hysK hbcadC)
    hR hRlim TnE aE haTE hsTE hasE pTE seedE L hL
    (hgood_seq_of_eventPrefix_P6JA (haTK := haT) (hsTK := hsT) (hasK := has) (haTE := haTE)
      (hsTE := hsTE) (hasE := hasE) hHs' hσ' hysK haa hseedC hgood)
    (hwinE_of_clock_P6JA hsTE (fun _ => rfl) hrX hclock hRlim)
    (hdistC_seq_of_eventPrefix_P6JA (haTK := haT) (hsTK := hsT) (hasK := has) (haTE := haTE)
      (hsTE := hsTE) (hasE := hasE) hHs' hσ' hysK haa hseedC hdistC)
    hC2G hrX hsmall hclock a₀X ha₀X hpinX hRa qX
    T₀X hT₀X recordsX hOldX hcanX hDmX haccX hmX hsepX hfinX
  -- 2. htraced 回 K
  have hallK : ∀ T : ℝ, 0 < T → DepthExtendable (fun n => (K n).toHistory) σ y R ψ T :=
    fun T hT => depthExtendable_of_eventPrefix_P6M hHs' hσ' hysK (hall T hT)
  -- 3. P6D G2 直接在 K 上
  have hscalE := scal_of_extendAt_P6D2 (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (y := yG) (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hjt htj
    Hs ts ys R rfl HEq.rfl hys hRn
  have hscal : ∀ n, metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) = R n := fun n =>
    (scalar_eq_of_eventPrefix_P6JGH (K n) (j n) (hjt n) (htj n) (ts n) (σ n) (hσ' n) (ys n) (y n)
      (hysK n)).symm.trans (hscalE n)
  obtain ⟨-, ψ', hψ', hev⟩ := hB' (fun m => (K (ψ m)).toHistory) (fun m => σ (ψ m))
    (fun m => y (ψ m)) (fun m => R (ψ m)) (fun m => hR (ψ m)) (fun m => hscal (ψ m))
    (hRlim.comp hψ.tendsto_atTop) (fun A T hA hT => hallK T hT A hA) hr₀ hw
    (hψ.tendsto_atTop.eventually hseed) hκ (fun m => ρnc (ψ m)) (hradii.comp hψ.tendsto_atTop)
    (fun D T hD hT => hψ.tendsto_atTop.eventually (hkappa D T hD hT)) hPhi
    (fun D T hD hT => hψ.tendsto_atTop.eventually (hpinchK D T hD hT)) (fun m => hqs (ψ m))
    (fun m => hqd (ψ m))
    (fun D T hD hT => by
      obtain ⟨Kc, hKc, hev⟩ := hallK T hT (2 * D) (by positivity)
      exact Filter.eventually_map.mp (hwitC ψ hψ D T Kc hD hT hKc (Filter.eventually_map.mpr hev)))
    (fun D T hD hT => by
      obtain ⟨Kc, hKc, hev⟩ := hallK T hT (2 * D) (by positivity)
      exact Filter.eventually_map.mp
        (hderivKC ψ hψ D T Kc hD hT hKc (Filter.eventually_map.mpr hev)))
  -- 4. AD-good
  exact false_of_not_good_of_eventually_good_P6L hC1 hC2 hCt (fun m => (K (ψ m)).toHistory)
    (fun m => σ (ψ m)) (fun m => y (ψ m)) (fun m => hsel (ψ m)) ⟨ψ', hψ', hev⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
