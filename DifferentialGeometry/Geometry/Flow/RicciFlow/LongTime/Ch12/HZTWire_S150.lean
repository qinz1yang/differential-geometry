import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HSurvCore_S146
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HBirthReduceT_S150
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HShiftV4T_S150
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HShiftOldT_S150
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTSAssemblyT_S150
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HFECoreT_S150
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTraceBall_S150
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BallBound_S150
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HFEVol_S127
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ZTAssembly_S113
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimMain_O36

/-!
# CH12-S150 G2: wiring of `hsurv_core_S146` into `hTS` / `hFE` / `hZT` (`[FROZEN] CH12-S150 G1/G2`)

GENERATED (statement texts) by `build-logs/ch12/scratch/S150gen/gen_g2.py`; the proofs are the wiring terms of the freeze block:
`hbirth_S150 := hbirth_of_hsurvT_S150 … (hsurv_core_S146 …)`, `hshift_S150 := hshift_of_hbirthT_S150 … hbirth_S150`
(`hshift_v4_S150` for the v4 / `hFE` side), `hTS_wired_S150 := hTS_S150 … hshift_S150`,
`hFE_S150 := hFE_of_core_S127 Hp (hFEcore_of_trace_T_S150 … hshift_v4_S150 (hTrace_S150 … (hBall_S150 Hp)))`,
`hZT_S150 := hZT_of_kl82_S113 … kl82_1_O36 hFE_S150 hTS_wired_S150`.
Open inputs (binders): `hFront` (→ `hFront_S148 Hp hRFCa`), `hCapWin` (ch11 cap-window clause), `hP2`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- `hbirth` (60-tube, c₀-clause) from `hsurv_core_S146`: `hbirth_of_hsurvT_S150` applied to the core. -/
theorem hbirth_S150
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime)
    (hFront : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tf εFr : ℝ), 0 < εFr ∧
      ∀ s : RegularSlice F.observation, Tf ≤ s.time → ∀ T₀ : ℝ, Tf ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εFr → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ),
        ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput),
          ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dcap - 1 + 1)
    :
    ∀ {ε₀' c₀ : ℝ}, 0 < ε₀' → 0 < c₀ →
      (∀ {H : ObservedHistory.{u}} {pp : CutoffParameters} {i : Fin H.eventCount},
      pp.modelAccuracy ≤ ε₀' → 4 ≤ pp.modelOrder → ∀ (R : GeometricCutoffRecord H i pp)
      (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ < pp.modelRadius → c₀ * (R.static b).neck.scale ≤
        metricScalarAt (H.event i).outputMetric ((R.static b).window x)) →
      ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 →
      StandardCap.transitionEnd + 3 < Dcap → ∀ K : ℝ, 0 < K →
      ∃ (Cb bH TH θH εH : ℝ), 0 < Cb ∧ 0 < bH ∧ 0 < θH ∧ 0 < εH ∧
      ∀ s : RegularSlice F.observation, TH ≤ s.time → ∀ T₀ : ℝ, TH ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εH → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bH * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          ¬ (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
              ‖x.val‖ < Dcap + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ θ' : ℝ, 0 < θ' → θ' ≤ θH → ∀ τ : ℝ, 0 < τ → 9 * K * τ ≤ 1 → 9 * K * τ ≤ c₀ * θ →
          ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) q)
            (_ : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
              (hav : towerIdx_S137 s j.succ ≤ (sliceTowerHistory_CX2 s).activeStage v)
              (hvt : (sliceTowerHistory_CX2 s).activeStage v ≤
                towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)),
              v.val ≤ s.time →
              ∀ q ∈ riemannianBallOf
                ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
                ((towerTrace_S137 s B).point ((sliceTowerHistory_CX2 s).activeStage v) hav hvt) (60 * (θ' * ρ)),
              Real.sqrt (normSq0S
                ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
                (metricRm04At
                  ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ K / (θ' * ρ) ^ 2)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius), ‖x.val‖ < Dcap - 1 + 1 →
            ((records j hj).static b).window x ∈
              riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
                (B.point j.succ le_rfl (Fin.le_last _)) (20 * (θ' * ρ)) →
            metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
              (((records j hj).static b).window x) ≤ 9 * K / (θ' * ρ) ^ 2 →
            s.time - (sliceHistoryR_O3 F s).time j.succ < τ * (θ' * ρ) ^ 2 →
            ((records j hj).static b).neck.scale ≤ Cb / ρ ^ 2 :=
  hbirth_of_hsurvT_S150 Hp Ctime hP2 (hsurv_core_S146 Hp Ctime hP2 hFront)

/-- old-scale `hshift` (the `hshift` binder of `hTS_S150`). -/
theorem hshift_S150
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime)
    (hFront : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tf εFr : ℝ), 0 < εFr ∧
      ∀ s : RegularSlice F.observation, Tf ≤ s.time → ∀ T₀ : ℝ, Tf ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εFr → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ),
        ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput),
          ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dcap - 1 + 1)
    :
    ∀ {ε₀' c₀ : ℝ}, 0 < ε₀' → 0 < c₀ →
      (∀ {H : ObservedHistory.{u}} {pp : CutoffParameters} {i : Fin H.eventCount},
      pp.modelAccuracy ≤ ε₀' → 4 ≤ pp.modelOrder → ∀ (R : GeometricCutoffRecord H i pp)
      (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ < pp.modelRadius → c₀ * (R.static b).neck.scale ≤
        metricScalarAt (H.event i).outputMetric ((R.static b).window x)) →
      ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 →
      StandardCap.transitionEnd + 3 < Dcap → ∀ K : ℝ, 0 < K →
      ∃ (bH TH θH εH : ℝ), 0 < bH ∧ 0 < θH ∧ 0 < εH ∧
      ∀ s : RegularSlice F.observation, TH ≤ s.time → ∀ T₀ : ℝ, TH ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εH → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bH * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          ¬ (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
              ‖x.val‖ < Dcap + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ θ' : ℝ, 0 < θ' → θ' ≤ θH → ∀ τ : ℝ, 0 < τ → 9 * K * τ ≤ 1 → 9 * K * τ ≤ c₀ * θ →
          ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) q)
            (_ : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
              (hav : towerIdx_S137 s j.succ ≤ (sliceTowerHistory_CX2 s).activeStage v)
              (hvt : (sliceTowerHistory_CX2 s).activeStage v ≤
                towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)),
              v.val ≤ s.time →
              ∀ q ∈ riemannianBallOf
                ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
                ((towerTrace_S137 s B).point ((sliceTowerHistory_CX2 s).activeStage v) hav hvt) (60 * (θ' * ρ)),
              Real.sqrt (normSq0S
                ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
                (metricRm04At
                  ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ K / (θ' * ρ) ^ 2)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius), ‖x.val‖ < Dcap - 1 + 1 →
            ((records j hj).static b).window x ∈
              riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
                (B.point j.succ le_rfl (Fin.le_last _)) (20 * (θ' * ρ)) →
            metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
              (((records j hj).static b).window x) ≤ 9 * K / (θ' * ρ) ^ 2 →
            s.time - (sliceHistoryR_O3 F s).time j.succ < τ * (θ' * ρ) ^ 2 →
            40 * (θ' * ρ) * Real.sqrt ((records j hj).static b).neck.scale ≤ 1 :=
  hshift_of_hbirthT_S150 Hp (hbirth_S150 Hp Ctime hP2 hFront)

/-- v4 `hshift` (the `hshift` binder of `hFEcore_of_trace_T_S150`). -/
theorem hshift_v4_S150
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime)
    (hFront : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tf εFr : ℝ), 0 < εFr ∧
      ∀ s : RegularSlice F.observation, Tf ≤ s.time → ∀ T₀ : ℝ, Tf ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εFr → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ),
        ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput),
          ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dcap - 1 + 1)
    :
    ∀ {ε₀' c₀ : ℝ}, 0 < ε₀' → 0 < c₀ →
      (∀ {H : ObservedHistory.{u}} {pp : CutoffParameters} {i : Fin H.eventCount},
      pp.modelAccuracy ≤ ε₀' → 4 ≤ pp.modelOrder → ∀ (R : GeometricCutoffRecord H i pp)
      (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ < pp.modelRadius → c₀ * (R.static b).neck.scale ≤
        metricScalarAt (H.event i).outputMetric ((R.static b).window x)) →
      ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 →
      StandardCap.transitionEnd + 3 < Dcap → ∀ K : ℝ, 0 < K →
      ∃ (bH TH θH εH : ℝ), 0 < bH ∧ 0 < θH ∧ 0 < εH ∧
      ∀ s : RegularSlice F.observation, TH ≤ s.time → ∀ T₀ : ℝ, TH ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εH → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bH * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          ¬ (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
              ‖x.val‖ < Dcap + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ θ' : ℝ, 0 < θ' → θ' ≤ θH → ∀ τ : ℝ, 0 < τ → 9 * K * τ ≤ 1 → 9 * K * τ ≤ c₀ * θ →
          ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) q)
            (_ : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
              (hav : towerIdx_S137 s j.succ ≤ (sliceTowerHistory_CX2 s).activeStage v)
              (hvt : (sliceTowerHistory_CX2 s).activeStage v ≤
                towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)),
              v.val ≤ s.time →
              ∀ q ∈ riemannianBallOf
                ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
                ((towerTrace_S137 s B).point ((sliceTowerHistory_CX2 s).activeStage v) hav hvt) (60 * (θ' * ρ / 40)),
              Real.sqrt (normSq0S
                ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
                (metricRm04At
                  ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ K / (θ' * ρ / 40) ^ 2)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius), ‖x.val‖ < Dcap - 1 + 1 →
            ((records j hj).static b).window x ∈
              riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
                (B.point j.succ le_rfl (Fin.le_last _)) (20 * (θ' * ρ / 40)) →
            metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
              (((records j hj).static b).window x) ≤ 9 * K / (θ' * ρ / 40) ^ 2 →
            s.time - (sliceHistoryR_O3 F s).time j.succ < τ * (θ' * ρ / 40) ^ 2 →
            40 * (θ' * ρ / 40) * Real.sqrt ((records j hj).static b).neck.scale ≤ 1 :=
  hshift_of_hbirthT_v4_S150 Hp (hbirth_S150 Hp Ctime hP2 hFront)

/-- `hTS` (the `hTS` binder of `hZT_of_kl82_S113`) from the core: `hTS_S150 Hp hFront hshift_S150`. -/
theorem hTSwired_S150
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime)
    (hFront : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tf εFr : ℝ), 0 < εFr ∧
      ∀ s : RegularSlice F.observation, Tf ≤ s.time → ∀ T₀ : ℝ, Tf ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εFr → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ),
        ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput),
          ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dcap - 1 + 1)
    :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
      ∀ a₀ c₁ : ℝ, 0 < a₀ → 0 < c₁ →
      ∃ (bS TS T₀' ρ₀ K₀ θ₂ εT : ℝ), 0 < bS ∧ 0 < TS ∧ 0 < T₀' ∧ 0 < ρ₀ ∧ 0 < K₀ ∧ 0 < θ₂ ∧ 0 < εT ∧
      ∀ s : RegularSlice F.observation, TS ≤ s.time → ∀ T₀ : ℝ, TS ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εT → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bS * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          ¬ (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
              ‖x.val‖ < Dcap + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ θ' : ℝ, 0 < θ' → θ' ≤ θ₂ → ∀ τ : ℝ, 0 < τ → Real.exp (9 * K₀ * τ) < 2 →
          ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
          (∀ v : Icc (0 : ℝ) s.history.horizon, s.time - τ * (θ' * ρ) ^ 2 ≤ v.val →
            ∃ yv : (s.history.stageAt v).Carrier,
              hasSmallParabolicCurvature s.history v yv (a₀ * (θ' * ρ)) ∧
              ENNReal.ofReal (c₁ * (a₀ * (θ' * ρ)) ^ 3) ≤
                ballVolume (s.history.stageMetric (s.history.activeStage v) v) yv (a₀ * (θ' * ρ)) ∧
              ∃ A : BackwardPointTrace s.history (s.history.activeStage v)
                  (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono
                    (show v ≤ sliceTop_S8 s from v.property.2)) q',
                A.point (s.history.activeStage v) le_rfl
                  (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) = yv) →
          (∀ v : Icc (0 : ℝ) s.history.horizon, s.time - τ * (θ' * ρ) ^ 2 ≤ v.val →
            T₀' ≤ v.val ∧ θ' * ρ ≤ ρ₀ * Real.sqrt v) →
          s.history.isTracedRegion (sliceTop_S8 s) q' (2 * (θ' * ρ)) (τ * (θ' * ρ) ^ 2)
            (K₀ / (θ' * ρ) ^ 2) :=
  hTS_S150 Hp hFront (hshift_S150 Hp Ctime hP2 hFront)

/-- `hFE` (the `hFE` binder of `hZT_of_kl82_S113`) from the core. -/
theorem hFE_S150
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime)
    (hFront : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tf εFr : ℝ), 0 < εFr ∧
      ∀ s : RegularSlice F.observation, Tf ≤ s.time → ∀ T₀ : ℝ, Tf ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εFr → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ),
        ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput),
          ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dcap - 1 + 1)
    (hCapWin : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tc εc : ℝ), 0 < εc ∧
      ∀ s : RegularSlice F.observation, Tc ≤ s.time → ∀ T₀ : ℝ, Tc ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εc → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
        (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ∃ x : standardCapWindow pp.modelRadius, ‖x.val‖ < Dcap - 1 + 1 ∧
          ((records j hj).static b).window x =
            ((records j hj).static b).inclusion (((records j hj).static b).witness.cap z))
    :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
          ∃ (bF TF K τ₁ τ₂ w₁ θ₁ εF : ℝ), 0 < bF ∧ 0 < TF ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < w₁ ∧ 0 < θ₁ ∧ 0 < εF ∧
          ∀ s : RegularSlice F.observation, TF ≤ s.time → ∀ T₀ : ℝ, TF ≤ T₀ → T₀ ≤ s.time →
          ∀ (pp : CutoffParameters)
            (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
              T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
              GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
            pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
            pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
            32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
            pp.modelAccuracy ≤ εF → 4 ≤ pp.modelOrder →
            (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
          ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bF * Real.sqrt s.time →
            (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
              (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
              ρ < Λ * (Hp.records n i).nominalRadius h) →
            (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
            (∀ q ∈ riemannianBallOf s.metric p ρ,
              SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
            ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
            (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
            ∀ q ∈ riemannianBallOf s.metric p ρ,
              ¬ (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
                (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
                (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
                (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
                  (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
                (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
                (x : standardCapWindow pp.modelRadius),
                B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
                  ‖x.val‖ < Dcap + 1 ∧
                  s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                    θ * (((records j hj).static b).neck.scale)⁻¹) →
            ∀ θ' : ℝ, 0 < θ' → θ' ≤ θ₁ → ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
              ∃ (a' : Icc (0 : ℝ) s.history.horizon) (hat : a' ≤ sliceTop_S8 s)
                (X : BackwardPointTrace s.history (s.history.activeStage a')
                  (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) q'),
                (a' : ℝ) = s.time - τ₁ * (θ' * ρ) ^ 2 ∧
                (∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a' ≤ u) (hut : u ≤ sliceTop_S8 s),
                  s.history.isTracedRegion u
                    (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                      (s.history.activeStage_mono hut))
                    (θ' * ρ / 40) (τ₂ * (θ' * ρ) ^ 2) (K * ((θ' * ρ) ^ 2)⁻¹)) ∧
                (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ θ' * ρ →
                  ENNReal.ofReal (w₁ * ρ' ^ 3) ≤
                    ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) q' ρ') :=
  hFE_of_core_S127 Hp (hFEcore_of_trace_T_S150 Hp hFront (hshift_v4_S150 Hp Ctime hP2 hFront)
    (hTrace_S150 Hp hP2 hCapWin (hBall_S150 Hp)))

/-- **`hZT` from the survival core**: `hZT_of_kl82_S113` fed with `kl82_1_O36`, `hFE_S150` and `hTSwired_S150`.
Open inputs: `hFront`, `hCapWin`, `hP2`, `hdec`. -/
theorem hZT_S150
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime)
    (hFront : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tf εFr : ℝ), 0 < εFr ∧
      ∀ s : RegularSlice F.observation, Tf ≤ s.time → ∀ T₀ : ℝ, Tf ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εFr → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ),
        ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput),
          ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dcap - 1 + 1)
    (hCapWin : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tc εc : ℝ), 0 < εc ∧
      ∀ s : RegularSlice F.observation, Tc ≤ s.time → ∀ T₀ : ℝ, Tc ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εc → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
        (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ∃ x : standardCapWindow pp.modelRadius, ‖x.val‖ < Dcap - 1 + 1 ∧
          ((records j hj).static b).window x =
            ((records j hj).static b).inclusion (((records j hj).static b).witness.cap z))
    :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
      ∃ (b T a τ C ε₀ : ℝ), 0 < b ∧ 0 < a ∧ 0 < τ ∧ 0 < C ∧ 0 < ε₀ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ T₀ : ℝ, T ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ ε₀ → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ b * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          ¬ (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
              ‖x.val‖ < Dcap + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
            s.history.isTracedRegion (sliceTop_S8 s) q' (2 * (a * ρ)) (τ * (a * ρ) ^ 2)
              (C / (a * ρ) ^ 2) :=
  hZT_of_kl82_S113 Hp hdec Ctime hP2 kl82_1_O36.{u} (hFE_S150 Hp Ctime hP2 hFront hCapWin)
    (hTSwired_S150 Hp Ctime hP2 hFront)

end GC.LongTime.Ch12
