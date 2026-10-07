import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.A13WiringK_S46
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroPointwiseAssemblyK_S113
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapWindowZCMain_S64
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapKcapMain_S73
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroZeroOrderDoubled_O23
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroLowPoint_S33
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcapPt_O29
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreAssembly_O31
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84GlueKappa_O22
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Pinch_O16
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862KappaCert_O28
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HtraceU_O56
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HScaleExact_S119
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimMain_O36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HG2cV3_O63
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HSeed_S139
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTraceBall_S138
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BallBound_S141
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HKL70Direct_O65
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HFEVol_S127
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HFEGlue_S133
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTSAssembly_S113
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HBirthReduce_S134
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HShiftReduce_S131
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HShiftReduceV4_S137
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ZTAssembly_S113

set_option autoImplicit false

/-!
# CH12-S144 (regenerated from A13Final_S124 by scratch/S144gen/regen_s144.py, hKL70 mode O65): A13 terminal wiring with ALL existing producers plugged in (hKL82 := kl82_1_O36, hG2c := hG2c_v3_O63 (hscale from hprof), hKL70 := hKL70_direct_O65, hZT := hZT_of_kl82_S113 .. hFE hTS with hFE/hTS from hFE_of_core_S127/hFEcore_of_trace_S133/hTS_S113/hshift reductions from hsurv); the remaining binders are exactly the producers' own inputs (text cut mechanically from the producer sources), see the delivery block.  Previously: S124 (copy of CH12-S78 via the S113 pipeline), A13 terminal wiring (conditional theorem) with the `hZT` binder at `[FROZEN v2] CH12-S113`, `hptK_of_Z0_ZT_ZC_S113`, and the `hKL70` binder in the U-form of `[FROZEN] CH12-O56 G1/G2` (no `∃ Dcap hD`; cap premise `¬ capPtU_O56`; proof side `hcore_O31 Hp (capPtU_O56 ..)`, `hcap_U_O56`); everything else verbatim

`A13_of_supplies_S144` has the conclusion of `late_derivative_tests_of_flow`
(`LateCutGeometry.lean:158`, binders `F K hK δ hadm hdec slices htimes hnonempty L` and conclusion
`L.hasEventualDerivativeBounds`, verbatim), plus a profile `Hp` (as in S32 / S46) and explicit
hypotheses.  Every proved piece is imported and substituted:

* K-indexed A13 wiring `late_derivative_tests_of_flow_of_supplies_K_S46` (S46 / S32 / CX9 / CX2);
* `hMicroK` := `microWholeBallK_of_pointwise_S44` applied to `hptK_of_Z0_ZT_ZC_S113` (S44 / S64);
* `hZ0` := `micro_zero_order_doubled_v2_O23` with `hZ1` := `micro_low_scalar_point_S33` and
  `hKcan` := `hKcan_v2_of_branchesA_O23` (O23) at the union cap predicate `capPtU_O56` (O56),
  `hcap` := `hcap_U_O56` fed with `hKcap_S73` (S73), `hcore` := `hcore_O31` (O31 G2);
* `hZC` := `hZC_S64` (S64);
* `hG2` := `hG2_of_kl82_kappa_O22` (O22) with `hpinchS_O16` (O16) and `hG2c_kappa_of_cert_O28` (O28).

Remaining explicit ch12 inputs: `hKL82`, `hG2c` (κ-cert), `hKL70` (the KL70.2 core consumed by
`hcore_O31`, at the union cap predicate `capPtU_O56`, no `Dcap`), `hZT`.  ch11 supplies:
`hP1`, `hP2`, `hP3`, `hP4`, `hP6`, `hP5`, `hStrong`, `hcompat`.

S124 changes vs S113: only the `hKL70` binder / its three proof lines (see the title); the free cap radius `Dcap` is gone (the cap predicate is the union over cap radii `capPtU_O56`, lead ruling O56-1 (a)).  No `hscale` binder exists in this terminal (`hscale` enters through the `hG2c` producer only).
-/

noncomputable section

open Set Filter TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open GC.LongTime
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch12
universe u

-- S144: the local instance of the producer file HKL70Direct_O65.lean (needed by the text of `hloc`), cut mechanically
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **A13 from the supplies (terminal conditional theorem).**  Conclusion = that of
`late_derivative_tests_of_flow`; see the file header for the substituted pieces and the remaining
explicit inputs. -/
theorem A13_of_supplies_S144 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (L : GC.LongTime.LateCutFamily F K slices)
    (Hp : AnalyticSurgeryProfile F δ)
    (hP1 : P1_O2 Hp) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) (hP3 : P3_O2 Hp) (hP4 : P4_O2 Hp)
    (hP6 : P6_S23 Hp) (hP5 : P5Linked_O13 Hp)
    (hcompat : CompatibleUpgradedCapRecords_S58 Hp)
    (hStrong : ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier,
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∃ (U : TopologicalSpace.Opens s.stage.Carrier) (hxU : x ∈ U)
            (S : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed (s.time - (metricScalarAt s.metric x)⁻¹) s.time
                (sub_le_self _ (inv_nonneg.mpr
                  (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
            IsSolutionOn S ∧ S.base.metric s.time = s.metric.restrictOpen U ∧
            Nonempty (StrongNeck S Hp.epsilon ⟨x, hxU⟩ s.time))
    (hprof : Hp.parameters.modelAccuracy ≤ (hscale_of_prof_S119.{u}).choose ∧
      2 ≤ Hp.parameters.modelOrder ∧ StandardCap.transitionEnd + 1 ≤ Hp.parameters.modelRadius)
    (heps : 13000 * (13000 * Hp.epsilon) ≤
      min (neckModelTolerance ((1 / 4000000 : ℝ) / 26000)) (((1 / 4000000 : ℝ) / 26000) / 64))
    (hloc :
      ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPtU_O56 Hp (hKcap_S73 Hp hdec hP3 hcompat Ctime hP2) A (s n) (y n)) →
      0 ≤ ρ → ρ ≤ A →
      (∀ n, z n ∈ riemannianBallOf (s n).metric (y n)
        (A / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      (∃ κ : ℝ, 0 < κ ∧ ∀ lam : ℝ, 1 < lam → ∀ r : ℝ, ρ < r → ∀ᶠ n in atTop,
          ∃ w : (s n).stage.Carrier,
            w ∈ riemannianBallOf (s n).metric (y n)
              (r / Real.sqrt (metricScalarAt (s n).metric (y n))) ∧
            metricScalarAt (s n).metric w = lam * metricScalarAt (s n).metric (y n) ∧
            ∃ hR : (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ < metricScalarAt (s n).metric w,
            ∃ W : SpatialCanonicalWitness (s n).metric Hp.epsilon Hp.C1 Hp.C2 w,
              W.capTubeHasNeckChart Hp.epsilon ∧
              (W.alternative.requiresVolume → ∀ b : ℝ, 0 < b → b ≤ (Real.sqrt Hp.C2)⁻¹ →
                ENNReal.ofReal (κ * b ^ 3) ≤
                  riemannianVolumeMeasure ThreeModel (s n).stage.Carrier
                    (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos (s n).metric)
                    (riemannianBallOf
                      (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos (s n).metric) w b)) ∧
              ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
                ∃ (U : TopologicalSpace.Opens (s n).stage.Carrier) (hxU : w ∈ U)
                  (S : SolutionOn (I := ThreeModel) (M := U)
                    (RealTimeInterval.closed
                      ((s n).time - (metricScalarAt (s n).metric w)⁻¹) (s n).time
                      (sub_le_self _ (inv_nonneg.mpr
                        (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
                  IsSolutionOn S ∧ S.base.metric (s n).time = (s n).metric.restrictOpen U ∧
                  Nonempty (StrongNeck S Hp.epsilon ⟨w, hxU⟩ (s n).time)) →
      ∃ (κ : ℝ) (σ : ℕ → ℝ), (0 < κ) ∧
      (Tendsto (fun i => σ i *
        Real.sqrt ((sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))) atTop atTop) ∧
      (∀ i (w : ((sliceSlabR_O3 F (s i)).restrictIncoming le_rfl
          (sliceSlabR_O3 F (s i)).lt le_rfl).terminalRegularOpen),
        riemannianEDistOf ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
          ((sliceHistoryR_O3 F (s i)).stage
            (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric
          ⟨y i, mem_slice_terminalRegularOpen_O51 F (s i) (y i)⟩ w <
          ENNReal.ofReal (σ i) →
        ∀ b : ℝ, 0 < b → b ≤ σ i →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel
              ((sliceSlabR_O3 F (s i)).restrictIncoming le_rfl
                (sliceSlabR_O3 F (s i)).lt le_rfl).terminalRegularOpen
              ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
                ((sliceHistoryR_O3 F (s i)).stage
                  (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric
              (riemannianBallOf ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
                ((sliceHistoryR_O3 F (s i)).stage
                  (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric w b)))
    (hU : ∀ σ ℓ wst : ℝ, 0 < σ → σ ≤ 1 → 0 < ℓ → 0 < wst →
      ∃ B c C₀ b₀ T₀ : ℝ, 0 < B ∧ 0 < c ∧ c ≤ ℓ ∧ 1 ≤ C₀ ∧ 0 < b₀ ∧ 0 < T₀ ∧
      ∀ s : RegularSlice F.observation, let N := sliceTowerHistory_CX2 s;
      ∀ (u : Icc (0 : ℝ) N.horizon), T₀ ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
      ∀ (x : (N.stageAt u).Carrier) (r : ℝ), 0 < r → r ≤ b₀ * Real.sqrt u →
      ∀ (a : Icc (0 : ℝ) N.horizon) (hau : a ≤ u)
        (X : BackwardPointTrace N (N.activeStage a) (N.activeStage u) (N.activeStage_mono hau) x),
        (u : ℝ) - r ^ 2 ≤ a →
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((a : ℝ) - c * r ^ 2) a →
          ∀ h, C₀ * (Hp.records m i).nominalRadius h ≤ r) →
        (∃ K' : ℝ, ∀ (v : Icc (0 : ℝ) N.horizon) (hav : a ≤ v) (hvu : v ≤ u),
          ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
              (X.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hvu)) r,
            ∃ A' : BackwardPointTrace N (N.activeStage a) (N.activeStage v)
                (N.activeStage_mono hav) q, A'.isRmBoundedBy (hat := hav) K') →
        (∀ (v : Icc (0 : ℝ) N.horizon) (hav : a ≤ v) (hvu : v ≤ u),
          ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
              (X.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hvu)) r,
            SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r ^ 2)⁻¹)) →
        ∀ y : (N.stageAt a).Carrier,
        y ∈ riemannianBallOf (N.stageMetric (N.activeStage a) a)
            (X.point (N.activeStage a) le_rfl (N.activeStage_mono hau)) (r / 2) →
        (∃ (a' : Icc (0 : ℝ) N.horizon) (ha' : a' ≤ a)
          (Y : BackwardPointTrace N (N.activeStage a') (N.activeStage a) (N.activeStage_mono ha') y),
          (a' : ℝ) = a - ℓ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
            hasSmallParabolicCurvature N w
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
              (σ * r) ∧
            ENNReal.ofReal (wst * (σ * r) ^ 3) ≤
              ballVolume (N.stageMetric (N.activeStage w) w)
                (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
                (σ * r)) →
        ∃ (ae : Icc (0 : ℝ) N.horizon) (haa : ae ≤ a)
          (Z : BackwardPointTrace N (N.activeStage ae) (N.activeStage a) (N.activeStage_mono haa)
            (X.point (N.activeStage a) le_rfl (N.activeStage_mono hau))),
          (ae : ℝ) = a - c * r ^ 2 ∧
          (∃ K'' : ℝ, ∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                ((X.concat Z).point (N.activeStage v) (N.activeStage_mono hav)
                  (N.activeStage_mono hvu)) r,
              ∃ A' : BackwardPointTrace N (N.activeStage ae) (N.activeStage v)
                  (N.activeStage_mono hav) q, A'.isRmBoundedBy (hat := hav) K'') ∧
          (∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                ((X.concat Z).point (N.activeStage v) (N.activeStage_mono hav)
                  (N.activeStage_mono hvu)) r,
              SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r ^ 2)⁻¹)) ∧
          (∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hva : v ≤ a),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                (Z.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hva)) r,
              metricScalarAt (N.stageMetric (N.activeStage v) v) q ≤ B / r ^ 2))
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
    (hsurv : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 →
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
          ∀ θ' : ℝ, 0 < θ' → θ' ≤ θH → ∀ τ : ℝ, 0 < τ → 9 * K * τ ≤ 1 →
          ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) q)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius), ‖x.val‖ < Dcap - 1 + 1 →
            ((records j hj).static b).window x ∈
              riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
                (B.point j.succ le_rfl (Fin.le_last _)) (20 * (θ' * ρ)) →
            metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
              (((records j hj).static b).window x) ≤ 9 * K / (θ' * ρ) ^ 2 →
            s.time - (sliceHistoryR_O3 F s).time j.succ < τ * (θ' * ρ) ^ 2 →
            ∃ yf ∈ riemannianBallOf s.metric p (2 * ρ),
              ∃ A : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
                (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) yf,
                A.point j.succ le_rfl (Fin.le_last _) = ((records j hj).static b).window x)
    : L.hasEventualDerivativeBounds := by
  classical
  -- KL84.2: `hG2` from KL82.1, the slice pinching and the κ-certified KL Lemma 86.2
  -- S144 producer wiring (all `have`s are the frozen producer applications; remaining inputs are binders)
  have hscale := (hscale_of_prof_S119.{u}).choose_spec.2 Hp hprof
  have hKL82 := kl82_1_O36.{u}
  have hG2c := hG2c_v3_O63 Hp hdec hP2 hscale (hSeed_S139 Hp) hU
  have hbirth := hbirth_of_hsurv_S134 Hp Ctime hP2 hsurv
  have hFE := hFE_of_core_S127 Hp (hFEcore_of_trace_S133 Hp hFront (hshift_of_hbirth_v4_S137 Hp hbirth) (hTrace_S138 Hp hP2 hCapWin (hBall_S141 Hp)))
  have hTS := hTS_S113 Hp hFront (hshift_of_hbirth_S131 Hp hbirth)
  have hZT := hZT_of_kl82_S113 Hp hdec Ctime hP2 hKL82 hFE hTS
  have hG2 := hG2_of_kl82_kappa_O22 Hp hdec hKL82 (hpinchS_O16 Hp) (hG2c_kappa_of_cert_O28 Hp hG2c)
  -- K-cap (S73) and the cap predicate (O29)
  have hKcap := hKcap_S73 Hp hdec hP3 hcompat Ctime hP2
  have hKL70 := hKL70_direct_O65 Hp hKcap Ctime hP2 hP5 heps hloc
  have hcore := hcore_O31 Hp (capPtU_O56 Hp hKcap) hStrong hKL70
  have hcap := hcap_U_O56 Hp hKcap
  -- Z0 on the doubled ball (O23), then the K-indexed pointwise glue (S64) and the micro glue (S44)
  have hKcan := hKcan_v2_of_branchesA_O23 Hp (capPtU_O56 Hp hKcap) hcore hcap
  have hZ0 := micro_zero_order_doubled_v2_O23 Hp (micro_low_scalar_point_S33 Hp) hKcan
  -- S64's `hZC_S64` states the records data as one conjunction; `hptK_of_Z0_ZT_ZC_S113` takes it curried
  -- (adapter as in `scratch/AxS64G1.lean`)
  have hpt := hptK_of_Z0_ZT_ZC_S113 Hp hP5 Ctime hP2 hZ0
    (fun Ctime' hP2' => by
      obtain ⟨θ, hθ, h⟩ := hZC_S64 Hp hdec hP3 hcompat Ctime' hP2'
      refine ⟨θ, hθ, fun Dcap C0 hD hC0 K' => ?_⟩
      obtain ⟨B, T, hBT⟩ := h Dcap C0 hD hC0 K'
      exact ⟨B, T, fun s hs T₀ h1 h2 pp rec h3 h4 h5 h6 h7 h8 y ρ hρ hZ0' hcap k hk =>
        hBT s hs T₀ h1 h2 pp rec ⟨h3, h4, h5, h6, h7, h8⟩ y ρ hρ hZ0' hcap k hk⟩) hZT
  exact late_derivative_tests_of_flow_of_supplies_K_S46 F K hK δ hadm hdec slices htimes hnonempty L
    Hp hP1 Ctime hP2 hP3 hP4 hP6 hG2
    (fun _ _ _ => microWholeBallK_of_pointwise_S44 Hp hpt K)

end GC.LongTime.Ch12
