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

set_option autoImplicit false

/-!
# CH12-S124 (copy of CH12-S78 via the S113 pipeline): A13 terminal wiring (conditional theorem) with the `hZT` binder at `[FROZEN v2] CH12-S113`, `hptK_of_Z0_ZT_ZC_S113`, and the `hKL70` binder in the U-form of `[FROZEN] CH12-O56 G1/G2` (no `∃ Dcap hD`; cap premise `¬ capPtU_O56`; proof side `hcore_O31 Hp (capPtU_O56 ..)`, `hcap_U_O56`); everything else verbatim

`A13_of_supplies_S124` has the conclusion of `late_derivative_tests_of_flow`
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
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch12
universe u

/-- **A13 from the supplies (terminal conditional theorem).**  Conclusion = that of
`late_derivative_tests_of_flow`; see the file header for the substituted pieces and the remaining
explicit inputs. -/
theorem A13_of_supplies_S124 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hKL82 : ∀ w : ℝ, 0 < w → ∃ τ₀ K₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ 1 ∧ 0 < K₀ ∧
      ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
        (r0 τ K : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x0) {Phi : ℝ → ℝ},
        Perelman.AdmissiblePinchingFunction Phi →
        (∀ v : Icc (0 : ℝ) H.horizon, v ≤ top → ∀ x,
          curvatureOperatorLowerBoundAt (H.stageMetric (H.activeStage v) v) x
            (metricAlgebraicCurvatureTensorAt (H.stageMetric (H.activeStage v) v) x)
            (Phi (metricScalarAt (H.stageMetric (H.activeStage v) v) x))) →
        0 < r0 → 0 < τ → τ ≤ τ₀ → (a : ℝ) = top - τ * r0 ^ 2 →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
            ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
                (H.activeStage_mono hav) q, A.isRmBoundedBy (hat := hav) K) →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
            SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          (top : ℝ) - 3 / 4 * τ * r0 ^ 2 ≤ v →
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (r0 / 4),
            metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤ K₀ * τ⁻¹ * (r0 ^ 2)⁻¹) ∧
        ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
          ballVolume (H.stageMetric (H.activeStage a) a)
            (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4))
    (hG2c : ∃ ε C₁ K τ₁ τ₂ κ₀ b T : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧
      0 < κ₀ ∧ 0 < b ∧ (τ₁ + τ₂) * b ^ 2 ≤ 1 / 2 ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ b * Real.sqrt s.time →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, C₁ * (Hp.records n i).nominalRadius h ≤ r0) →
        (∀ q ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          SectionalBoundedBelowAt
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r0 ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
                z ρ) →
        ∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
          (X : BackwardPointTrace s.history (s.history.activeStage a)
            (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
          (a : ℝ) = s.time - τ₁ * r0 ^ 2 ∧
          ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u) (hut : u ≤ sliceTop_S8 s),
            s.history.isTracedRegion u
              (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                (s.history.activeStage_mono hut))
              (κ₀ * r0) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹))
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
    (hKL70 : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
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
      False)
    (hZT : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
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
              (C / (a * ρ) ^ 2))
    : L.hasEventualDerivativeBounds := by
  classical
  -- KL84.2: `hG2` from KL82.1, the slice pinching and the κ-certified KL Lemma 86.2
  have hG2 := hG2_of_kl82_kappa_O22 Hp hdec hKL82 (hpinchS_O16 Hp) (hG2c_kappa_of_cert_O28 Hp hG2c)
  -- K-cap (S73) and the cap predicate (O29)
  have hKcap := hKcap_S73 Hp hdec hP3 hcompat Ctime hP2
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
