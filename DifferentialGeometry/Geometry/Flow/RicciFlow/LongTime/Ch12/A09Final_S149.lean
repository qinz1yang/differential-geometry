import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateCutFamilyOfCoresV5_S69
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoresBranchPersist_O21
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EmptyThickCores_S37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HfamPackaging_O33
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
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HfamWrap_S135
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HnegDefect_S135
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HEndSfamWired_S143
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HoneS83_S129
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HLTF04StrongV2_S121
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HWBClosed_S121
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HWAAssemble_S132
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HDdPatch_S128
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HLowMain_S114
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HvolW_S100
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HScaleExact_S119
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimMain_O36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HG2cV3_O63
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HSeed_S139
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HFrontSlice_S148
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTraceBall_S138
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BallBound_S141
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HKL70DirectV2_O72
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HFEVol_S127
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HFEGlue_S133
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTSAssembly_S113
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HBirthReduce_S134
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HShiftReduce_S131
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HShiftReduceV4_S137
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ZTAssembly_S113
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickSeedBridge_S38
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LTF03Wiring_S32
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.W2Assembly_CX2

set_option autoImplicit false

/-!
# CH12-S149 (regenerated from A09Final_S124 by scratch/S149gen/regen_s149.py, hKL70 mode O72, hG2c mode U): A09 terminal wiring with ALL existing producers plugged in (as A13Final_S149, plus `hfam := hfam_S135 .. (hone_S129 ..) (hDd_of_patch_S128 ..) hextract HLOW_S114 (hvolw_S100 ..)` following scratch/AxS135G3.lean, `hEndSfam := hEndSfam_wired_S143` (S143: hHPS01 := hps01_O62, hanchor := hanchor_O60 inside), `hSeed := hSeed_S139`, `hTrace := hTrace_S138 .. (hBall_S141 Hp)`); the remaining binders are the producers' own inputs (text cut mechanically).  Previously: S144, S124 (copy of CH12-S79 via the S113 pipeline), A09 terminal wiring (conditional theorem) with the `hZT` binder at `[FROZEN v2] CH12-S113`, `hptK_of_Z0_ZT_ZC_S113`, the `hKL70` binder in the U-form of `[FROZEN] CH12-O56 G1/G2`, the binder `hP6 : P6_S23 Hp` (ch11 supply) added back, and `hextract` wired (S38 + S32 + `W2_of_G2_CX2`) so that it is a premise of the `hfam` binder, not an input of the terminal; everything else verbatim

`A09_of_supplies_S149` has the conclusion of `exists_late_cut_family`
(`LateCutGeometry.lean:148`, binders `F K hK δ hadm hdec slices htimes hnonempty`, conclusion
`Nonempty (LateCutFamily F K slices)`, verbatim), plus a profile `Hp` (as in S32 / S46 / S78) and
explicit hypotheses.  Every proved piece is imported and substituted:

* the cores `B` and the truncations `base` come from `exists_bufferedCores_v2_O21 F (K + 4) ...`
  (O21 G4: both branches of S5), and are fed to `exists_late_cut_family_of_cores_v5_S69`
  (S69 / S59 / S47 / O17 / S31 ...), which needs `BufferedPersistentCores F (K + 4)`;
* `hslice` (the non-negative-scalar branch of O21) is `no_thick_slice_points_of_not_negative_S37`
  (S37 G2 / G1) fed with the normalised zero-order bound `hW1`; the thick-limit negative branch
  is entirely inside `hfam`;
* `hW1` := `exists_normalized_bound_of_physical_W1` applied to `hW1_of_enhanced_K_S46`
  (P1-P4, `macroWholeBall_of_G2_CX2`, `hMicroK` := `microWholeBallK_of_pointwise_S44` applied to
  `hptK_of_Z0_ZT_ZC_S113`), with the same upstream pieces as `A13_of_supplies_S78`:
  `hG2` := `hG2_of_kl82_kappa_O22` (O22) with `hpinchS_O16` (O16) and `hG2c_kappa_of_cert_O28`
  (O28); `hKcap_S73` (S73), `hcore_O31` (O31 G2), `hcap_U_O56` / `capPtU_O56` (O56),
  `hKcan_v2_of_branchesA_O23` and `micro_zero_order_doubled_v2_O23` (O23),
  `micro_low_scalar_point_S33` (S33), `hZC_S64` (S64).

Remaining explicit inputs.  External (ch8): `hHG03`.  ch11 supplies: `hP1`-`hP6`, `hStrong`,
`hcompat`.  ch12 pieces not yet proved: `hfam` (the frozen O21 cover-form family given `hextract`, at order
`K + 4`; produced by `hfam_O33` from the R3 family and the event-time cover R4e), `hKL82`,
`hG2c` (kappa-certificate), `hKL70` (the KL70.2 core consumed by `hcore_O31`), `hZT`.
`hMGL` and `hHG06` are not binders here: they enter only through the producer of `hfam`
(S8 / S1 / S7 of the R3 family), see the delivery block.

S124 changes vs S113: `hKL70` U-form (as in A13); new ch11-supply binder `hP6`; the `hfam` binder (moved after `Hp`, which its new premise mentions) takes `hextract` as a premise, and the proof supplies it (`thickSequenceHasHyperbolicSubsequence_S38`, `hLTF03_of_P6_W2_S32`, `W2_of_G2_CX2`).  No `hscale` binder exists in this terminal.
-/

noncomputable section

open Set Filter TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic
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

/-- **A09 from the supplies (terminal conditional theorem).**  Conclusion = that of
`exists_late_cut_family`; see the file header for the substituted pieces and the remaining
explicit inputs.  `hfam` is the `hfam` binder of `exists_bufferedCores_v2_O21` at order `K + 4`,
verbatim. -/
theorem A09_of_supplies_S149 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
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
    (hRFCa : ∀ (s : RegularSlice F.observation) (pp : CutoffParameters),
      pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
      pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
      StandardCap.transitionEnd + 3 < pp.modelRadius → pp.modelAccuracy ≤ 3 / 4 →
      4 ≤ pp.modelOrder →
      ∀ (i : Fin (sliceHistoryR_O3 F s).eventCount)
        (R : GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        (∀ b, linkedCanonicalWindow_O2 (R.static b)) →
        ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event i).oldOutput),
          ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event i).RetainedBoundaryIndex)
            (c : neckRetainedCollar (R.static b).delta), c.1.2 ≤ 1 ∧
              (R.static b).inclusion ((R.static b).witness.retained c) = y)
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
    (hHG06 : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (Tr : HyperbolicTruncation H)
          (Tr' : HyperbolicTruncation H'), Tr.count ≤ Tr'.count →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ k : ℕ, k ≤ n + 1 → ∀ p ∈ riemannianClosedBallOf H.metric o ξ⁻¹,
            ckErr_O19 H H'.metric 1 f k p < ξ / 3) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
            (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
            ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
              riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η)
    (hthickWF : ∀ wstar : ℝ, 0 < wstar → ∀ H : FiniteVolumeHyperbolicModel.{u},
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (4 * R''), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r)
    (holdF : ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (H : FiniteVolumeHyperbolicModel.{u}), ∃ α : Fin old → ℝ → ℝ, (∀ i t, 0 < α i t) ∧
      (∀ i, Filter.Tendsto (α i) Filter.atTop (nhds 0)) ∧
      (∀ i t (hi : sold i ≤ t), ∃ U : TopologicalSpace.Opens (Hold i).Carrier,
        riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹) ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i t hi) U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => mold i t hi x) ∧
        ∀ k : ℕ, k ≤ ⌈(α i t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹),
          ckErr_S45 (Hold i) (postMetric F.observation t) t⁻¹ (mold i t hi) k p < α i t) ∧
      ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧ ∃ T : ℝ,
        ∀ (i : Fin old) (t : ℝ) (hi : sold i ≤ t), T ≤ t →
        ∀ (q : H.Carrier → (postStage F.observation t).Carrier) (R'' : ℝ), R ≤ R'' →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        (∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ q k'' p < ε) →
        ∀ z ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint ((α i t)⁻¹ / 2),
          mold i t hi z = q H.basepoint →
        ∃ e : H.Carrier ≃ (Hold i).Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
          ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
          ∀ p, localPullInner (Hold i).metric e p = H.metric.inner p)
    (hNewLimF : ∀ wstar : ℝ, 0 < wstar → ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (H : FiniteVolumeHyperbolicModel.{u}), ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
      ∀ (t : ℕ → ℝ), Filter.Tendsto t Filter.atTop Filter.atTop →
      ∀ (q : (m : ℕ) → H.Carrier → (postStage F.observation (t m)).Carrier),
      (∀ m, ∃ R'' : ℝ, R ≤ R'' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
        Set.InjOn (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
        ∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation (t m)) (t m)⁻¹ (q m) k'' p < ε) →
      (∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t m,
        q m H.basepoint ∉ mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
        IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
        (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
          S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
            (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
        ∃ ψ : (m : ℕ) → H'.Carrier → (postStage F.observation (t (σ m))).Carrier,
          (∀ m, ψ m H'.basepoint = q (σ m) H.basepoint) ∧
          (∀ (δ r : ℝ) (m' : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ m, I ≤ m →
            ∃ U : TopologicalSpace.Opens H'.Carrier,
              riemannianBallOf H'.metric H'.basepoint r ⊆ U ∧
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ m) U ∧
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => ψ m x) ∧
              ∀ k : ℕ, k ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
                ckErr_S45 H' (postMetric F.observation (t (σ m))) (t (σ m))⁻¹ (ψ m) k p < δ) ∧
          ∃ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
            riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) ∧
            ∀ k : ℕ, k ≤ n' + 1 → ∀ p ∈ riemannianClosedBallOf H.metric H.basepoint ξ⁻¹,
              ckErr_O19 H H'.metric 1 f k p < ξ / 3)
    (hMGL : ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ H : FiniteVolumeHyperbolicModel.{u}, ∃ x : H.Carrier,
      ∀ y ∈ riemannianBallOf H.metric x a, ENNReal.ofReal c ≤ ballVolume H.metric y 2)
    (hdriftG : ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (Rold : Fin old → ℝ),
      ∀ i' : Fin old, ∀ (hs : 0 < sold i') (K : ℕ) (α : ℝ → ℝ)
        (Ω : TopologicalSpace.Opens (ℝ × (Hold i').Carrier)),
      ((∀ t, sold i' ≤ t → 0 < α t) ∧ AntitoneOn α (Ici (sold i')) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε) ∧
      (∀ t (ht : sold i' ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i' t ht) (sourceSlice_CX5 Ω t)) ∧
      (∀ t (ht : sold i' ≤ t),
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => mold i' t ht x)) ∧
      (∀ t, sold i' ≤ t →
        riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t) ∧
      (∀ t (ht : sold i' ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α t)⁻¹),
          ckErr_S45 (Hold i') (postMetric F.observation t) t⁻¹ (mold i' t ht) k p < α t) ∧
      (∀ t (_ht : sold i' ≤ t), ∀ x ∈ sourceSlice_CX5 Ω t,
        Nonempty (PersistentModelPatch F (Hold i') (sold i') α (sourceSlice_CX5 Ω) (mold i') t x))) →
      ∀ ε : ℝ, 0 < ε → ∃ T0 : ℝ, ∀ (r t : ℝ) (hri : sold i' ≤ r) (hti : sold i' ≤ t),
        T0 ≤ r → ∀ (hrt : r ≤ t), t ≤ 2 * r →
        ∀ q' ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i'),
        ∀ (W : Set ℝ) (w : ∀ s : ℝ, s ∈ W → (postStage F.observation s).Carrier) (hW : Icc r t ⊆ W),
        (∀ s ∈ Icc r t, ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b) (hrW : (r : ℝ) ∈ W),
            HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
              ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
              (w r hrW)) →
        w t (hW ⟨hrt, le_rfl⟩) = mold i' t hti q' →
        riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (hs.trans_le hri)) (postMetric F.observation r))
          (mold i' r hri q') (w r (hW ⟨le_rfl, hrt⟩)) < ENNReal.ofReal ε)
    : Nonempty (LateCutFamily F K slices) := by
  classical
  -- zero-order bound `hW1` (normalised form) exactly as in `A13_of_supplies_S78`
  -- S149 producer wiring (hFront := hFront_S148 Hp hRFCa; hKL70 := O72) (all `have`s are the frozen producer applications; remaining inputs are binders)
  have hscale := (hscale_of_prof_S119.{u}).choose_spec.2 Hp hprof
  have hKL82 := kl82_1_O36.{u}
  have hG2c := hG2c_v3_O63 Hp hdec hP2 hscale (hSeed_S139 Hp) hU
  have hFront := hFront_S148 Hp hRFCa
  have hbirth := hbirth_of_hsurv_S134 Hp Ctime hP2 hsurv
  have hFE := hFE_of_core_S127 Hp (hFEcore_of_trace_S133 Hp hFront (hshift_of_hbirth_v4_S137 Hp hbirth) (hTrace_S138 Hp hP2 hCapWin (hBall_S141 Hp)))
  have hTS := hTS_S113 Hp hFront (hshift_of_hbirth_S131 Hp hbirth)
  have hZT := hZT_of_kl82_S113 Hp hdec Ctime hP2 hKL82 hFE hTS
  have hG2 := hG2_of_kl82_kappa_O22 Hp hdec hKL82 (hpinchS_O16 Hp) (hG2c_kappa_of_cert_O28 Hp hG2c)
  have hKcap := hKcap_S73 Hp hdec hP3 hcompat Ctime hP2
  have hKL70 := hKL70_direct_v2_O72 Hp hKcap Ctime hP2 hP5 heps
  have hcore := hcore_O31 Hp (capPtU_O56 Hp hKcap) hStrong hKL70
  have hcap := hcap_U_O56 Hp hKcap
  have hKcan := hKcan_v2_of_branchesA_O23 Hp (capPtU_O56 Hp hKcap) hcore hcap
  have hZ0 := micro_zero_order_doubled_v2_O23 Hp (micro_low_scalar_point_S33 Hp) hKcan
  have hpt := hptK_of_Z0_ZT_ZC_S113 Hp hP5 Ctime hP2 hZ0
    (fun Ctime' hP2' => by
      obtain ⟨θ, hθ, h⟩ := hZC_S64 Hp hdec hP3 hcompat Ctime' hP2'
      refine ⟨θ, hθ, fun Dcap C0 hD hC0 K' => ?_⟩
      obtain ⟨B, T, hBT⟩ := h Dcap C0 hD hC0 K'
      exact ⟨B, T, fun s hs T₀ h1 h2 pp rec h3 h4 h5 h6 h7 h8 y ρ hρ hZ0' hcap k hk =>
        hBT s hs T₀ h1 h2 pp rec ⟨h3, h4, h5, h6, h7, h8⟩ y ρ hρ hZ0' hcap k hk⟩) hZT
  obtain ⟨b, T, A, hb, hphys⟩ :=
    hW1_of_enhanced_K_S46 F K δ Hp hdec hP1 Ctime hP2 hP3 hP4
      (macroWholeBall_of_G2_CX2 Hp hdec hG2) (fun _ _ _ => microWholeBallK_of_pointwise_S44 Hp hpt K)
  have hW1 := exists_normalized_bound_of_physical_W1 F K b T A hb hphys
  -- `hextract` (LTF05a, negative branch): S38 fed with LTF03 (S32: `hP6`, `hW2`), `hW2` (CX2: the `hG2` chain above) and `hW1`
  have hW2 := W2_of_G2_CX2 Hp hdec hG2
  have hextract : ∀ hneg : EventuallyNegativeScalar_S13 F, ∀ w : ℝ,
      ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w :=
    fun hneg w => thickSequenceHasHyperbolicSubsequence_S38 Hp hdec hneg
      (hLTF03_of_P6_W2_S32 Hp hdec hneg hP6 hW2) hW2 K hW1 w
  -- S149: `hW1` destructured for the hone chain (`hLTF04Ico_strong_S121` / `hWA_S132` take it at order 0), as in scratch/AxS135G3.lean
  have hW1' := hW1
  obtain ⟨b1, T1, C1, h1, h2, h3⟩ := hW1'
  -- S5: cores `B` and truncations `base` (O21), at order `K + 4`
  obtain ⟨B, ⟨base⟩⟩ := exists_bufferedCores_v2_O21 F (K + 4) hHG03
    (fun hn => no_thick_slice_points_of_not_negative_S37 Hp K hW1 hn)
    (hfam_S135 F (K + 4) Hp hdec hHG03
      (fun hneg => hone_S129 F (K + 4)
        (hLTF04Ico_strong_S121 Hp hdec hneg (hLTF03_of_P6_W2_S32 Hp hdec hneg hP6 hW2) hW2 ⟨b1, T1, C1, h1, h2, fun w hw s hs p r hr hrb hnc hbd hv k hk q hq =>
            h3 w hw s hs p r hr hrb hnc hbd hv k (hk.trans (Nat.zero_le K)) q hq⟩
          (hWA_S132 Hp hdec hneg (hLTF03_of_P6_W2_S32 Hp hdec hneg hP6 hW2) hW2 ⟨b1, T1, C1, h1, h2, fun w hw s hs p r hr hrb hnc hbd hv k hk q hq =>
            h3 w hw s hs p r hr hrb hnc hbd hv k (hk.trans (Nat.zero_le K)) q hq⟩ hprof) hWB_S121)
        Hp hscale hdec (hneg_S135 F)
        (hEndSfam_wired_S143 F hHG03 hHG06 hthickWF holdF hNewLimF))
      (fun wstar _hw count model start α Ω map hb Rold H S _hW Φ L hL =>
        hDd_of_patch_S128 F wstar 1 count model start map Rold H S Φ
          (fun i' => ⟨K + 4, α i', Ω i', hb.1 i', fun t ht => hb.2.1 i' t ht, hb.2.2.1 i',
            fun ε hε => hb.2.2.2.1 i' ε hε, fun t ht => hb.2.2.2.2.1 i' t ht,
            fun t ht => hb.2.2.2.2.2.1 i' t ht, fun t ht => hb.2.2.2.2.2.2.1 i' t ht,
            fun t ht k hk p hp => hb.2.2.2.2.2.2.2.1 i' t ht k hk p hp,
            fun t ht x hx => hb.2.2.2.2.2.2.2.2 i' t ht x hx⟩)
          (hdriftG count model start map Rold) L hL)
      hextract (HLOW_S114 F (K + 4))
      (hvolw_S100 F (K + 4) Hp (normalizedVolumeBounded_S13_unconditional_S10 Hp) hMGL))
  exact exists_late_cut_family_of_cores_v5_S69 F K hK δ hadm hdec slices htimes hnonempty B base

end GC.LongTime.Ch12
