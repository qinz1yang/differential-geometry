import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicSeedRecenter
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicSeedRecenterPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicSeedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicSeedVolumePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.AffineEventDistanceScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.AffineEventDistanceScalarPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.AffineHistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.BoundedHistoryEvents
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.BoundedHistoryEventsPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.GeometricObservationFineQuality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.GeometricObservationFineQualityPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.HistoryParabolicBallPrefixTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialBasePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDecay
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDiagonalDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDiagonalDerivativePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDistanceBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDistanceChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDistanceData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialLargerBallAccuracy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialLargerBallAccuracyPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialOwnThresholdDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualityTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQueryReserve
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecentCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveBallPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReservePhysicalInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveQualityData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepRetention
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialSurgeryDecay
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialSurgeryDecayPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialUniformPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialUniformPinchingPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialUniformReserveBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialUniformReserveBallPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawPrefixFineRecords
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawPrefixFineRecordsPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleBirthWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleBirthWeightedMinimumPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventWeightedContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventWeightedContinuationPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventWindowEndpointPair
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.IncomingEventWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.IncomingEventWeightedMinimumPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.NonnegativeEventWindowEndpointPair
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedLocalizedBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedLocalizedBarrierPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedSupportBranches
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedSupportBranchesPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarGeometryPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarSupportJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarSupportJetsPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.WeightedCollarAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.WeightedCollarActionPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.AffineJoinNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.AffineJoinNoncollapsePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.CommonScaffoldExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.CommonScaffoldExtensionPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.CommonScaffoldObservation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.CommonScaffoldObservationPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricObservationExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.NativeObservationCertificates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.NativeObservationDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.NativeObservationDerivativeBoundsPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.NoncollapsedGeometricObservation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.NoncollapsedGeometricObservationPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedDistanceData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedDistanceDataPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedNativeCertificateData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedNativeCertificateDataPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedObservationEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.RegularObservationNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.UniformClosedBirthObservationEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.UniformClosedBirthObservationEstimatesPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowActionRecentNode
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowActionRecentNodePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordCanonicalRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordCanonicalRadiusPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordDelayedRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordDelayedRadiusPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordHistoryRestriction.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordHistoryRestriction.BasicPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordModelRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapNoShortcut
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteOutputDistanceScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteOutputDistanceScalarPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsePrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsePrefix.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsingPresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsingPresentation.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionVolumePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformBirthSpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformBirthSpatialCanonicalWitnessPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformCapWindowBirthSpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformCapWindowBirthSpatialCanonicalWitnessPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformFineCutoffScaffold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformFineCutoffScaffoldPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformScaffoldSurgeryStep

set_option autoImplicit false
noncomputable section

/-!
# S-CH11-CONS2 G1 consumer（`_C11C3`）：patched-at-path / `PortC11P` 文件对 donor 陈述逐字比对

对 root #32 起登记（及已 commit 未登记）的每个 patched-at-path / `PortC11P` 文件的每个 public
theorem / def：把 donor（ch11 HEAD a73e4bdbfd，`build-logs/scratch/ch11src` 同路径）里该声明的
**签名文本逐字**（binders + 类型）搬进 `example : ∀ binders, type := @Full`，放在 port 文件自己的
namespace / open / variable 上下文里；通过 = donor 陈述文本在本树 elaborate 出的类型与 port
常量的类型 defeq（hypothesis 名 α-重命名不影响）。超过 100 列的 donor 行在空格处折行。donor 文本
本身在本树编不过的声明（`x ^ 2` postponed、`𝓝` 误解析、`).` 换行、`▸` 等，正是 port 修补的对象）
与 structure 退回 `type_of% @D := @D`，逐条列在 `build-logs/scratch/S-CH11-CONS2/
portaudit3-report.txt`。VERBATIM 模块与原路径 shim 只做 `type_of%` 可见性 / 可 import 检查。
只含 `example`，不引入声明。生成脚本 `build-logs/scratch/S-CH11-CONS2/mkport3.py`。
-/

-- RF.LongTime.ParabolicSeedRecenterPortC11P  [PORT, PEND]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
open private ObservedHistory.exists_past_seed_core_traces_of_metric_distortion from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicSeedRicciPortC11P
namespace GC.LongTime
universe u
#guard_msgs (drop warning) in
example :
    ∀ {H : ObservedHistory.{u}} {T aSeed : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ T) (p : (H.stageAt T).Carrier) (r A : ℝ)
    (hA : 1 < A) (htime : 2 * r ^ 2 < (T : ℝ))
    (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (hseed : hasSmallParabolicCurvature H T p r)
    (hvolume : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      DifferentialGeometry.Geometry.Collapse.ballVolume
        (H.stageMetric (H.activeStage T) T) p r)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ T)
    (hv : (T : ℝ) - r ^ 2 / 2 ≤ (v : ℝ)),
    let O := seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
      (H.activeStage_mono hvT)
    let R := r / 100
    hasSmallParabolicCurvature H v O R ∧
      ENNReal.ofReal ((A⁻¹ * Real.exp (-57) / 512) * R ^ 3) ≤
        DifferentialGeometry.Geometry.Collapse.ballVolume
          (H.stageMetric (H.activeStage v) v) O R ∧
      2 * R ^ 2 < (v : ℝ) :=
  @_root_.GC.LongTime.hasSmallParabolicCurvature.earlier_seed_on_half_depth
end GC.LongTime
end

-- RF.LongTime.ParabolicSeedVolumePortC11P  [PORT, PEND]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime
universe u
private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩
#guard_msgs (drop warning) in
example :
    ∀ {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {r w : ℝ}
    (hseed : hasSmallParabolicCurvature H t p r)
    (hvolume : ENNReal.ofReal (w * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) p r)
    {y : (H.stageAt t).Carrier}
    (hy : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4))
    {s : ℝ} (hs : 0 < s) (hsr : s ≤ r / 2),
    ENNReal.ofReal ((w * Real.exp (-3) / 512) * s ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) y s :=
  @_root_.GC.LongTime.hasSmallParabolicCurvature.volume_lower_of_nearby_center
#guard_msgs (drop warning) in
example :
    ∀ {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {r w : ℝ}
    (hseed : hasSmallParabolicCurvature H t p r)
    (hvolume : ENNReal.ofReal (w * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) p r)
    {y : (H.stageAt t).Carrier}
    (hy : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4))
    (v : Icc (0 : ℝ) H.horizon) (hvt : v ≤ t)
    (hv : (t : ℝ) - r ^ 2 ≤ (v : ℝ)),
    Nonempty (BackwardPointTrace H (H.activeStage v) (H.activeStage t)
      (H.activeStage_mono hvt) y) ∧
    ∀ A : BackwardPointTrace H (H.activeStage v) (H.activeStage t)
        (H.activeStage_mono hvt) y,
      ∀ s : ℝ, 0 < s → s ≤ r / 2 →
        ENNReal.ofReal ((w * Real.exp (-57) / 512) * s ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) s :=
  @_root_.GC.LongTime.hasSmallParabolicCurvature.volume_lower_along_nearby_trace
end GC.LongTime
end

-- RF.Surgery.History.AffineEventDistanceScalarPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal ENNReal
namespace GC.GeneralFlow
universe u
#guard_msgs (drop warning) in
example :
    ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {C : ℝ≥0}
    (E : RetainedCoreEvent P Q a s) (c : ℝ)
    (h : E.toMetricCutCapEvent.HasUniformDistanceScalar C),
    (translate_retained_event E c).toMetricCutCapEvent.HasUniformDistanceScalar C :=
  @_root_.GC.GeneralFlow.hasUniformDistanceScalar_translate_retained_event
example : type_of% @GC.GeneralFlow.AffineEventPrefix.hasUniformDistanceScalar_event :=
  @GC.GeneralFlow.AffineEventPrefix.hasUniformDistanceScalar_event
#guard_msgs (drop warning) in
example :
    ∀ {H K J : RetainedCoreHistory.{u}} {c : ℝ} {C : ℝ≥0}
    (hp : H.toHistory.IsPrefixOf J.toHistory)
    (A : AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount))
    (hH : ∀ i : Fin H.eventCount, (H.toHistory.event i).HasUniformDistanceScalar C)
    (hK : ∀ i : Fin K.eventCount, (K.toHistory.event i).HasUniformDistanceScalar C),
    ∀ i : Fin J.eventCount, (J.toHistory.event i).HasUniformDistanceScalar C :=
  @_root_.GC.GeneralFlow.hasUniformDistanceScalar_at_affine_join
end GC.GeneralFlow
end

-- RF.Surgery.History.AffineHistoryParabolicBall  [PATCHED, REG]
section
set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
namespace AffineEventPrefix
variable {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount))
#guard_msgs (drop warning) in
example :
    ∀ (j : Fin (K.eventCount + 1)),
                                              Fin (J.eventCount + 1) :=
  _root_.GC.GeneralFlow.AffineEventPrefix.stageIndex
    A
#guard_msgs (drop warning) in
example :
    ∀ (j : Fin (K.eventCount + 1)),
    (A.stageIndex j).val = offset + j.val :=
  _root_.GC.GeneralFlow.AffineEventPrefix.stageIndex_val
    A
#guard_msgs (drop warning) in
example :
    ∀ (j k : Fin (K.eventCount + 1)),
    A.stageIndex j ≤ A.stageIndex k ↔ j ≤ k :=
  _root_.GC.GeneralFlow.AffineEventPrefix.stageIndex_le_iff
    A
#guard_msgs (drop warning) in
example :
    ∀ (i : Fin K.eventCount),
    A.stageIndex i.castSucc = (A.eventIndex i).castSucc :=
  _root_.GC.GeneralFlow.AffineEventPrefix.stageIndex_castSucc
    A
#guard_msgs (drop warning) in
example :
    ∀ (i : Fin K.eventCount),
    A.stageIndex i.succ = (A.eventIndex i).succ :=
  _root_.GC.GeneralFlow.AffineEventPrefix.stageIndex_succ
    A
#guard_msgs (drop warning) in
example :
    A.stageIndex (Fin.last K.eventCount) = Fin.last J.eventCount :=
  _root_.GC.GeneralFlow.AffineEventPrefix.stageIndex_last
    A
#guard_msgs (drop warning) in
example :
    ∀ (j : Fin (K.eventCount + 1)),
    J.time (A.stageIndex j) = K.time j + c :=
  _root_.GC.GeneralFlow.AffineEventPrefix.stageIndex_time
    A
#guard_msgs (drop warning) in
example :
    ∀ (j : Fin (K.eventCount + 1)),
    J.stage (A.stageIndex j) = K.stage j :=
  _root_.GC.GeneralFlow.AffineEventPrefix.stageIndex_stage
    A
include A in
example : type_of% @GC.GeneralFlow.AffineEventPrefix.shift_nonneg :=
  @GC.GeneralFlow.AffineEventPrefix.shift_nonneg
#guard_msgs (drop warning) in
example :
    ∀ (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon),
                                  Icc (0 : ℝ) J.horizon :=
  _root_.GC.GeneralFlow.AffineEventPrefix.shiftTime
    A
#guard_msgs (drop warning) in
example :
    ∀ (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon),
                                  (A.shiftTime hhor t : ℝ) = (t : ℝ) + c :=
  _root_.GC.GeneralFlow.AffineEventPrefix.shiftTime_val
    A
#guard_msgs (drop warning) in
example :
    ∀ (hhor : J.horizon = K.horizon + c)
    (s t : Icc (0 : ℝ) K.horizon),
                                    A.shiftTime hhor s ≤ A.shiftTime hhor t ↔ s ≤ t :=
  _root_.GC.GeneralFlow.AffineEventPrefix.shiftTime_le_iff
    A
#guard_msgs (drop warning) in
example :
    ∀ (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon),
    J.toHistory.activeStage (A.shiftTime hhor t) = A.stageIndex (K.toHistory.activeStage t) :=
  _root_.GC.GeneralFlow.AffineEventPrefix.activeStage_shift_eq
    A
#guard_msgs (drop warning) in
example :
    ∀ (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon),
    J.toHistory.stageAt (A.shiftTime hhor t) = K.toHistory.stageAt t :=
  _root_.GC.GeneralFlow.AffineEventPrefix.stageAt_shift_eq
    A
#guard_msgs (drop warning) in
example :
    ∀ (hfinal : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    (j : Fin (K.eventCount + 1)) (t : ℝ),
    HEq (J.toHistory.stageMetric (A.stageIndex j) (t + c))
      (K.toHistory.stageMetric j t) :=
  _root_.GC.GeneralFlow.AffineEventPrefix.stageMetric_shift_heq
    A
#guard_msgs (drop warning) in
example :
    ∀ (hhor : J.horizon = K.horizon + c)
    (hfinal : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    (t : Icc (0 : ℝ) K.horizon),
    HEq (J.toHistory.stageMetric (J.toHistory.activeStage (A.shiftTime hhor t))
      (A.shiftTime hhor t)) (K.toHistory.stageMetric (K.toHistory.activeStage t) t) :=
  _root_.GC.GeneralFlow.AffineEventPrefix.sliceMetric_shift_heq
    A
example : type_of% @GC.GeneralFlow.AffineEventPrefix.traceEquiv :=
  @GC.GeneralFlow.AffineEventPrefix.traceEquiv
#guard_msgs (drop warning) in
example :
    ∀ {first last : Fin (K.eventCount + 1)} {hle : first ≤ last}
    {p : (K.stage last).Carrier} (B : BackwardPointTrace K.toHistory first last hle p)
    (j : Fin (K.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last),
    HEq ((A.traceEquiv first last hle p B).point (A.stageIndex j)
      ((A.stageIndex_le_iff _ _).mpr hf) ((A.stageIndex_le_iff _ _).mpr hl))
      (B.point j hf hl) :=
  _root_.GC.GeneralFlow.AffineEventPrefix.traceEquiv_point_heq
    A
example : type_of% @GC.GeneralFlow.AffineEventPrefix.traceEquiv_symm_point_heq :=
  @GC.GeneralFlow.AffineEventPrefix.traceEquiv_symm_point_heq
end AffineEventPrefix
namespace AffineEventPrefix
variable {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount))
#guard_msgs (drop warning) in
example :
    ∀ (hhor : J.horizon = K.horizon + c)
    (hfinal : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    (t : Icc (0 : ℝ) K.horizon) (p : (K.toHistory.stageAt t).Carrier) (r : ℝ)
    (hrtime : r ^ 2 ≤ (t : ℝ)),
    J.toHistory.isParabolicallyRmControlledBall (A.shiftTime hhor t)
      ((A.stageAt_shift_eq hhor t).symm ▸ p) r ↔
    K.toHistory.isParabolicallyRmControlledBall t p r :=
  _root_.GC.GeneralFlow.AffineEventPrefix.isParabolicallyRmControlledBall_shift_iff
    A
#guard_msgs (drop warning) in
example :
    ∀ (hhor : J.horizon = K.horizon + c)
    (hfinal : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    (t : Icc (0 : ℝ) K.horizon) (p : (K.toHistory.stageAt t).Carrier) (r : ℝ),
    riemannianVolumeMeasure ThreeModel (J.toHistory.stageAt (A.shiftTime hhor t)).Carrier
      (J.toHistory.stageMetric (J.toHistory.activeStage (A.shiftTime hhor t)) (A.shiftTime hhor t))
      (riemannianBallOf
        (J.toHistory.stageMetric (J.toHistory.activeStage (A.shiftTime hhor t)) (A.shiftTime hhor
          t))
        ((A.stageAt_shift_eq hhor t).symm ▸ p) r) =
    riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt t).Carrier
      (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
      (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t) p r) :=
  _root_.GC.GeneralFlow.AffineEventPrefix.ball_volume_shift_eq
    A
end AffineEventPrefix
end GC.GeneralFlow
end

-- RF.Surgery.History.BoundedHistoryEventsPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow
universe u
#guard_msgs (drop warning) in
example :
    ∀ {H J : ObservedHistory.{u}} (hprefix : H.IsPrefixOf J)
    (j : Fin J.eventCount) (hj : J.time j.succ ≤ H.horizon),
    j.val < H.eventCount :=
  @_root_.GC.GeneralFlow.event_index_lt_of_birth_le_prefix_horizon
#guard_msgs (drop warning) in
example :
    ∀ {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    (hprefix : H.toHistory.IsPrefixOf J.toHistory)
    (j : Fin J.eventCount) (hj : J.time j.succ ≤ H.horizon),
    ∃! i : Fin H.eventCount, i.castLE I.count_le = j :=
  @_root_.GC.GeneralFlow.exists_unique_original_event_of_birth_le_prefix_horizon
#guard_msgs (drop warning) in
example :
    ∀ {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    (i : Fin H.eventCount),
    (∀ v : ℝ, HEq ((J.toHistory.event (i.castLE I.count_le)).incoming.flow.base.metric v)
      ((H.toHistory.event i).incoming.flow.base.metric v)) ∧
    HEq (J.toHistory.event (i.castLE I.count_le)).terminal.metric
      (H.toHistory.event i).terminal.metric ∧
    HEq (J.toHistory.event (i.castLE I.count_le)).outputMetric
      (H.toHistory.event i).outputMetric :=
  @_root_.GC.GeneralFlow.raw_prefix_incoming_metric_data
#guard_msgs (drop warning) in
example :
    ∀ {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    (i : Fin H.eventCount) {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p),
    J.time (i.castLE I.count_le).castSucc = H.time i.castSucc ∧
    J.time (i.castLE I.count_le).succ = H.time i.succ ∧
    J.stage (i.castLE I.count_le).castSucc = H.stage i.castSucc ∧
    J.stage (i.castLE I.count_le).succ = H.stage i.succ ∧
    (∀ v : ℝ, HEq ((J.toHistory.event (i.castLE I.count_le)).incoming.flow.base.metric v)
      ((H.toHistory.event i).incoming.flow.base.metric v)) ∧
    HEq (J.toHistory.event (i.castLE I.count_le)).terminal.metric
      (H.toHistory.event i).terminal.metric ∧
    HEq (J.toHistory.event (i.castLE I.count_le)).outputMetric
      (H.toHistory.event i).outputMetric ∧
    HEq (I.transportRecord R).nominalRadius R.nominalRadius ∧
    HEq (I.transportRecord R).delta R.delta ∧
    HEq (I.transportRecord R).order R.order ∧
    HEq (I.transportRecord R).neck R.neck ∧
    HEq (I.transportRecord R).static R.static :=
  @_root_.GC.GeneralFlow.raw_prefix_original_event_data
#guard_msgs (drop warning) in
example :
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (step : ∀ n, RawInitialPrefix (F.tower.history n) (F.tower.history (n + 1)))
    (Tmax : ℝ),
    ∃ N : ℕ, Tmax < (N : ℝ) ∧
      ∀ (n : ℕ) (hNn : N ≤ n),
        let I := rawPrefixOfLE F step N n hNn;
        ∀ (j : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time j.succ ≤ Tmax →
          ∃! i : Fin (F.tower.history N).eventCount, i.castLE I.count_le = j :=
  @_root_.GC.GeneralFlow.exists_fixed_history_for_bounded_event_queries
end GC.GeneralFlow
end

-- RF.Surgery.History.GeometricObservationFineQualityPortC11P  [PORT, PEND]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal ENNReal
namespace GC.GeneralFlow
universe u
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)
#guard_msgs (drop warning) in
example :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenter : ℝ), 4 ≤ recenter ∧
      PreparedDistanceClassProvider fixed recenter Cdist :=
  (@_root_.GC.GeneralFlow.exists_common_prepared_geometric_observation_extension_before_quality_with_distance_scalars).imp fun Cdist h =>
    ⟨h.1, h.2.imp fun fixed h => h.imp fun r h => ⟨h.1.1, h.2⟩⟩
#guard_msgs (drop warning) in
example :
    ∃ (fixed : StaticCapScaffold) (recenter : ℝ), 4 ≤ recenter ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
    ∀ (δcap ρcap εcapRequest DcapRequest : ℝ) (mcapRequest : ℕ),
      0 < δcap → 0 < ρcap → 0 < εcapRequest → 0 < DcapRequest →
    ∃ (p₀ : CutoffParameters) (δb ρb : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
      0 < δb ∧ δb ≤ δcap ∧ 0 < ρb ∧ ρb ≤ ρcap ∧
      p₀.modelAccuracy ≤ εcapRequest ∧ DcapRequest ≤ p₀.modelRadius ∧
      mcapRequest ≤ p₀.modelOrder ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
      (∀ (L : RetainedCoreHistory.{u}) (IL : InitialIdentification P g L.toHistory)
        (pL : CutoffParameters)
        (R : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL),
        L.horizon ≤ B → L.IsCanonicalCutoffRecordFamily p₀ δb ρb R →
        L.NoncollapsedBefore κ ε L.horizon) ∧
      PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb :=
  @_root_.GC.GeneralFlow.exists_common_prepared_geometric_observation_extension_before_quality
#guard_msgs (drop warning) in
example :
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B),
    ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
    ∀ (δcap ρcap εcapRequest DcapRequest : ℝ) (mcapRequest : ℕ),
      0 < δcap → 0 < ρcap → 0 < εcapRequest → 0 < DcapRequest →
    ∃ (p₀ : CutoffParameters) (δb ρb : ℝ),
      0 < δb ∧ δb ≤ δcap ∧ 0 < ρb ∧ ρb ≤ ρcap ∧
      p₀.modelAccuracy ≤ εcapRequest ∧ DcapRequest ≤ p₀.modelRadius ∧
      mcapRequest ≤ p₀.modelOrder ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
    ∀ (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
      (p : CutoffParameters)
      (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.horizon < B → H.IsCanonicalCutoffRecordFamily p₀ δb ρb old →
      HistoryEventControl H →
    ∃ εK κK κJ : ℝ, 0 < εK ∧ εK < 1 / 11 ∧ 0 < κK ∧ 0 < κJ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (K : RetainedCoreHistory.{u})
      (IK : InitialIdentification (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount)) K.toHistory)
      (pB pF : CutoffParameters) (δbound ρbound v : ℝ)
      (fine : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pF),
      K.horizon = B - H.time (Fin.last H.eventCount) ∧
      (InitialIdentification.atZero (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount))).IsPrefixOf IK ∧
      HistoryEventControl K ∧ K.NoncollapsedBefore κK εK K.horizon ∧
      pF.fixed = p.fixed ∧ pF.recenterConstant = p.recenterConstant ∧
      pF.modelAccuracy ≤ εcut ∧ Dcut ≤ pF.modelRadius ∧ mcut ≤ pF.modelOrder ∧
      0 < δbound ∧ δbound ≤ δcut ∧ 0 < ρbound ∧ ρbound ≤ ρcut ∧
      pB.recenterConstant * δbound ≤ 1 / 2 ∧ 0 < v ∧
      K.IsCanonicalCutoffRecordFamily pB δbound ρbound fine ∧
      (∀ i : Fin K.eventCount,
        ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
              (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
            (K.coreEvent i).terminal.metric F) ∧
      ∃ (hwin : ∀ i b, ((fine i).static b).hasLinkedCanonicalWindow_C12X)
        (_hrecK : RecordHypFar_C12X (5 / 4) K fine)
        (hD : p.modelRadius ≤ pF.modelRadius)
        (hm : p.modelOrder ≤ pF.modelOrder)
        (hacc : pF.modelAccuracy ≤ p.modelAccuracy),
        let c := H.time (Fin.last H.eventCount)
        let pC := pF.withModelWindow p.modelRadius p.modelOrder p.modelAccuracy
          p.modelRadius_pos (pF.modelAccuracy_pos.trans_le hacc)
        let coarse : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pC :=
          fun i => (fine i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
              p.modelRadius_pos hD hm hacc
        let q := p.spliceAfter (translate_cutoff_parameters pC c) H.horizon
        ∃ (J : RetainedCoreHistory.{u})
          (A : AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount))
          (I : RawInitialPrefix H J)
          (hn : H.eventCount ≤ J.eventCount)
          (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i q)
          (hp : H.toHistory.IsPrefixOf J.toHistory)
          (IJ : InitialIdentification P g J.toHistory),
          IH.IsPrefixOf IJ ∧ J.horizon = B ∧ HistoryEventControl J ∧
          J.NoncollapsedBefore κJ ε B ∧
          J.IsCanonicalCutoffRecordFamily p₀ δb ρb records ∧
          J.NoncollapsedBefore κ ε B ∧
          (q.fixed = p.fixed ∧ q.modelRadius = p.modelRadius ∧
            q.modelOrder = p.modelOrder ∧ q.modelAccuracy = p.modelAccuracy ∧
            q.recenterConstant = p.recenterConstant) ∧
          (∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
            (K.toHistory.stageMetric (Fin.last K.eventCount) t)) ∧
          (∀ t : ℝ, t ≤ H.horizon → q.delta t = p.delta t ∧
            q.neckRadius t = p.neckRadius t ∧ q.protectedRadius t = p.protectedRadius t) ∧
          (∀ i b, ((records i).static b).hasCanonicalWindow) ∧
          (∀ i : Fin H.eventCount,
            HEq (records (i.castLE hn)).nominalRadius (old i).nominalRadius ∧
            HEq (records (i.castLE hn)).delta (old i).delta ∧
            HEq (records (i.castLE hn)).order (old i).order ∧
            HEq (records (i.castLE hn)).neck (old i).neck ∧
            HEq (records (i.castLE hn)).static (old i).static) ∧
          ∀ i : Fin K.eventCount,
            HEq (records (A.eventIndex i)).nominalRadius (fine i).nominalRadius ∧
            HEq (records (A.eventIndex i)).delta (fine i).delta ∧
            HEq (records (A.eventIndex i)).order (fine i).order ∧
            HEq (records (A.eventIndex i)).neck (fine i).neck ∧
            HEq (records (A.eventIndex i)).static
              (fun b => translate_presented_static_cap (K.coreEvent i) c ((coarse i).static b)) :=
  @_root_.GC.GeneralFlow.exists_prepared_geometric_observation_extension_before_quality
#guard_msgs (drop warning) in
example :
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B),
    ∃ (p₀ : CutoffParameters) (δb ρb ε κ : ℝ),
      0 < δb ∧ 0 < ρb ∧ 0 < ε ∧ 0 < κ ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
    ∀ (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
      (p : CutoffParameters)
      (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.horizon < B → H.IsCanonicalCutoffRecordFamily p₀ δb ρb old →
      HistoryEventControl H →
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (J : RetainedCoreHistory.{u}) (IJ : InitialIdentification P g J.toHistory)
      (K : RetainedCoreHistory.{u})
      (A : AffineEventPrefix K J (H.time (Fin.last H.eventCount)) H.eventCount
        (Fin.last K.eventCount))
      (I : RawInitialPrefix H J) (q pFine : CutoffParameters)
      (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i q)
      (fine : ∀ i : Fin K.eventCount,
        GeometricCutoffRecord J.toHistory (A.eventIndex i) pFine),
      J.horizon = B ∧ IH.IsPrefixOf IJ ∧ HistoryEventControl J ∧
      J.IsCanonicalCutoffRecordFamily p₀ δb ρb records ∧
      J.NoncollapsedBefore κ ε B ∧
      (∀ t : ℝ, t ≤ H.horizon → q.delta t = p.delta t ∧
        q.neckRadius t = p.neckRadius t ∧ q.protectedRadius t = p.protectedRadius t) ∧
      (∀ i : Fin H.eventCount,
        HEq (records (i.castLE I.count_le)).nominalRadius (old i).nominalRadius ∧
        HEq (records (i.castLE I.count_le)).delta (old i).delta ∧
        HEq (records (i.castLE I.count_le)).order (old i).order ∧
        HEq (records (i.castLE I.count_le)).neck (old i).neck ∧
        HEq (records (i.castLE I.count_le)).static (old i).static) ∧
      pFine.fixed = p₀.fixed ∧ pFine.recenterConstant = p₀.recenterConstant ∧
      pFine.modelAccuracy ≤ εcut ∧ Dcut ≤ pFine.modelRadius ∧
      mcut ≤ pFine.modelOrder ∧
      (∀ i b, ((fine i).static b).hasCanonicalWindow) ∧
      (∀ i : Fin K.eventCount,
        pFine.delta (J.time (A.eventIndex i).succ) ≤ δcut ∧
        pFine.neckRadius (J.time (A.eventIndex i).succ) ≤ ρcut) ∧
      ∀ i : Fin K.eventCount,
        HEq (records (A.eventIndex i)).nominalRadius (fine i).nominalRadius ∧
        HEq (records (A.eventIndex i)).delta (fine i).delta ∧
        HEq (records (A.eventIndex i)).order (fine i).order ∧
        HEq (records (A.eventIndex i)).neck (fine i).neck :=
  @_root_.GC.GeneralFlow.exists_geometric_observation_extension_with_fine_quality
end GC.GeneralFlow
end

-- RF.Surgery.History.HistoryParabolicBallPrefixTransport  [PATCHED, REG]
section
set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
universe u
open private cast_point cast_point_heq ball_mem_iff_of_metric_heq
  curvature_sq_eq_of_metric_heq trace_point_heq_of_index_eq
  lift_restricted_time restricted_controlled_ball from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsePrefix.Basic
open private regularCrossing_iff_of_samePresentation
  terminal_curvature_normSq_eq_of_samePresentation from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsingPresentation.Basic
end GC.GeneralFlow
end

-- RF.Surgery.History.PreparedSpatialBasePortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow
universe u
#guard_msgs (drop warning) in
example :
    ∀ (cMax : ℝ) (hcMax : 0 < cMax)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (prepared : ClosedBirthPreparedClass pBase C P g 1)
    (hbase : prepared.parameters = pBase),
    ∃ S : PreparedSpatialState pBase C P g 0 1,
      S.history = RetainedCoreHistory.atZero P g ∧
      HEq S.initial (InitialIdentification.atZero P g) ∧
      S.nativeStage = P ∧ HEq S.nativeMetric g ∧
      S.native = RetainedCoreHistory.atZero P g ∧
      HEq S.nativeInitial (InitialIdentification.atZero P g) ∧
      S.nativeParameters = prepared.parameters ∧ HEq S.prepared prepared ∧
      S.shift = 0 ∧ S.offset = 0 ∧ S.radius ≤ 1 ∧
      S.radius * Real.sqrt S.prepared.Qall ≤ 100 * cMax ∧
      S.parameters.delta = (fun _ => (1 : ℝ) / 2) ∧
      (∀ t : ℝ, S.parameters.neckRadius t = S.radius) :=
  @_root_.GC.GeneralFlow.exists_prepared_spatial_base_with_small_test_margin
#guard_msgs (drop warning) in
example :
    ∀ (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (prepared : ClosedBirthPreparedClass pBase C P g 1)
    (hbase : prepared.parameters = pBase),
    ∃ S : PreparedSpatialState pBase C P g 0 1,
      S.history = RetainedCoreHistory.atZero P g ∧
      HEq S.initial (InitialIdentification.atZero P g) ∧
      S.nativeStage = P ∧ HEq S.nativeMetric g ∧
      S.native = RetainedCoreHistory.atZero P g ∧
      HEq S.nativeInitial (InitialIdentification.atZero P g) ∧
      S.nativeParameters = prepared.parameters ∧ HEq S.prepared prepared ∧
      S.shift = 0 ∧ S.offset = 0 ∧ S.radius ≤ 1 ∧
      S.parameters.delta = (fun _ => (1 : ℝ) / 2) ∧
      (∀ t : ℝ, S.parameters.neckRadius t = S.radius) :=
  @_root_.GC.GeneralFlow.exists_prepared_spatial_base
end GC.GeneralFlow
end

-- RF.Surgery.History.PreparedSpatialChain  [VERBATIM, REG]
section
example : type_of% @GC.GeneralFlow.preparedSpatialHorizon := @GC.GeneralFlow.preparedSpatialHorizon
example : type_of% @GC.GeneralFlow.nat_lt_three_pow := @GC.GeneralFlow.nat_lt_three_pow
example : type_of% @GC.GeneralFlow.PreparedSpatialChain := @GC.GeneralFlow.PreparedSpatialChain
example : type_of% @GC.GeneralFlow.PreparedSpatialChain.observationTime :=
  @GC.GeneralFlow.PreparedSpatialChain.observationTime
example : type_of% @GC.GeneralFlow.PreparedSpatialChain.observation :=
  @GC.GeneralFlow.PreparedSpatialChain.observation
example : type_of% @GC.GeneralFlow.PreparedSpatialChain.observation_successor :=
  @GC.GeneralFlow.PreparedSpatialChain.observation_successor
example : type_of% @GC.GeneralFlow.PreparedSpatialChain.tower :=
  @GC.GeneralFlow.PreparedSpatialChain.tower
example : type_of% @GC.GeneralFlow.PreparedSpatialChain.observation_canonical :=
  @GC.GeneralFlow.PreparedSpatialChain.observation_canonical
end

-- RF.Surgery.History.PreparedSpatialDecay  [VERBATIM, REG]
section
example : type_of% @GC.GeneralFlow.PreparedSpatialChain.diagonal_delta_tendsto :=
  @GC.GeneralFlow.PreparedSpatialChain.diagonal_delta_tendsto
end

-- RF.Surgery.History.PreparedSpatialDiagonalDerivativePortC11P  [PORT, PEND]
section
set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal Topology
namespace GC.GeneralFlow
universe u
open private quality_prefix_stage quality_common_prefix_open_stage
  PreparedSpatialChain.quality_state_prefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualityTransport
open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
namespace PreparedSpatialChain
variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}
end PreparedSpatialChain
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower)
    (q : CutoffParameters) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hdiagonal : ∀ v : ℝ, 0 ≤ v → q.neckRadius v =
      (CutoffParameters.diagonal (fun m => (S.observation m).parameters)).neckRadius v),
    ∀ (n : ℕ) (v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (z : ((F.tower.history n).toHistory.stageAt v).Carrier),
      (F.tower.history n).time ((F.tower.history n).toHistory.activeStage v) < (v : ℝ) →
      (v : ℝ) < (F.tower.history n).toHistory.horizon →
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) t) z) (Iic (v : ℝ)) v| ≤
        C.Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) v) z ^ 2 :=
  @_root_.GC.GeneralFlow.PreparedSpatialChain.scalar_time_derivative_at_diagonal_threshold
end GC.GeneralFlow
end

-- RF.Surgery.History.PreparedSpatialDistanceBase  [VERBATIM, REG]
section
open GC.GeneralFlow in
example : type_of% @exists_prepared_spatial_base_with_distance_scalars_and_small_test_margin :=
  @exists_prepared_spatial_base_with_distance_scalars_and_small_test_margin
example : type_of% @GC.GeneralFlow.exists_prepared_spatial_base_with_distance_scalars :=
  @GC.GeneralFlow.exists_prepared_spatial_base_with_distance_scalars
end

-- RF.Surgery.History.PreparedSpatialDistanceChain  [VERBATIM, REG]
section
example : type_of% @GC.GeneralFlow.PreparedSpatialChain.observation_hasUniformDistanceScalar :=
  @GC.GeneralFlow.PreparedSpatialChain.observation_hasUniformDistanceScalar
example : type_of% @GC.GeneralFlow.PreparedSpatialChain.tower_hasUniformDistanceScalar :=
  @GC.GeneralFlow.PreparedSpatialChain.tower_hasUniformDistanceScalar
end

-- RF.Surgery.History.PreparedSpatialDistanceData  [VERBATIM, REG]
section
example : type_of% @GC.GeneralFlow.ClosedBirthPreparedClass.HasDistanceExtension :=
  @GC.GeneralFlow.ClosedBirthPreparedClass.HasDistanceExtension
example : type_of% @GC.GeneralFlow.PreparedSpatialState.DistanceData :=
  @GC.GeneralFlow.PreparedSpatialState.DistanceData
end

-- RF.Surgery.History.PreparedSpatialLargerBallAccuracyPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow.PreparedSpatialChain
universe u
open private state_delta_compat diagonal_delta_antitone from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDecay
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (A _t : ℝ),
                                                        ℝ :=
  @_root_.GC.GeneralFlow.PreparedSpatialChain.diagonalLargerBallAccuracy
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (n : ℕ) (s : ℝ)
    (hs : preparedSpatialHorizon n < s) (hsB : s ≤ (3 : ℝ) ^ n),
    (CutoffParameters.diagonal (fun k => (S.observation k).parameters)).delta s =
      S.accuracy n :=
  @_root_.GC.GeneralFlow.PreparedSpatialChain.diagonal_delta_eq_accuracy_on_block
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (hdrop : ∀ n : ℕ, S.accuracy n ≤
      (S.state n).parameters.delta (preparedSpatialHorizon n) / 4)
    (s : ℝ) (hs : 0 ≤ s),
    (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta
        (3 * max 1 s) ≤
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta s / 4 :=
  @_root_.GC.GeneralFlow.PreparedSpatialChain.diagonal_delta_quarter_lag
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (hdrop : ∀ n : ℕ, S.accuracy n ≤
      (S.state n).parameters.delta (preparedSpatialHorizon n) / 4),
    (∀ A t : ℝ, 0 < A → 0 ≤ t → 0 < S.diagonalLargerBallAccuracy A t) ∧
    (∀ A : ℝ, 0 < A → AntitoneOn (S.diagonalLargerBallAccuracy A) (Ici 0)) ∧
    (∀ t : ℝ, 0 ≤ t →
      AntitoneOn (fun A => S.diagonalLargerBallAccuracy A t) (Ioi 0)) ∧
    (∀ t : ℝ, 0 < t →
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta t <
        S.diagonalLargerBallAccuracy (2 * t) (2 * t)) ∧
    ∀ A s : ℝ, 0 < A → 0 ≤ s →
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta s <
        S.diagonalLargerBallAccuracy A s → A < 12 * max 1 s :=
  @_root_.GC.GeneralFlow.PreparedSpatialChain.diagonalLargerBallAccuracy_spec
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (hdrop : ∀ n : ℕ, S.accuracy n ≤
      (S.state n).parameters.delta (preparedSpatialHorizon n) / 4)
    (m : ℕ) (A s : ℝ) (hA : 0 < A) (hs : 0 ≤ s) (hsB : s ≤ (3 : ℝ) ^ m)
    (hsmall :
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta s <
        S.diagonalLargerBallAccuracy A s),
    A < 12 * (3 : ℝ) ^ m :=
  @_root_.GC.GeneralFlow.PreparedSpatialChain.diagonalLargerBallAccuracy_birth_block_bound
end GC.GeneralFlow.PreparedSpatialChain
end

-- RF.Surgery.History.PreparedSpatialOwnThresholdDerivatives  [PATCHED, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology Pointwise
namespace GC.GeneralFlow
universe u
open private event_samePresentation_of_prefix derivative_bound_of_translated_germ from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative
open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
open private retained_event_incoming_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext d eta εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (t : Icc (0 : ℝ) W.oldNative.horizon) (htop : (t : ℝ) < W.oldNative.horizon),
    let K := W.oldNative
    let M := L.prepared.Qall
    K.EventSlabsDerivative C.Ctime M (K.toHistory.activeStage t) ∧
    K.EventSlabsGradient C.Cgrad M (K.toHistory.activeStage t) ∧
    (∀ i : Fin K.eventCount, i.castSucc = K.toHistory.activeStage t →
      (K.toHistory.event i).incoming.DerivativeBoundBefore C.Ctime M t) ∧
    (∀ h : K.time (Fin.last K.eventCount) < K.horizon,
      K.toHistory.activeStage t = Fin.last K.eventCount →
      ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore C.Ctime M t) ∧
    ∀ y : (K.toHistory.stageAt t).Carrier,
      M < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) y →
      (K.time (K.toHistory.activeStage t) < (t : ℝ) →
        |derivWithin (fun v => metricScalarAt
          (K.toHistory.stageMetric (K.toHistory.activeStage t) v) y) (Iic (t : ℝ)) t| ≤
          C.Ctime * metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) y ^ 2) ∧
      ∀ v : TangentSpace I3 y,
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
          (metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t)) y v)| ≤
        C.Cgrad * metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) y *
          Real.sqrt (metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) y) *
          Real.sqrt ((K.toHistory.stageMetric (K.toHistory.activeStage t) t).inner y v v) :=
  @_root_.GC.GeneralFlow.PreparedSpatialStepRetention.own_threshold_native_certificates
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hLR : PreparedSpatialSuccessor L R activation eta d)
    (hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
    (hoffset : R.offset = L.history.eventCount)
    (j : Fin (R.history.eventCount + 1)) (hj : L.offset ≤ j.val)
    (y : (R.history.stage j).Carrier)
    (s : ℝ) (hs : s ∈ Ico (R.history.time j) (R.history.toHistory.stageEndTime j))
    (hscalar : L.prepared.Qall < metricScalarAt (R.history.toHistory.stageMetric j s) y),
    (R.history.time j < s →
      |derivWithin (fun v => metricScalarAt (R.history.toHistory.stageMetric j v) y)
        (Iic s) s| ≤ C.Ctime * metricScalarAt (R.history.toHistory.stageMetric j s) y ^ 2) ∧
    ∀ v : TangentSpace I3 y,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
        (metricScalarAt (R.history.toHistory.stageMetric j s)) y v)| ≤
      C.Cgrad * metricScalarAt (R.history.toHistory.stageMetric j s) y *
        Real.sqrt (metricScalarAt (R.history.toHistory.stageMetric j s) y) *
        Real.sqrt ((R.history.toHistory.stageMetric j s).inner y v v) :=
  @_root_.GC.GeneralFlow.PreparedSpatialStepRetention.time_derivative_gradient_on_old_native_tail_at_own_threshold
end GC.GeneralFlow
end

-- RF.Surgery.History.PreparedSpatialQualityTransport  [PATCHED, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology NNReal
namespace GC.GeneralFlow
universe u
namespace PreparedSpatialChain
variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}
  (S : PreparedSpatialChain pBase C P g)
open private activation activation_strictMono from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecentCutoff
end PreparedSpatialChain
end GC.GeneralFlow
end

-- RF.Surgery.History.PreparedSpatialQueryReserve  [PATCHED, REG]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal
namespace GC.GeneralFlow
universe u
namespace PreparedSpatialChain
open private activation nat_le_activation
  horizon_lt_half_activation radius_eq_on_activation_band from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecentCutoff
end PreparedSpatialChain
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {cMax : ℝ}
    (S : PreparedSpatialChain pBase C P g)
    (hcMax : 0 < cMax)
    (hfit : ∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax)
    (hshift0 : (S.state 0).shift = 0)
    (hradius0 : ∀ t : ℝ, (S.state 0).parameters.neckRadius t = (S.state 0).radius)
    (hshift : ∀ n, (S.state (n + 1)).shift =
      (S.state n).history.time (Fin.last (S.state n).history.eventCount))
    {T r : ℝ} (hr : 0 < r) (hT : 2 * r ^ 2 < T)
    (hsmall :
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T / 100 < r),
    let σ := (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T
    ∃ j : ℕ,
      σ = (S.state j).radius ∧
      (j = 0 ∧ T ≤ (5 / 6 : ℝ) ∨
        ∃ k : ℕ, j = k + 1 ∧ (5 / 6 : ℝ) * 3 ^ k < T ∧
          T ≤ (5 / 6 : ℝ) * 3 ^ (k + 1)) ∧
      (S.state j).shift < T - (σ / 100) ^ 2 ∧
      T < (3 : ℝ) ^ j ∧
      0 < σ / 100 ∧
      σ / 100 ≤ cMax / Real.sqrt (S.state j).prepared.Qall ∧
      (let M := (S.state j).prepared.Qall
       let c := (σ / 100) * Real.sqrt M
       1 ≤ M ∧ (S.state j).prepared.qcan ≤ M ∧
       (S.state j).prepared.qs ≤ M ∧ (S.state j).prepared.Qbirth ≤ M ∧
       (S.state j).prepared.Qzero ≤ M ∧
       0 < c ∧ c ≤ cMax ∧ σ / 100 = c / Real.sqrt M ∧
       c ^ 2 / M < T - (S.state j).shift) :=
  @_root_.GC.GeneralFlow.PreparedSpatialChain.exists_small_test_reserve_in_same_native_class
#guard_msgs (drop warning) in
example :
    ∀ {Dstar εReserve : ℝ}
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {cMax : ℝ}
    (S : PreparedSpatialChain pBase C P g)
    (hquality : ∀ n, (S.state n).prepared.HasReserveQuality Dstar εReserve)
    (hcMax : 0 < cMax)
    (hfit : ∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax)
    (hshift0 : (S.state 0).shift = 0)
    (hradius0 : ∀ t : ℝ, (S.state 0).parameters.neckRadius t = (S.state 0).radius)
    (hshift : ∀ n, (S.state (n + 1)).shift =
      (S.state n).history.time (Fin.last (S.state n).history.eventCount))
    {T r : ℝ} (hr : 0 < r) (hT : 2 * r ^ 2 < T)
    (hsmall :
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T / 100 < r),
    let σ := (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T
    ∃ j : ℕ,
      (S.state j).prepared.HasReserveQuality Dstar εReserve ∧
      σ = (S.state j).radius ∧
      (j = 0 ∧ T ≤ (5 / 6 : ℝ) ∨
        ∃ k : ℕ, j = k + 1 ∧ (5 / 6 : ℝ) * 3 ^ k < T ∧
          T ≤ (5 / 6 : ℝ) * 3 ^ (k + 1)) ∧
      (S.state j).shift < T - (σ / 100) ^ 2 ∧
      T < (3 : ℝ) ^ j ∧
      0 < σ / 100 ∧
      σ / 100 ≤ cMax / Real.sqrt (S.state j).prepared.Qall ∧
      (let M := (S.state j).prepared.Qall
       let c := (σ / 100) * Real.sqrt M
       1 ≤ M ∧ (S.state j).prepared.qcan ≤ M ∧
       (S.state j).prepared.qs ≤ M ∧ (S.state j).prepared.Qbirth ≤ M ∧
       (S.state j).prepared.Qzero ≤ M ∧
       0 < c ∧ c ≤ cMax ∧ σ / 100 = c / Real.sqrt M ∧
       c ^ 2 / M < T - (S.state j).shift) :=
  @_root_.GC.GeneralFlow.PreparedSpatialChain.exists_small_test_reserve_in_same_native_class_with_reserve_quality
end GC.GeneralFlow
end

-- RF.Surgery.History.PreparedSpatialRecentCutoff  [PATCHED, REG]
section
set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow.PreparedSpatialChain
universe u
variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}
  (S : PreparedSpatialChain pBase C P g)
#guard_msgs (drop warning) in
example :
    let q := CutoffParameters.diagonal (fun n => (S.observation n).parameters)
    ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → ∀ n : ℕ, t ≤ (n : ℝ) →
      ∀ i : Fin (S.observation n).history.eventCount,
        (S.observation n).history.time i.succ ∈ Icc (t / 2) t →
        ∀ h, ((S.observation n).records i).nominalRadius h ≤ η * q.neckRadius t :=
  _root_.GC.GeneralFlow.PreparedSpatialChain.recent_cutoff_decay
    S
end GC.GeneralFlow.PreparedSpatialChain
end

-- RF.Surgery.History.PreparedSpatialReserveBallPortC11P  [PORT, PEND]
section
set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology
namespace GC.GeneralFlow
universe u
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext d eta εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hcan : ∀ i b, ((W.oldNativeRecords i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((W.oldNativeRecords i).static b).neck.scale / 2 ≤
      metricScalarAt ((W.oldNativeRecords i).static b).witness.metric
        (((W.oldNativeRecords i).static b).witness.cap z))
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : W.oldNative.EventSlabsPinched phi)
    (t : Icc (0 : ℝ) W.oldNative.horizon) (htop : (t : ℝ) < W.oldNative.horizon)
    (hlast : W.oldNative.toHistory.activeStage t = Fin.last W.oldNative.eventCount →
      ∃ h : W.oldNative.time (Fin.last W.oldNative.eventCount) < W.oldNative.horizon,
        Perelman.PhiAlmostNonnegative (W.oldNative.finalSlab h).flow
          (Icc (W.oldNative.time (Fin.last W.oldNative.eventCount)) W.oldNative.horizon) phi)
    (y : (W.oldNative.toHistory.stageAt t).Carrier)
    (hRle : metricScalarAt
      (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage t) t) y ≤
        L.prepared.Qall)
    (hback : (L.radius / 100) ^ 2 ≤ (t : ℝ))
    (hgradScale : (C.Cgrad : ℝ) * (L.radius / 100) * Real.sqrt L.prepared.Qall ≤ 1 / 4)
    (htimeScale : C.Ctime * (4 * L.prepared.Qall) * (L.radius / 100) ^ 2 ≤ 1 / 2)
    (hpinchScale : (L.radius / 100) ^ 4 *
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * L.prepared.Qall)) ^ 2 ≤ 1)
    (hlarge : ∀ i : Fin W.oldNative.eventCount,
      W.oldNative.time i.succ ∈ Ioc ((t : ℝ) - (L.radius / 100) ^ 2) (t : ℝ) →
      ∀ b : (W.oldNative.toHistory.event i).RetainedBoundaryIndex,
        16 * L.prepared.Qall < ((W.oldNativeRecords i).static b).neck.scale),
    W.oldNative.toHistory.isParabolicallyRmControlledBall t y (L.radius / 100) :=
  @_root_.GC.GeneralFlow.PreparedSpatialStepRetention.isParabolicallyRmControlledBall_at_reserve_of_scalar_le
end GC.GeneralFlow
end

-- RF.Surgery.History.PreparedSpatialReservePhysicalInputs  [VERBATIM, REG]
section
example : type_of% @GC.GeneralFlow.PreparedSpatialStepRetention.oldNative_hasCanonicalWindows :=
  @GC.GeneralFlow.PreparedSpatialStepRetention.oldNative_hasCanonicalWindows
example : type_of% @GC.GeneralFlow.exists_old_native_cap_scalar_quality :=
  @GC.GeneralFlow.exists_old_native_cap_scalar_quality
open GC.GeneralFlow.PreparedSpatialStepRetention in
example : type_of% @static_scale_gt_sixteen_own_threshold_of_class_bound :=
  @static_scale_gt_sixteen_own_threshold_of_class_bound
example : type_of% @GC.GeneralFlow.PreparedSpatialState.exists_pinching_for_old_native_extensions :=
  @GC.GeneralFlow.PreparedSpatialState.exists_pinching_for_old_native_extensions
end

-- RF.Surgery.History.PreparedSpatialReserveQualityData  [VERBATIM, REG]
section
example : type_of% @GC.GeneralFlow.ClosedBirthPreparedClass.HasReserveQuality :=
  @GC.GeneralFlow.ClosedBirthPreparedClass.HasReserveQuality
end

-- RF.Surgery.History.PreparedSpatialReserveTransport  [PATCHED, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology
namespace GC.GeneralFlow
universe u
open private castPoint castPoint_heq normSq_eq_of_metric_heq ball_mem_iff_of_metric_heq
  trace_point_heq traceIndexEquiv traceIndexEquiv_point_heq controlled_of_regular
  crossing_iff_of_translated_event from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.AffineHistoryParabolicBall
open private event_samePresentation_of_prefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative
open private own_threshold_native_tail_stageMetric from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialOwnThresholdDerivatives
open private regularCrossing_iff_of_samePresentation_heq controlled_ball_iff_of_prefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.HistoryParabolicBallPrefixTransport
namespace ReserveShiftedTracePresentation
end ReserveShiftedTracePresentation
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hLR : PreparedSpatialSuccessor L R activation eta d)
    (hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
    (hoffset : R.offset = L.history.eventCount)
    (τ : Icc (0 : ℝ) W.oldNative.horizon)
    (T : Icc (0 : ℝ) R.history.horizon) (hclock : (T : ℝ) = (τ : ℝ) + L.shift),
    R.history.toHistory.stageAt T = W.oldNative.toHistory.stageAt τ ∧
    HEq (R.history.toHistory.stageMetric (R.history.toHistory.activeStage T) T)
      (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage τ) τ) ∧
    ∀ (x : (R.history.toHistory.stageAt T).Carrier)
      (y : (W.oldNative.toHistory.stageAt τ).Carrier), HEq x y →
      ∀ r : ℝ, W.oldNative.toHistory.isParabolicallyRmControlledBall τ y r →
        R.history.toHistory.isParabolicallyRmControlledBall T x r :=
  @_root_.GC.GeneralFlow.PreparedSpatialStepRetention.full_native_query_transport
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower)
    (j : ℕ) {εcut Dcut : ℝ} {mcut : ℕ}
    (W : PreparedSpatialStepRetention (S.state j) (S.state (j + 1))
      (S.accuracy j) (1 / ((j : ℝ) + 2)) εcut Dcut mcut)
    (hshift : (S.state (j + 1)).shift =
      (S.state j).history.time (Fin.last (S.state j).history.eventCount))
    (hoffset : (S.state (j + 1)).offset = (S.state j).history.eventCount)
    (U : ℝ) (hU : 0 ≤ U)
    (T : Icc (0 : ℝ) (F.observation.observe U hU).horizon)
    (τ : Icc (0 : ℝ) W.oldNative.horizon)
    (hclock : (T : ℝ) = (τ : ℝ) + (S.state j).shift),
      let H := F.observation.observe U hU
      H.stageAt T = W.oldNative.toHistory.stageAt τ ∧
      HEq (H.stageMetric (H.activeStage T) T)
        (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage τ) τ) ∧
      ∀ (x : (H.stageAt T).Carrier)
        (y : (W.oldNative.toHistory.stageAt τ).Carrier), HEq x y →
        ∀ r : ℝ, W.oldNative.toHistory.isParabolicallyRmControlledBall τ y r →
          H.isParabolicallyRmControlledBall T x r :=
  @_root_.GC.GeneralFlow.PreparedSpatialChain.native_query_transport_to_observation
end GC.GeneralFlow
end

-- RF.Surgery.History.PreparedSpatialStepDerivative  [PATCHED, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal Topology Pointwise
namespace GC.GeneralFlow
universe u
open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
open private retained_event_incoming_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hLR : PreparedSpatialSuccessor L R activation eta d)
    (hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
    (hoffset : R.offset = L.history.eventCount)
    (j : Fin (R.history.eventCount + 1)) (hj : L.offset ≤ j.val)
    (y : (R.history.stage j).Carrier)
    (s : ℝ) (hs : s ∈ Ioo (R.history.time j) (R.history.toHistory.stageEndTime j))
    (hscalar : (L.radius ^ 2)⁻¹ <
      metricScalarAt (R.history.toHistory.stageMetric j s) y),
    |derivWithin (fun u => metricScalarAt (R.history.toHistory.stageMetric j u) y)
      (Iic s) s| ≤
      C.Ctime * metricScalarAt (R.history.toHistory.stageMetric j s) y ^ 2 :=
  @_root_.GC.GeneralFlow.PreparedSpatialStepRetention.derivative_bound_on_old_native_tail
end GC.GeneralFlow
end

-- RF.Surgery.History.PreparedSpatialStepRetention  [VERBATIM, REG]
section
example : type_of% @GC.GeneralFlow.PreparedSpatialStepRetention :=
  @GC.GeneralFlow.PreparedSpatialStepRetention
end

-- RF.Surgery.History.PreparedSpatialSurgery  [VERBATIM, REG]
section
example : type_of% @GC.GeneralFlow.PreparedSpatialChain.exists_surgery_with_spatial_control :=
  @GC.GeneralFlow.PreparedSpatialChain.exists_surgery_with_spatial_control
end

-- RF.Surgery.History.PreparedSpatialSurgeryDecayPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped ENNReal
namespace GC.GeneralFlow.PreparedSpatialChain
universe u
#guard_msgs (drop warning) in
example :
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g),
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q),
      F.tower = S.tower ∧
      (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
        q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy ∧
        q.recenterConstant = pBase.recenterConstant) ∧
      (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      (∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
        q.delta t = (S.observation n).parameters.delta t ∧
        q.neckRadius t = (S.observation n).parameters.neckRadius t ∧
        q.protectedRadius t = (S.observation n).parameters.protectedRadius t) ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
        (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) ∧
      (∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
        (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
        (q.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)
          C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart C.epsilon) ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) C.epsilon t) ∧
      (∃ hc : Monotone (fun n => (F.tower.history n).eventCount),
        ∀ (m n : ℕ) (hmn : m ≤ n),
          (F.tower.initial m).IsPrefixOf (F.tower.initial n) ∧
          ∀ i : Fin (F.tower.history m).eventCount,
            HEq (records n (i.castLE (hc hmn))).nominalRadius (records m i).nominalRadius ∧
            HEq (records n (i.castLE (hc hmn))).delta (records m i).delta ∧
            HEq (records n (i.castLE (hc hmn))).order (records m i).order ∧
            HEq (records n (i.castLE (hc hmn))).neck (records m i).neck ∧
            HEq (records n (i.castLE (hc hmn))).static (records m i).static) ∧
      Filter.Tendsto q.delta Filter.atTop (nhds (0 : ℝ)) ∧
      ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ,
        ∀ i : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
          ∀ h, (records n i).nominalRadius h ≤ η * q.neckRadius t :=
  @_root_.GC.GeneralFlow.PreparedSpatialChain.exists_surgery_with_spatial_control_and_decay
end GC.GeneralFlow.PreparedSpatialChain
end

-- RF.Surgery.History.PreparedSpatialUniformPinchingPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology
namespace GC.GeneralFlow
universe u
open private own_native_tail_trace_presentation from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveTransport
open private overlapCastPoint overlapCastPoint_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
#guard_msgs (drop warning) in
example :
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
      {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
      {L : PreparedSpatialState pBase C P g E B}
      {R : PreparedSpatialState pBase C P g B Bnext}
      (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
      (hLR : PreparedSpatialSuccessor L R activation eta d)
      (hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
      (hoffset : R.offset = L.history.eventCount)
      (hshift_nonneg : 0 ≤ L.shift),
      W.oldNative.EventSlabsPinched phi ∧
      ∀ hfinal : W.oldNative.time (Fin.last W.oldNative.eventCount) < W.oldNative.horizon,
        Perelman.PhiAlmostNonnegative (W.oldNative.finalSlab hfinal).flow
          (Icc (W.oldNative.time (Fin.last W.oldNative.eventCount)) W.oldNative.horizon) phi :=
  @_root_.GC.GeneralFlow.exists_uniform_pinching_for_same_full_native_steps
end GC.GeneralFlow
end

-- RF.Surgery.History.PreparedSpatialUniformReserveBallPortC11P  [PORT, PEND]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology
namespace GC.GeneralFlow
universe u
#guard_msgs (drop warning) in
example :
    ∀ (Dstar : ℝ) (hDstar : StandardCap.transitionEnd < Dstar),
    ∃ εcap : ℝ, 0 < εcap ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (C : ClosedBirthConstants),
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
    ∃ cMax : ℝ, 0 < cMax ∧
    ∀ {pBase : CutoffParameters}
      {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
      {L : PreparedSpatialState pBase C P g E B}
      {R : PreparedSpatialState pBase C P g B Bnext}
      (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
      (hLR : PreparedSpatialSuccessor L R activation eta d)
      (hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
      (hoffset : R.offset = L.history.eventCount)
      (hshift_nonneg : 0 ≤ L.shift)
      (hmodelRadius : Dstar ≤ L.prepared.parameters.modelRadius)
      (hmodelAccuracy : L.prepared.parameters.modelAccuracy ≤ εcap)
      (hmodelOrder : 2 ≤ L.prepared.parameters.modelOrder)
      (hclassScale : 32 * L.prepared.Qall * L.prepared.radiusBound ^ 2 ≤ 1)
      (hfit : L.radius * Real.sqrt L.prepared.Qall ≤ 100 * cMax)
      (t : Icc (0 : ℝ) W.oldNative.horizon) (htop : (t : ℝ) < W.oldNative.horizon)
      (y : (W.oldNative.toHistory.stageAt t).Carrier)
      (hRle : metricScalarAt
        (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage t) t) y ≤
          L.prepared.Qall)
      (hback : (L.radius / 100) ^ 2 ≤ (t : ℝ)),
      W.oldNative.toHistory.isParabolicallyRmControlledBall t y (L.radius / 100) :=
  @_root_.GC.GeneralFlow.exists_same_native_reserve_ball_control_of_retained_class_quality
end GC.GeneralFlow
end

-- RF.Surgery.History.RawPrefixFineRecordsPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff BigOperators NNReal
namespace GC.GeneralFlow
universe u
#guard_msgs (drop warning) in
example :
    ∀ {H J K : RetainedCoreHistory.{u}}
    (I : RawInitialPrefix H J) (I' : RawInitialPrefix J K),
                                                             RawInitialPrefix H K :=
  @_root_.GC.GeneralFlow.rawPrefix_trans
example : type_of% @GC.GeneralFlow.prefixPullTrace := @GC.GeneralFlow.prefixPullTrace
#guard_msgs (drop warning) in
example :
    ∀ {H J : RetainedCoreHistory.{u}}
    (I : RawInitialPrefix H J) {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {y : (J.stage (last.castLE (Nat.succ_le_succ I.count_le))).Carrier}
    (B : BackwardPointTrace J.toHistory
      (first.castLE (Nat.succ_le_succ I.count_le))
      (last.castLE (Nat.succ_le_succ I.count_le)) hle y)
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last),
    HEq ((prefixPullTrace I hle B).point j hf hl)
      (B.point (j.castLE (Nat.succ_le_succ I.count_le)) hf hl) :=
  @_root_.GC.GeneralFlow.prefixPullTrace_point_heq
#guard_msgs (drop warning) in
example :
    ∀ {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p)
    (b' : (J.toHistory.event (i.castLE I.count_le)).RetainedBoundaryIndex),
    ∃ b : (H.toHistory.event i).RetainedBoundaryIndex,
      HEq b b' ∧ (∀ z : standardCapWindow p.modelRadius,
        HEq ((R.static b).window z) (((I.transportRecord R).static b').window z)) ∧
      (R.static b).neck.scale = ((I.transportRecord R).static b').neck.scale ∧
      R.nominalRadius ⟨b.val.1⟩ = (I.transportRecord R).nominalRadius ⟨b'.val.1⟩ :=
  @_root_.GC.GeneralFlow.prefix_fine_cap_label
#guard_msgs (drop warning) in
example :
    ∀ {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p)
    (k : Fin (H.eventCount + 1)) (hik : i.succ ≤ k)
    (last : Fin (J.eventCount + 1))
    (hklast : k.castLE (Nat.succ_le_succ I.count_le) ≤ last)
    {y : (J.stage last).Carrier}
    (B : BackwardPointTrace J.toHistory (i.castLE I.count_le).succ last
      ((show (i.castLE I.count_le).succ ≤ k.castLE (Nat.succ_le_succ I.count_le) from hik).trans
        hklast) y)
    (b' : (J.toHistory.event (i.castLE I.count_le)).RetainedBoundaryIndex)
    (z : standardCapWindow p.modelRadius)
    (hanchor : B.point (i.castLE I.count_le).succ le_rfl ((show (i.castLE I.count_le).succ ≤
      k.castLE (Nat.succ_le_succ I.count_le) from hik).trans hklast) =
      ((I.transportRecord R).static b').window z),
    ∃ (x : (H.stage k).Carrier) (B0 : BackwardPointTrace H.toHistory i.succ k hik x)
      (b : (H.toHistory.event i).RetainedBoundaryIndex),
      HEq x (B.point (k.castLE (Nat.succ_le_succ I.count_le)) hik hklast) ∧
      HEq b b' ∧ B0.point i.succ le_rfl hik = (R.static b).window z ∧
      (∀ j (hf : i.succ ≤ j) (hl : j ≤ k),
        HEq (B0.point j hf hl)
          (B.point (j.castLE (Nat.succ_le_succ I.count_le)) hf ((show j.castLE (Nat.succ_le_succ
            I.count_le) ≤ k.castLE (Nat.succ_le_succ I.count_le) from hl).trans hklast))) ∧
      (R.static b).neck.scale = ((I.transportRecord R).static b').neck.scale ∧
      R.nominalRadius ⟨b.val.1⟩ = (I.transportRecord R).nominalRadius ⟨b'.val.1⟩ ∧
      ∀ t : ℝ, t - J.time (i.castLE I.count_le).succ = t - H.time i.succ :=
  @_root_.GC.GeneralFlow.prefix_part_of_fine_cap_trace
#guard_msgs (drop warning) in
example :
    ∀ {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    (i : Fin H.eventCount) (C : ℝ≥0) (q T : ℝ),
    ((J.toHistory.event (i.castLE I.count_le)).incoming.DerivativeBoundBefore C q T ↔
      (H.toHistory.event i).incoming.DerivativeBoundBefore C q T) ∧
    ((J.toHistory.event (i.castLE I.count_le)).incoming.GradientBoundBefore C q T ↔
      (H.toHistory.event i).incoming.GradientBoundBefore C q T) :=
  @_root_.GC.GeneralFlow.prefix_incoming_before_iff
#guard_msgs (drop warning) in
example :
    ∀ (H : RetainedCoreHistory.{u}) (parameters : Fin H.eventCount → CutoffParameters)
    (records : ∀ i, GeometricCutoffRecord H.toHistory i (parameters i)) (θ : ℝ),
    ∃ T : ℝ, H.horizon < T ∧ 0 < T ∧
      ∀ (J : RetainedCoreHistory.{u}) (I : RawInitialPrefix H J) (t : ℝ), T ≤ t →
      ∀ (i : Fin H.eventCount)
        (b' : (J.toHistory.event (i.castLE I.count_le)).RetainedBoundaryIndex),
        θ * (((I.transportRecord (records i)).static b').neck.scale)⁻¹ <
          t - J.time (i.castLE I.count_le).succ :=
  @_root_.GC.GeneralFlow.exists_uniform_expiry_of_original_fine_prefix
#guard_msgs (drop warning) in
example :
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (step : ∀ n, RawInitialPrefix (F.tower.history n) (F.tower.history (n + 1)))
    (m n : ℕ) (hmn : m ≤ n),
                              RawInitialPrefix (F.tower.history m) (F.tower.history n) :=
  @_root_.GC.GeneralFlow.rawPrefixOfLE
end GC.GeneralFlow
end

-- RF.Surgery.LGeometry.Action.DistinctPoleBirthWeightedMinimumPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
#guard_msgs (drop warning) in
example :
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ z, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ z)
    (hscalar : ∀ z, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) z)
    (aSeed t : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (p x : (H.stageAt t).Carrier) (r rho A : ℝ)
    (hr : 0 < r) (hA : 1 ≤ A)
    (hSeedClock : (aSeed : ℝ) = (t : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (hPoleTest : H.isParabolicallyRmControlledBall t x rho)
    (hrecent : 2 * r ^ 2 < (t : ℝ))
    (i : Fin H.eventCount) (hactive : H.activeStage t = i.succ)
    (hbirth : (t : ℝ) = H.time i.succ)
    {Dcap εcap : ℝ} {mcap : ℕ}
    (S : ∀ b : (H.event i).RetainedBoundaryIndex,
      (H.event i).PresentedStaticCap parameters.fixed Dcap mcap εcap b)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow)
    (hε : εcap ≤ 1 / 2) (hD : StandardCap.transitionEnd + 10 < Dcap)
    (Oold xold : (H.event i).old)
    (hO : HEq ((H.event i).oldOutput Oold) p)
    (hx : HEq ((H.event i).oldOutput xold) x)
    (hOoutside : ∀ b, (H.event i).oldOutput Oold ∉ (S b).window ''
      {z : standardCapWindow Dcap | ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    (hxoutside : ∀ b, (H.event i).oldOutput xold ∉ (S b).window ''
      {z : standardCapWindow Dcap | ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    (hdist : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x <
      ENNReal.ofReal (A * r)),
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    (∃ e : ℝ, 0 < e ∧ e ≤ r / 4 ∧ e ≤ rho / 2 ∧
      e ^ 2 < (t : ℝ) - H.time i.castSucc ∧ 6 * e ^ 3 / rho ^ 2 ≤ r / 4 ∧
      ∀ v : ℝ, 0 < v → v < e →
        ∃ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - v ^ 2 ∧
          H.activeStage a = i.castSucc ∧
          let first := H.activeStage a
          let last := H.activeStage t
          let hle := H.activeStage_mono hat
          let O := seedTrace.point first (H.activeStage_mono has) hle
          ∃ poleTrace : BackwardPointTrace H first last hle x,
            poleTrace.isRmControlled (hat := hat) rho ∧
            let y := poleTrace.point first le_rfl hle
            riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O y <
              ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2))) ∧
            ∃ action : ℝ,
              action ∈ H.regularizedC1ActionValues first last hle t 0 v x y ∧
              (action : WithTop ℝ) ∈ H.regularizedActionValues first last hle t (3 / a₀) 0 v x y ∧
              H.regularizedCost first last hle t (3 / a₀) 0 v x y ≤ (action : WithTop ℝ) ∧
              action ≤ 6 * v ^ 3 / rho ^ 2 ∧
              ∃ (q : (H.stage first).Carrier) (L m : ℝ),
                H.regularizedCost first last hle t (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
                riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O q <
                  ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 12)) ∧
                L ≤ action ∧ 3 * r / 4 ≤ L + r ∧
                H.physicalWeightedCost first last hle t (3 / a₀) r A v x O q = (m : WithTop ℝ) ∧
                M v = (m : WithTop ℝ) ∧ 0 < m ∧
                2 * r - 4 * v ^ 3 / r ^ 2 ≤ m / v ∧
                m / v ≤ 2 * r + 12 * v ^ 3 / rho ^ 2 ∧
                ∀ z : (H.stage first).Carrier,
                  H.physicalWeightedCost first last hle t (3 / a₀) r A v x O q ≤
                    H.physicalWeightedCost first last hle t (3 / a₀) r A v x O z) ∧
    (∀ᶠ v in 𝓝[>] (0 : ℝ), M v ≠ ⊤) ∧
    Tendsto (fun v : ℝ => (M v).untopD 0 / v) (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_distinct_pole_initial_weighted_minimum_and_limit_at_birth
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

-- RF.Surgery.LGeometry.Action.EventWeightedContinuationPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
#guard_msgs (drop warning) in
example :
    ∀ (H : ObservedHistory.{u})
    (i : Fin H.eventCount) (last : Fin (H.eventCount + 1)) (hl : i.succ ≤ last)
    {T B r A k b C : ℝ}
    (hr : 0 < r) (hk : 0 < k) (hkb : k < b)
    (hevent : T - k ^ 2 = H.time i.succ)
    (hupper : T ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval i.castSucc last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val)
        (H.regularizedStageEnd T b j.val),
      ∀ x : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ c : (H.event i).RetainedBoundaryIndex,
      (H.event i).PresentedStaticCap fixed D m ε c)
    (hOld : (H.event i).old = (H.event i).transition.trace.retainedCore)
    (hcanonical : ∀ c, (S c).hasCanonicalWindow)
    (hε : ε ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < D)
    (O z : (H.event i).old)
    (hO : ∀ c, (H.event i).oldOutput O ∉ (S c).window ''
      {x : standardCapWindow D | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (hz : ∀ c, (H.event i).oldOutput z ∉ (S c).window ''
      {x : standardCapWindow D | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (hinside : riemannianEDistOf (H.event i).outputMetric
        ((H.event i).oldOutput O) ((H.event i).oldOutput z) <
      ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)))
    (hcost : H.regularizedCost i.succ last hl T B 0 k p
      ((H.event i).oldOutput z) = (C : WithTop ℝ))
    (hpositive : 0 < 2 * k * C + 2 * r * k),
    ∀ η : ℝ, 0 < η → ∃ d : ℝ, k < d ∧ d ≤ b ∧
      ∀ v ∈ Ioo k d,
        H.physicalWeightedCost i.castSucc last (i.castSucc_le_succ.trans hl)
            T B r A v p O.val.val z.val.val <
          H.physicalWeightedCost i.succ last hl T B r A k p
            ((H.event i).oldOutput O) ((H.event i).oldOutput z) + (η : WithTop ℝ) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_physicalWeightedCost_lt_after_event_of_outside_canonical_cap_windows
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end

-- RF.Surgery.LGeometry.Action.EventWindowEndpointPair  [VERBATIM, REG]
-- (no public user declarations)

-- RF.Surgery.LGeometry.Action.IncomingEventWeightedMinimumPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
#guard_msgs (drop warning) in
example :
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (a₀ : ℝ) (ha₀ : 0 < a₀)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
    (r A k : ℝ) (hr : 0 < r) (hk : 0 < k)
    (hhalf : k ^ 2 < r ^ 2 / 2) (hT : 2 * r ^ 2 < t.val)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (i : Fin H.eventCount) (hfSeed : H.activeStage aSeed ≤ i.castSucc)
    (hl : i.succ ≤ H.activeStage t)
    (hevent : t.val - k ^ 2 = H.time i.succ)
    {Dcap εcap : ℝ} {ncap : ℕ}
    (S : ∀ c : (H.event i).RetainedBoundaryIndex,
      (H.event i).PresentedStaticCap parameters.fixed Dcap ncap εcap c)
    (hcanonical : ∀ c, (S c).hasCanonicalWindow)
    (hε : εcap ≤ 1 / 2) (hD : StandardCap.transitionEnd + 10 < Dcap)
    (O z : (H.event i).old)
    (hOin : O.val.val = seedTrace.point i.castSucc hfSeed (i.castSucc_le_succ.trans hl))
    (hO : ∀ c, (H.event i).oldOutput O ∉ (S c).window ''
      {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10})
    (hz : ∀ c, (H.event i).oldOutput z ∉ (S c).window ''
      {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10})
    (L : ℝ)
    (hinside : riemannianEDistOf (H.event i).outputMetric
        ((H.event i).oldOutput O) ((H.event i).oldOutput z) <
      ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)))
    (hcost : H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x
      ((H.event i).oldOutput z) = (L : WithTop ℝ))
    (hcontact : H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x
        ((H.event i).oldOutput O) ((H.event i).oldOutput z) =
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A k),
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    let m : ℝ → ℝ := fun v => (M v).untopD 0
    M k ≠ ⊤ ∧ 0 < m k ∧
    (∀ η : ℝ, 0 < η → ∃ d : ℝ, k < d ∧ d ^ 2 < r ^ 2 / 2 ∧
      ∀ v ∈ Ioo k d,
        t.val - v ^ 2 ∈ Ioo (H.time i.castSucc) (H.time i.succ) ∧
        BddBelow (Set.range (H.physicalWeightedCost i.castSucc (H.activeStage t)
          (i.castSucc_le_succ.trans hl) t.val (3 / a₀) r A v x O.val.val)) ∧
        M v = sInf (Set.range (H.physicalWeightedCost i.castSucc (H.activeStage t)
          (i.castSucc_le_succ.trans hl) t.val (3 / a₀) r A v x O.val.val)) ∧
        M v ≠ ⊤ ∧ 0 ≤ m v ∧ M v < M k + (η : WithTop ℝ) ∧ m v < m k + η) ∧
    ∀ C : ℝ,
      UpperSemicontinuousWithinAt
        (fun v : ℝ => Real.exp (-C * v ^ 2 / r ^ 2 - 32 * v / r) * m v / v)
        (Ici k) k :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.traced_physical_weighted_minimum_right_control_of_event_window_data
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

-- RF.Surgery.LGeometry.Action.NonnegativeEventWindowEndpointPair  [VERBATIM, REG]
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_old_seed_and_endpoint_outside_retained_cap_windows_of_nonneg_clock :=
  @exists_old_seed_and_endpoint_outside_retained_cap_windows_of_nonneg_clock
end

-- RF.Surgery.LGeometry.Action.PhysicalWeightedLocalizedBarrierPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @weighted_physical_history_support_heat_lower_at_minimum :=
  @weighted_physical_history_support_heat_lower_at_minimum
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

-- RF.Surgery.LGeometry.Action.PhysicalWeightedSupportBranchesPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_weighted_physical_history_support_of_seed_ricci_of_shifted_pos :=
  @exists_weighted_physical_history_support_of_seed_ricci_of_shifted_pos
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_weighted_physical_history_support_of_seed_ricci :=
  @exists_weighted_physical_history_support_of_seed_ricci
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_weighted_physical_history_support_on_half_seed_clock :=
  @exists_weighted_physical_history_support_on_half_seed_clock
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

-- RF.Surgery.LGeometry.Action.SmoothCollarGeometryPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval
universe u uP
#guard_msgs (drop warning) in
example :
    ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Ioc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j,
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount)
      (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    (hC1Atv : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel 1
      (gamma ⟨first, le_rfl, hle⟩) v)
    (hcross : ∀ (i : Fin H.eventCount)
      (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))),
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : J := ⟨first, le_rfl, hle⟩;
    let jl : J := ⟨last, hle, le_rfl⟩;
    let N := last.val - first.val;
    ∃ (DT : RealTimeInterval)
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (b lowT highT : ℝ) (alphaT : ℝ → (H.stage first).Carrier),
      IsSolutionOn ST ∧
      (∀ t, ST.base.metric t = H.stageMetric first t) ∧
      0 < b ∧ b < v ∧
      (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2 < b ∧
      lowT < b ∧ v < highT ∧
      (∀ r ∈ Ioo lowT highT, T - r ^ 2 ∈ DT.regular) ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ alphaT ∧
      IsLRegularizedGeodesicOn ST T alphaT (Icc b v) ∧
      EqOn alphaT (gamma jf) (Icc b v) ∧
      alphaT =ᶠ[𝓝 b] gamma jf ∧
      alphaT v = gamma jf v ∧
      lVelocity (I := ThreeModel) alphaT v =
        lVelocity (I := ThreeModel) (gamma jf) v ∧
      lRegularizedAction ST T alphaT b v =
        H.stageRegularizedAction first T (gamma jf) b v ∧
      ∃ (C D : E → ℝ) (hCs : ∀ i, C i < H.time i.val.succ)
        (hsD : ∀ i, H.time i.val.succ < D i)
        (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
        (FC : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
          (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
        (SS : (i : E) → SolutionOn (I := ThreeModel) (M := W i)
          (RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le))
        (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞
          (fun z : W i => z.val.val))
        (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞
          (fun z : W i => FC i z.val))
        (c0 d0 : E → ℝ) (eta : (i : E) → ℝ → W i),
        (∀ i,
          0 < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < v ∧
          H.time i.val.castSucc < C i ∧ D i < H.stageEndTime i.val.succ ∧
          (FC i).source = W i ∧ IsSolutionOn (SS i) ∧
          (∀ z : W i, (H.event i.val).RegularCrossing z.val.val (FC i z.val)) ∧
          (∀ t ∈ Ico (C i) (H.time i.val.succ), (SS i).base.metric t =
            localPullMetric (H.stageMetric i.val.castSucc t)
              (fun z : W i => z.val.val) (hold i)) ∧
          (∀ t ∈ Icc (H.time i.val.succ) (D i), (SS i).base.metric t =
            localPullMetric (H.stageMetric i.val.succ t)
              (fun z : W i => FC i z.val) (hnew i)) ∧
          (SS i).base.metric (H.time i.val.succ) =
            (H.event i.val).terminal.metric.restrictOpen (W i) ∧
          0 < c0 i ∧ c0 i < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < d0 i ∧ d0 i < v ∧
          H.regularizedStageStart T 0 i.val.succ < c0 i ∧
          d0 i < H.regularizedStageEnd T v i.val.castSucc ∧
          (∀ r ∈ Icc (c0 i) (d0 i), T - r ^ 2 ∈ Ioo (C i) (D i)) ∧
          Manifold.absolutelyContinuousOnInterval ThreeModel (eta i) (c0 i) (d0 i) ∧
          ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (eta i) (Icc (c0 i) (d0 i)) ∧
          IsLRegularizedGeodesicOn (SS i) T (eta i) (Ioo (c0 i) (d0 i)) ∧
          EqOn ((fun z : W i => FC i z.val) ∘ eta i) (gamma (jn i))
            (Icc (c0 i) (Real.sqrt (T - H.time i.val.succ))) ∧
          EqOn ((fun z : W i => z.val.val) ∘ eta i) (gamma (jo i))
            (Icc (Real.sqrt (T - H.time i.val.succ)) (d0 i)) ∧
          IntervalIntegrable (lRegularizedLagrangian (SS i) T (eta i))
            volume (c0 i) (d0 i) ∧
          lRegularizedAction (SS i) T (eta i) (c0 i) (d0 i) =
            H.stageRegularizedAction i.val.succ T (gamma (jn i)) (c0 i)
              (Real.sqrt (T - H.time i.val.succ)) +
            H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
              (Real.sqrt (T - H.time i.val.succ)) (d0 i)) ∧
        ∃ (j : Fin (N + 1) ≃ J) (e : Fin N ≃ E)
          (c d : E → ℝ) (a0 : ℝ),
          j 0 = jl ∧ j (Fin.last N) = jf ∧
          (∀ k, j k.castSucc = jn (e k) ∧ j k.succ = jo (e k)) ∧
          0 < a0 ∧ a0 < b ∧
          (∀ i, a0 < c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
            Real.sqrt (T - H.time i.val.succ) < d i ∧ d i < b ∧
            Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i)) ∧
          H.regularizedStageStart T 0 last = 0 ∧
          H.regularizedStageEnd T v first = v ∧
          (∀ x : J, H.regularizedStageStart T 0 x.val <
            H.regularizedStageEnd T v x.val) ∧
          ∃ (lowS highS : E → ℝ) (alphaS : (i : E) → ℝ → W i),
      ((∀ i, lowS i < c i ∧ d i < highS i) ∧
      (∀ i, ∀ r ∈ Ioo (lowS i) (highS i),
        T - r ^ 2 ∈ (RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le).regular) ∧
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alphaS i)) ∧
      (∀ i, ∀ r ∈ Icc (c i) (d i), alphaS i =ᶠ[𝓝 r] eta i) ∧
      (∀ i, IsLRegularizedGeodesicOn (SS i) T (alphaS i) (Icc (c i) (d i))) ∧
      (∀ i, EqOn ((fun z : W i => FC i z.val) ∘ alphaS i) (gamma (jn i))
        (Icc (c i) (Real.sqrt (T - H.time i.val.succ)))) ∧
      (∀ i, EqOn ((fun z : W i => z.val.val) ∘ alphaS i) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (d i))) ∧
      (∀ i, ((fun z : W i => FC i z.val) ∘ alphaS i) =ᶠ[𝓝 (c i)] gamma (jn i)) ∧
      (∀ i, ((fun z : W i => z.val.val) ∘ alphaS i) =ᶠ[𝓝 (d i)] gamma (jo i)) ∧
      (∀ i, EqOn (lRegularizedLagrangian (SS i) T (alphaS i))
        (lRegularizedLagrangian (SS i) T (eta i)) (Icc (c i) (d i))) ∧
      (∀ i, IntervalIntegrable (lRegularizedLagrangian (SS i) T (alphaS i)) volume (c i) (d i)) ∧
      (∀ i, lRegularizedAction (SS i) T (alphaS i) (c i) (d i) =
        H.stageRegularizedAction i.val.succ T (gamma (jn i)) (c i)
          (Real.sqrt (T - H.time i.val.succ)) +
        H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
          (Real.sqrt (T - H.time i.val.succ)) (d i)) ∧
      (∀ i (weight : ℝ → ℝ), ContinuousOn weight (Icc (c i) (d i)) →
        IntervalIntegrable (fun r => weight r * lRegularizedLagrangian (SS i) T (alphaS i) r)
          volume (c i) (d i) ∧
        IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.val.succ T
          (gamma (jn i)) r) volume (c i) (Real.sqrt (T - H.time i.val.succ)) ∧
        IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.val.castSucc T
          (gamma (jo i)) r) volume (Real.sqrt (T - H.time i.val.succ)) (d i) ∧
        (∫ r in (c i)..(d i), weight r * lRegularizedLagrangian (SS i) T (alphaS i) r) =
          (∫ r in (c i)..Real.sqrt (T - H.time i.val.succ), weight r *
            H.stageRegularizedLagrangian i.val.succ T (gamma (jn i)) r) +
          ∫ r in Real.sqrt (T - H.time i.val.succ)..(d i), weight r *
            H.stageRegularizedLagrangian i.val.castSucc T (gamma (jo i)) r)) ∧
          ∀ a ∈ Ioo 0 a0,
            ∃ (lo hi : J → ℝ) (s : Fin (2 * N + 3) → ℝ),
              StrictMono s ∧ s 0 = a ∧ s (Fin.last (2 * N + 2)) = v ∧
              s ⟨2 * N + 1, by omega⟩ = b ∧
              (∀ k, s ⟨2 * k.val, by omega⟩ = lo (j k) ∧
                s ⟨2 * k.val + 1, by omega⟩ = hi (j k)) ∧
              (∀ k, s ⟨2 * k.val + 1, by omega⟩ = c (e k) ∧
                s ⟨2 * k.val + 2, by omega⟩ = d (e k)) ∧
              lo jl = a ∧ hi jf = b ∧
              (∀ i, hi (jn i) = c i ∧ lo (jo i) = d i) ∧
              (∀ x : J, H.regularizedStageStart T 0 x.val < lo x ∧ lo x < hi x ∧
                hi x < H.regularizedStageEnd T v x.val) ∧
              T - a ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) ∧
              (∀ x : J, H.regularizedStageStart T a x.val ≤ lo x ∧ lo x ≤ hi x ∧
                hi x ≤ H.regularizedStageEnd T v x.val) ∧
              Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 a ∧
              ∃ (DO : J → RealTimeInterval)
      (SO : (x : J) → SolutionOn (I := ThreeModel) (M := (H.stage x.val).Carrier) (DO x))
      (alphaO : (x : J) → ℝ → (H.stage x.val).Carrier) (lowO highO : J → ℝ),
      ((∀ x, IsSolutionOn (SO x)) ∧
      (∀ x t, (SO x).base.metric t = H.stageMetric x.val t) ∧
      (∀ x, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alphaO x)) ∧
      (∀ x, ∀ r ∈ Icc (lo x) (hi x), alphaO x =ᶠ[𝓝 r] gamma x) ∧
      (∀ x, EqOn (alphaO x) (gamma x) (Icc (lo x) (hi x))) ∧
      (∀ x, IsLRegularizedGeodesicOn (SO x) T (alphaO x) (Icc (lo x) (hi x))) ∧
      (∀ x, lowO x < lo x ∧ hi x < highO x) ∧
      (∀ x, ∀ r ∈ Ioo (lowO x) (highO x), T - r ^ 2 ∈ (DO x).regular) ∧
      (∀ x, EqOn (lRegularizedLagrangian (SO x) T (alphaO x))
        (H.stageRegularizedLagrangian x.val T (gamma x)) (Icc (lo x) (hi x))) ∧
      (∀ x, lRegularizedAction (SO x) T (alphaO x) (lo x) (hi x) =
        H.stageRegularizedAction x.val T (gamma x) (lo x) (hi x)) ∧
      (∀ x (weight : ℝ → ℝ),
        (∫ r in (lo x)..(hi x), weight r * lRegularizedLagrangian (SO x) T (alphaO x) r) =
          ∫ r in (lo x)..(hi x), weight r * H.stageRegularizedLagrangian x.val T (gamma x) r)) ∧
    let DS : E → RealTimeInterval := fun i =>
      RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le;
    let Tag := Fin (N + 1) ⊕ (Fin N ⊕ Fin 1);
    let M0 : Tag → Type u := ActualPieceCarrier H first last j e (fun k => W (e k));
    let D0 : Tag → RealTimeInterval := Sum.elim (fun k => DO (j k))
      (Sum.elim (fun k => DS (e k)) (fun _ => DT));
    let S0 : (k : Tag) → SolutionOn (I := ThreeModel) (M := M0 k) (D0 k) :=
      Sum.rec (fun k => SO (j k)) (Sum.rec (fun k => SS (e k)) (fun _ => ST));
    let alpha0 : (k : Tag) → ℝ → M0 k :=
      Sum.rec (fun k => alphaO (j k)) (Sum.rec (fun k => alphaS (e k)) (fun _ => alphaT));
    let Q := interleavedPieceEquiv N;
    let M : Fin (2 * N + 2) → Type u := fun i => M0 (Q.symm i);
    let Dpiece : Fin (2 * N + 2) → RealTimeInterval := fun i => D0 (Q.symm i);
    let S : (i : Fin (2 * N + 2)) → SolutionOn (I := ThreeModel) (M := M i) (Dpiece i) :=
      fun i => S0 (Q.symm i);
    let alpha : (i : Fin (2 * N + 2)) → ℝ → M i := fun i => alpha0 (Q.symm i);
    let lowFlat : Fin (2 * N + 2) → ℝ := fun i =>
      Sum.elim (fun k => lowO (j k))
        (Sum.elim (fun k => lowS (e k)) (fun _ => lowT)) (Q.symm i);
    let highFlat : Fin (2 * N + 2) → ℝ := fun i =>
      Sum.elim (fun k => highO (j k))
        (Sum.elim (fun k => highS (e k)) (fun _ => highT)) (Q.symm i);
      (∀ i, IsSolutionOn (S i)) ∧
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alpha i)) ∧
      (∀ i, lowFlat i < s i.castSucc ∧ s i.succ < highFlat i) ∧
      (∀ i r, r ∈ Ioo (lowFlat i) (highFlat i) → T - r ^ 2 ∈ (Dpiece i).regular) ∧
      (∀ i, IsLRegularizedGeodesicOn (S i) T (alpha i) (Icc (s i.castSucc) (s i.succ))) ∧
    ∃ Phi : (i : Fin (2 * N + 1)) →
      PartialDiffeomorph ThreeModel ThreeModel (M i.castSucc) (M i.succ) ∞,
      (∀ i : Fin (2 * N + 1),
        let r := s i.castSucc.succ;
        alpha i.castSucc r ∈ (Phi i).source ∧
        Phi i (alpha i.castSucc r) = alpha i.succ r ∧
        (Phi i : M i.castSucc → M i.succ) ∘ alpha i.castSucc =ᶠ[𝓝 r] alpha i.succ ∧
        (∀ x ∈ (Phi i).source, ∀ V W : TangentSpace ThreeModel x,
          ((S i.castSucc).base.metric (T - r ^ 2)).inner x V W =
            ((S i.succ).base.metric (T - r ^ 2)).inner (Phi i x)
              (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ) x V)
              (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ) x W)) ∧
        (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ)
          (alpha i.castSucc r) (lVelocity (I := ThreeModel) (alpha i.castSucc) r) : ThreeSpace) =
            lVelocity (I := ThreeModel) (alpha i.succ) r ∧
        (S i.castSucc).scalar (T - r ^ 2) (alpha i.castSucc r) =
          (S i.succ).scalar (T - r ^ 2) (alpha i.succ r) ∧
        lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) r =
          lRegularizedLagrangian (S i.succ) T (alpha i.succ) r) ∧
      ∀ (P : Type uP) (f : (i : Fin (2 * N + 2)) → P × ℝ → M i),
    let g := (Equiv.piCongrLeft' (fun k => P × ℝ → M0 k) Q).symm f;
    let ordinary : (x : J) → P × ℝ → (H.stage x.val).Carrier :=
      (Equiv.piCongrLeft' (fun x : J => P × ℝ → (H.stage x.val).Carrier) j.symm).symm
        (fun k => g (.inl k));
    let survivor : (i : E) → P × ℝ → W i :=
      (Equiv.piCongrLeft' (fun i : E => P × ℝ → W i) e.symm).symm
        (fun k => g (.inr (.inl k)));
    let tail : P × ℝ → (H.stage first).Carrier := g (.inr (.inr 0));
      ∀ z : P,
        (∀ i : Fin (2 * N + 1),
          f i.castSucc (z, s i.castSucc.succ) ∈ (Phi i).source ∧
          Phi i (f i.castSucc (z, s i.castSucc.succ)) =
            f i.succ (z, s i.succ.castSucc)) →
        (∀ i, ordinary (jn i) (z, hi (jn i)) = FC i (survivor i (z, hi (jn i))).val) ∧
        (∀ i, ordinary (jo i) (z, lo (jo i)) = (survivor i (z, lo (jo i))).val.val) ∧
        ordinary jf (z, hi jf) = tail (z, hi jf) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_smooth_physical_collar_geometry_of_attained_action
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

-- RF.Surgery.LGeometry.Action.SmoothCollarSupportJetsPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
open Bundle Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval
universe u uP uTag
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
#guard_msgs (drop warning) in
example :
    ∀ {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Ioc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) (Bfloor : ℝ)
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -Bfloor ≤ metricScalarAt (H.stageMetric j t) x),
    let Jstage := H.StageInterval first last;
    let Eevent := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : Eevent) : Jstage := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : Eevent) : Jstage := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : Jstage := ⟨first, le_rfl, hle⟩;
    let jl : Jstage := ⟨last, hle, le_rfl⟩;
    ∀ (gamma : (j : Jstage) → ℝ → (H.stage j.val).Carrier) (lo hi : Jstage → ℝ),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      hi jf < v →
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 (lo jl) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
      H.regularizedExtendedAction first last T Bfloor 0 v gamma =
        H.regularizedCost first last hle T Bfloor 0 v (gamma jl 0) (gamma jf v) →
    ∀ (W : (i : Eevent) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (FC : (i : Eevent) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (DO : Jstage → RealTimeInterval) (DS : Eevent → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (j : Jstage) → SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) (DO j))
      (SS : (i : Eevent) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => FC i z.val))
      {N : ℕ} (j : Fin (N + 1) ≃ Jstage) (e : Fin N ≃ Eevent)
      (s : Fin (2 * N + 3) → ℝ) (hs : StrictMono s)
      (hslo : ∀ k, s (interleavedPieceEquiv N (.inl k)).castSucc = lo (j k))
      (hshi : ∀ k, s (interleavedPieceEquiv N (.inl k)).succ = hi (j k))
      (hsnew : ∀ k, s (interleavedPieceEquiv N (.inr (.inl k))).castSucc = hi (jn (e k)))
      (hsold : ∀ k, s (interleavedPieceEquiv N (.inr (.inl k))).succ = lo (jo (e k)))
      (hstail : s (Fin.last (2 * N + 1)).castSucc = hi jf)
      (hsv : s (Fin.last (2 * N + 2)) = v)
      (alphaO : (x : Jstage) → ℝ → (H.stage x.val).Carrier)
      (alphaS : (i : Eevent) → ℝ → W i) (alphaT : ℝ → (H.stage first).Carrier),
    let Tag := Fin (N + 1) ⊕ (Fin N ⊕ Fin 1);
    let M0 : Tag → Type u := ActualPieceCarrier H first last j e (fun k => W (e k));
    let D0 : Tag → RealTimeInterval := Sum.elim (fun k => DO (j k))
      (Sum.elim (fun k => DS (e k)) (fun _ => DT));
    let S0 : (k : Tag) → SolutionOn (I := ThreeModel) (M := M0 k) (D0 k) :=
      Sum.rec (fun k => SO (j k)) (Sum.rec (fun k => SS (e k)) (fun _ => ST));
    let alpha0 : (k : Tag) → ℝ → M0 k :=
      Sum.rec (fun k => alphaO (j k)) (Sum.rec (fun k => alphaS (e k)) (fun _ => alphaT));
    let Q := interleavedPieceEquiv N;
    let M : Fin (2 * N + 2) → Type u := fun i => M0 (Q.symm i);
    let D : Fin (2 * N + 2) → RealTimeInterval := fun i => D0 (Q.symm i);
    let S : (i : Fin (2 * N + 2)) → SolutionOn (I := ThreeModel) (M := M i) (D i) :=
      fun i => S0 (Q.symm i);
    let alpha : (i : Fin (2 * N + 2)) → ℝ → M i := fun i => alpha0 (Q.symm i);
    let a : Fin (2 * N + 2) → ℝ := fun i => s i.castSucc;
    let b : Fin (2 * N + 2) → ℝ := fun i => s i.succ;
    ∀ (f : (i : Fin (2 * N + 2)) → P × ℝ → M i)
      (hf : ∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 (f i))
      (hgeoO : ∀ x, IsLRegularizedGeodesicOn (SO x) T (alphaO x) (Icc (lo x) (hi x)))
      (hgeoS : ∀ i, IsLRegularizedGeodesicOn (SS i) T (alphaS i) (Icc (hi (jn i)) (lo (jo i))))
      (hgeoT : IsLRegularizedGeodesicOn ST T alphaT (Icc (hi jf) v))
      (hcenter : ∀ i r, r ∈ Icc (a i) (b i) → (fun t => f i (0, t)) =ᶠ[𝓝 r] alpha i)
      (Phi : (i : Fin (2 * N + 1)) →
        PartialDiffeomorph ThreeModel ThreeModel (M i.castSucc) (M i.succ) ∞)
      (hmetric : ∀ (i : Fin (2 * N + 1)) (x : M i.castSucc), x ∈ (Phi i).source →
        ∀ V W : TangentSpace ThreeModel x,
        ((S i.castSucc).base.metric (T - (b i.castSucc) ^ 2)).inner x V W =
          ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner (Phi i x)
            (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ) x V)
            (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ) x W))
      (hjoin : ∀ z i, f i.castSucc (z, b i.castSucc) ∈ (Phi i).source ∧
        Phi i (f i.castSucc (z, b i.castSucc)) = f i.succ (z, a i.succ))
      (hvelocity : ∀ i : Fin (2 * N + 1),
        (mfderiv ThreeModel ThreeModel (Phi i : M i.castSucc → M i.succ)
          (alpha i.castSucc (b i.castSucc))
          (lVelocity (I := ThreeModel) (alpha i.castSucc) (b i.castSucc)) : ThreeSpace) =
            lVelocity (I := ThreeModel) (alpha i.succ) (a i.succ))
      (hfirst : ∀ z, f 0 (z, a 0) = alpha 0 (a 0)),
    let g := (Equiv.piCongrLeft' (fun k => P × ℝ → M0 k) Q).symm f;
    let ordinary : (x : Jstage) → P × ℝ → (H.stage x.val).Carrier :=
      (Equiv.piCongrLeft' (fun x : Jstage => P × ℝ → (H.stage x.val).Carrier) j.symm).symm
        (fun k => g (.inl k));
    let survivor : (i : Eevent) → P × ℝ → W i :=
      (Equiv.piCongrLeft' (fun i : Eevent => P × ℝ → W i) e.symm).symm
        (fun k => g (.inr (.inl k)));
    let tail : P × ℝ → (H.stage first).Carrier := g (.inr (.inr 0));
      (∀ j, IsSolutionOn (SO j)) → (∀ i, IsSolutionOn (SS i)) → IsSolutionOn ST →
      (∀ j t, (SO j).base.metric t = H.stageMetric j.val t) →
      (∀ t, ST.base.metric t = H.stageMetric first t) →
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (FC i z.val)) →
      (∀ i, ∀ r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.castSucc (T - r ^ 2))
            (fun z : W i => z.val.val) (hold i)) →
      (∀ i, ∀ r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.succ (T - r ^ 2))
            (fun z : W i => FC i z.val) (hnew i)) →
    ∀ (V : Set P), IsOpen V → (0 : P) ∈ V →
    ∀ (KO : Jstage → Set ℝ) (KS : Eevent → Set ℝ) (KT : Set ℝ),
      (∀ j, IsOpen (KO j) ∧ IsPreconnected (KO j) ∧ lo j ∈ KO j ∧ hi j ∈ KO j) →
      (∀ i, IsOpen (KS i) ∧ IsPreconnected (KS i) ∧ hi (jn i) ∈ KS i ∧ lo (jo i) ∈ KS i) →
      IsOpen KT ∧ IsPreconnected KT ∧ hi jf ∈ KT ∧ v ∈ KT →
      (∀ j r, r ∈ KO j → T - r ^ 2 ∈ (DO j).regular) →
      (∀ i r, r ∈ KS i → T - r ^ 2 ∈ (DS i).regular) →
      (∀ r ∈ KT, T - r ^ 2 ∈ DT.regular) →
      (∀ z ∈ V, ordinary jl (z, lo jl) = gamma jl (lo jl)) →
      (∀ z ∈ V, ∀ i, ordinary (jo i) (z, lo (jo i)) =
        (survivor i (z, lo (jo i))).val.val) →
      (∀ z ∈ V, ∀ i, ordinary (jn i) (z, hi (jn i)) =
        FC i (survivor i (z, hi (jn i))).val) →
      (∀ z ∈ V, ordinary jf (z, hi jf) = tail (z, hi jf)) →
      (∀ j, EqOn (fun r => ordinary j (0, r)) (gamma j) (Icc (lo j) (hi j))) →
      (∀ i, EqOn (fun r => (survivor i (0, r)).val.val) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) →
      (∀ i, EqOn (fun r => FC i (survivor i (0, r)).val) (gamma (jn i))
        (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)))) →
      EqOn (fun r => tail (0, r)) (gamma jf) (Icc (hi jf) v) →
    ∀ (Bframe : P ≃L[ℝ] ThreeSpace),
      (fun z => tail (z, v)) =ᶠ[𝓝 (0 : P)]
        (fun z => expMap (ST.base.metric (T - v ^ 2)) (gamma jf v)
          (show TangentSpace ThreeModel (gamma jf v) from Bframe z)) →
    ∀ {Idx : Type*} [Fintype Idx] [DecidableEq Idx] (basis : Module.Basis Idx ℝ P),
      (∀ i j, (ST.base.metric (T - v ^ 2)).inner (gamma jf v)
        (show TangentSpace ThreeModel (gamma jf v) from Bframe (basis i))
        (show TangentSpace ThreeModel (gamma jf v) from Bframe (basis j)) =
          if i = j then 1 else 0) →
    let action : P × ℝ → ℝ := fun z =>
      H.stageRegularizedAction last T (gamma jl) 0 (lo jl) +
      (∑ j : Jstage, lRegularizedAction (SO j) T (fun r => ordinary j (z.1, r)) (lo j) (hi j)) +
      (∑ i : Eevent, lRegularizedAction (SS i) T (fun r => survivor i (z.1, r))
        (hi (jn i)) (lo (jo i))) +
      lRegularizedAction ST T (fun r => tail (z.1, r)) (hi jf) z.2;
    ∃ (Jclock : Set ℝ) (U : Set ((H.stage first).Carrier × ℝ))
      (psi : (H.stage first).Carrier × ℝ → P) (F : (H.stage first).Carrier × ℝ → ℝ),
      (IsOpen Jclock ∧ v ∈ Jclock ∧ Jclock ⊆ KT ∧
      (∀ w ∈ Jclock, 0 < w ∧ hi jf < w ∧ T - w ^ 2 ∈ H.stageDomain first) ∧
      ContDiffOn ℝ 2 action (V ×ˢ KT) ∧
      IsOpen U ∧ (gamma jf v, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2 psi U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      psi (gamma jf v, v) = 0 ∧
      F (gamma jf v, v) = ∑ j : Jstage, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) ∧
      H.regularizedCost first last hle T Bfloor 0 v (gamma jl 0) (gamma jf v) =
        (F (gamma jf v, v) : WithTop ℝ) ∧
      ∀ x ∈ U, psi x ∈ V ∧ x.2 ∈ Jclock ∧
        tail (psi x, x.2) = x.1 ∧ F x = action (psi x, x.2) ∧
        H.regularizedCost first last hle T Bfloor 0 x.2 (gamma jl 0) x.1 ≤
          (F x : WithTop ℝ)) ∧
      (∀ z w, action (z, w) =
        H.stageRegularizedAction last T (gamma jl) 0 (lo jl) +
          finiteJointAction S T f a b (z, w)) ∧
    let gphys := ST.base.metric (T - v ^ 2)
    let q := gamma jf v
    let velocity : TangentSpace ThreeModel q :=
      show ThreeSpace from lVelocity (I := ThreeModel) (fun r => tail (0, r)) v
    let clock := 2 * v ^ 2 * ST.scalar (T - v ^ 2) q -
      (1 / 2 : ℝ) * gphys.inner q velocity velocity
    HasMFDerivAt (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) F (q, v)
      ((gphys.inner q velocity).comp (ContinuousLinearMap.fst ℝ ThreeSpace ℝ) +
        clock • ContinuousLinearMap.snd ℝ ThreeSpace ℝ) ∧
    gradientFun gphys (fun y => F (y, v)) q = velocity ∧
    HasDerivAt (fun w => F (q, w)) clock v ∧
    (∀ ξ : P, abstractHessian gphys (fun y => F (y, v)) q
      (show TangentSpace ThreeModel q from Bframe ξ) (show TangentSpace ThreeModel q from Bframe
        ξ) =
        2 * ∑ i : Fin (2 * N + 2), lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • ξ, r)) 0)
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • ξ, r)) 0) (a i) (b i)) ∧
    laplacian (LeviCivita gphys) gphys (fun y => F (y, v)) q =
      2 * ∑ i : Fin (2 * N + 2), ∑ k : Idx,
        lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0)
          (fun r => lVelocity (I := ThreeModel) (fun u => f i (u • basis k, r)) 0) (a i) (b i) ∧
    (∀ ξ : P, (fun u : ℝ => F (expMap gphys q (u • (show TangentSpace ThreeModel q from Bframe
      ξ)), v))
      =ᶠ[𝓝 0] (fun u => H.stageRegularizedAction last T (gamma jl) 0 (lo jl) + finiteJointAction S
        T f a b (u • ξ, v))) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_smooth_collar_cost_support_with_jets
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
#guard_msgs (drop warning) in
example :
    ∀ {P : Type uP} [Zero P]
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (gamma alphaT : ℝ → (H.stage first).Carrier)
    (tail : P × ℝ → (H.stage first).Carrier) (v : ℝ)
    (hvelocityT : lVelocity (I := ThreeModel) alphaT v =
      lVelocity (I := ThreeModel) gamma v)
    (hcenter : (fun r => tail (0, r)) =ᶠ[𝓝 v] alphaT),
    lVelocity (I := ThreeModel) (fun r => tail (0, r)) v =
      lVelocity (I := ThreeModel) gamma v :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.smooth_collar_original_velocity_of_terminal_germ
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

-- RF.Surgery.LGeometry.Action.WeightedCollarActionPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval
universe u v
#guard_msgs (drop warning) in
example :
    ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T a v : ℝ} (ha : 0 ≤ a) (hav : a ≤ v)
    (hupper : T - a ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first),
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    ∀ (lo hi : J → ℝ) (gamma : (j : J) → ℝ → (H.stage j.val).Carrier),
      (∀ j, H.regularizedStageStart T a j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      lo ⟨last, hle, le_rfl⟩ = a →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
    ∀ (weight : ℝ → ℝ), ContinuousOn weight (Icc a v) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (FC : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (DS : E → RealTimeInterval)
      (SS : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => FC i z.val))
      (eta : (i : E) → ℝ → W i),
      (∀ i, IsSolutionOn (SS i)) →
      (∀ i, ∀ r ∈ Icc (hi (jn i)) (lo (jo i)), T - r ^ 2 ∈ (DS i).carrier) →
      (∀ i, ∀ r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.castSucc (T - r ^ 2))
            (fun z : W i => z.val.val) (hold i)) →
      (∀ i, ∀ r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.succ (T - r ^ 2))
            (fun z : W i => FC i z.val) (hnew i)) →
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (eta i)) →
      (∀ i, EqOn (fun r => (eta i r).val.val) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) →
      (∀ i, EqOn (fun r => FC i (eta i r).val) (gamma (jn i))
        (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)))) →
    ∀ (DO : J → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (j : J) → SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) (DO j))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (beta : (j : J) → ℝ → (H.stage j.val).Carrier) (tail : ℝ → (H.stage first).Carrier),
      (∀ j, ∀ r ∈ uIoo (lo j) (hi j),
        (SO j).base.metric (T - r ^ 2) = H.stageMetric j.val (T - r ^ 2)) →
      (∀ r ∈ uIoo (hi ⟨first, le_rfl, hle⟩) v,
        ST.base.metric (T - r ^ 2) = H.stageMetric first (T - r ^ 2)) →
      (∀ j, EqOn (beta j) (gamma j) (uIoo (lo j) (hi j))) →
      EqOn tail (gamma ⟨first, le_rfl, hle⟩) (uIoo (hi ⟨first, le_rfl, hle⟩) v) →
      (∑ j : J,
        ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
          weight r * H.stageRegularizedLagrangian j.val T (gamma j) r) =
        (∑ j : J, ∫ r in lo j..hi j,
          weight r * lRegularizedLagrangian (SO j) T (beta j) r) +
        (∑ i : E, ∫ r in hi (jn i)..lo (jo i),
          weight r * lRegularizedLagrangian (SS i) T (eta i) r) +
        (∫ r in hi ⟨first, le_rfl, hle⟩..v,
          weight r * lRegularizedLagrangian ST T tail r) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.sum_weighted_stage_action_eq_smooth_collar_action_of_physical_projections
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

-- RF.Surgery.Noncollapsing.AffineJoinNoncollapsePortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
#guard_msgs (drop warning) in
example :
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    {ρglobal ρtail κH κT : ℝ}
    (hρglobal : 0 < ρglobal) (hρtail : 0 < ρtail)
    (hκH : 0 < κH) (hκT : 0 < κT),
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (H K J : RetainedCoreHistory.{u})
        (I : InitialIdentification P₀ g₀ K.toHistory)
        (c : ℝ) (offset : ℕ)
        (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)),
        (∀ i : Fin K.eventCount, (K.toHistory.event i).incoming.SingularEndpoint) →
        H.toHistory.IsPrefixOf J.toHistory → c ≤ H.horizon →
        J.horizon = K.horizon + c →
        (∀ t : ℝ,
          HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
            (K.toHistory.stageMetric (Fin.last K.eventCount) t)) →
        H.NoncollapsedBefore κH ρglobal H.horizon →
        K.NoncollapsedBefore κT ρtail K.horizon →
        J.NoncollapsedBefore κ ρglobal J.horizon :=
  @_root_.GC.GeneralFlow.exists_noncollapsed_affine_join
end GC.GeneralFlow
end

-- RF.Surgery.Noncollapsing.CommonScaffoldExtensionPortC11P  [PORT, PEND]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)
open GC.GeneralFlow in
example : type_of% @exists_common_scaffold_extension_with_raw_prefix_with_distance_scalars :=
  @exists_common_scaffold_extension_with_raw_prefix_with_distance_scalars
example : type_of% @GC.GeneralFlow.exists_common_scaffold_extension_with_raw_prefix :=
  @GC.GeneralFlow.exists_common_scaffold_extension_with_raw_prefix
example : type_of% @GC.GeneralFlow.exists_common_scaffold_extension :=
  @GC.GeneralFlow.exists_common_scaffold_extension
end GC.GeneralFlow
end

-- RF.Surgery.Noncollapsing.CommonScaffoldObservationPortC11P  [PORT, PEND]
section
set_option autoImplicit false
noncomputable section
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
universe u
open private observation_initial_budget_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricObservationExtension
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)
#guard_msgs (drop warning) in
example :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenterConstant ∧
      p₀.modelAccuracy ≤ εcut ∧ Dcut ≤ p₀.modelRadius ∧ mcut ≤ p₀.modelOrder ∧
      δbound ≤ δcut ∧ ρbound ≤ ρcut ∧ p₀.recenterConstant * δbound ≤ 1 / 2 ∧
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        (∀ i : Fin K.eventCount, (K.toHistory.event i).HasUniformDistanceScalar Cdist) ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        (∀ i b, ((records i).static b).witness.HasRadialCoordinates ∧
          ((records i).static b).hasLinkedCanonicalWindow_C12X) ∧
        RecordHypFar_C12X (5 / 4) K records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F :=
  (@_root_.GC.GeneralFlow.exists_common_scaffold_noncollapsed_geometric_observation_before_quality_with_radial_coordinates_with_distance_scalars).imp fun Cdist h =>
    ⟨h.1, h.2.imp fun fixed h => h.imp fun r h => ⟨h.1.1, h.2⟩⟩
#guard_msgs (drop warning) in
example :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenterConstant ∧
      p₀.modelAccuracy ≤ εcut ∧ Dcut ≤ p₀.modelRadius ∧ mcut ≤ p₀.modelOrder ∧
      δbound ≤ δcut ∧ ρbound ≤ ρcut ∧ p₀.recenterConstant * δbound ≤ 1 / 2 ∧
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        (∀ i b, ((records i).static b).witness.HasRadialCoordinates ∧
          ((records i).static b).hasLinkedCanonicalWindow_C12X) ∧
        RecordHypFar_C12X (5 / 4) K records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F :=
  @_root_.GC.GeneralFlow.exists_common_scaffold_noncollapsed_geometric_observation_before_quality_with_radial_coordinates
#guard_msgs (drop warning) in
example :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenterConstant ∧
      p₀.modelAccuracy ≤ εcut ∧ Dcut ≤ p₀.modelRadius ∧ mcut ≤ p₀.modelOrder ∧
      δbound ≤ δcut ∧ ρbound ≤ ρcut ∧ p₀.recenterConstant * δbound ≤ 1 / 2 ∧
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F :=
  @_root_.GC.GeneralFlow.exists_common_scaffold_noncollapsed_geometric_observation_before_quality
#guard_msgs (drop warning) in
example :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (p₀ : CutoffParameters) (δbound ρbound ε κ v : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenterConstant ∧
      p₀.modelAccuracy ≤ εcut ∧ Dcut ≤ p₀.modelRadius ∧ mcut ≤ p₀.modelOrder ∧
      δbound ≤ δcut ∧ ρbound ≤ ρcut ∧ p₀.recenterConstant * δbound ≤ 1 / 2 ∧
      0 < δbound ∧ 0 < ρbound ∧ 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F :=
  @_root_.GC.GeneralFlow.exists_common_scaffold_noncollapsed_geometric_observation
end GC.GeneralFlow
end

-- RF.Surgery.Noncollapsing.GeometricObservationExtension  [PATCHED, REG]
section
set_option autoImplicit false
noncomputable section
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
universe u
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)
#guard_msgs (drop warning) in
example :
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B),
    ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧
      ∀ (H : RetainedCoreHistory.{u})
        (A : InitialIdentification P g H.toHistory) (p : CutoffParameters)
        (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
        H.horizon ≤ B → H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound old →
        ∀ w : ℝ, 0 < w →
          (∀ i : Fin H.eventCount,
            ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
                  (H.coreEvent i).outputMetric univ +
                ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * w) ≤
              riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
                (H.coreEvent i).terminal.metric F) →
          ∃ (K : RetainedCoreHistory.{u})
            (A' : InitialIdentification P g K.toHistory) (q : CutoffParameters)
            (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i q)
            (hc : H.eventCount ≤ K.eventCount),
            K.horizon = B ∧ A.IsPrefixOf A' ∧
            (HistoryEventControl H → HistoryEventControl K) ∧
            (∀ t : ℝ, t ≤ H.horizon → q.delta t = p.delta t ∧
              q.neckRadius t = p.neckRadius t ∧ q.protectedRadius t = p.protectedRadius t) ∧
            K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
            (∀ i : Fin H.eventCount,
              HEq (records (Fin.castLE hc i)).nominalRadius (old i).nominalRadius ∧
              HEq (records (Fin.castLE hc i)).delta (old i).delta ∧
              HEq (records (Fin.castLE hc i)).order (old i).order ∧
              HEq (records (Fin.castLE hc i)).neck (old i).neck ∧
              HEq (records (Fin.castLE hc i)).static (old i).static) ∧
            ∀ i : Fin K.eventCount,
              ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
                riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                    (K.coreEvent i).outputMetric univ +
                  ENNReal.ofReal
                    ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * min w v) ≤
                riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
                  (K.coreEvent i).terminal.metric F :=
  @_root_.GC.GeneralFlow.exists_geometric_observation_extension_preserving_control
#guard_msgs (drop warning) in
example :
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B),
    ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧
      ∀ (H : RetainedCoreHistory.{u})
        (A : InitialIdentification P g H.toHistory) (p : CutoffParameters)
        (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
        H.horizon ≤ B → H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound old →
        ∀ w : ℝ, 0 < w →
          (∀ i : Fin H.eventCount,
            ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
                  (H.coreEvent i).outputMetric univ +
                ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * w) ≤
              riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
                (H.coreEvent i).terminal.metric F) →
          ∃ (K : RetainedCoreHistory.{u})
            (A' : InitialIdentification P g K.toHistory) (q : CutoffParameters)
            (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i q)
            (hc : H.eventCount ≤ K.eventCount),
            K.horizon = B ∧ A.IsPrefixOf A' ∧
            K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
            (∀ i : Fin H.eventCount,
              HEq (records (Fin.castLE hc i)).nominalRadius (old i).nominalRadius ∧
              HEq (records (Fin.castLE hc i)).delta (old i).delta ∧
              HEq (records (Fin.castLE hc i)).order (old i).order ∧
              HEq (records (Fin.castLE hc i)).neck (old i).neck ∧
              HEq (records (Fin.castLE hc i)).static (old i).static) ∧
            ∀ i : Fin K.eventCount,
              ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
                riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                    (K.coreEvent i).outputMetric univ +
                  ENNReal.ofReal
                    ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * min w v) ≤
                riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
                  (K.coreEvent i).terminal.metric F :=
  @_root_.GC.GeneralFlow.exists_geometric_observation_extension
end GC.GeneralFlow
end
end

-- RF.Surgery.Noncollapsing.NativeObservationCertificates  [VERBATIM, PEND]
section
example : type_of% @GC.GeneralFlow.NativeEstimates.exists_outgoingSlab_of_lt_horizon :=
  @GC.GeneralFlow.NativeEstimates.exists_outgoingSlab_of_lt_horizon
example : type_of% @GC.GeneralFlow.NativeEstimates.buffered_incoming_certificates :=
  @GC.GeneralFlow.NativeEstimates.buffered_incoming_certificates
end

-- RF.Surgery.Noncollapsing.NativeObservationDerivativeBoundsPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology
namespace GC.GeneralFlow
universe u
#guard_msgs (drop warning) in
example :
    ∀ {K : RetainedCoreHistory.{u}}
    {ε C1 C2 C1s C2s qcan qs τmin : ℝ} {Ctime Cgrad : ℝ≥0}
    (hEst : NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad)
    (hqcan : 0 < qcan)
    (j : Fin (K.eventCount + 1)) (s : ℝ)
    (hs : s ∈ Ico (K.time j) (K.toHistory.stageEndTime j))
    (y : (K.stage j).Carrier)
    (hscalar : qcan < metricScalarAt (K.toHistory.stageMetric j s) y),
    (K.time j < s →
      |derivWithin (fun v => metricScalarAt (K.toHistory.stageMetric j v) y) (Iic s) s| ≤
        Ctime * metricScalarAt (K.toHistory.stageMetric j s) y ^ 2) ∧
    ∀ v : TangentSpace I3 y,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
        (metricScalarAt (K.toHistory.stageMetric j s)) y v)| ≤
      Cgrad * metricScalarAt (K.toHistory.stageMetric j s) y *
        Real.sqrt (metricScalarAt (K.toHistory.stageMetric j s) y) *
        Real.sqrt ((K.toHistory.stageMetric j s).inner y v v) :=
  @_root_.GC.GeneralFlow.NativeEstimates.time_derivative_gradient_on_stage
end GC.GeneralFlow
end

-- RF.Surgery.Noncollapsing.NoncollapsedGeometricObservationPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
universe u
open private observation_initial_budget_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricObservationExtension
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)
#guard_msgs (drop warning) in
example :
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B)
    (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ)
    (hδcut : 0 < δcut) (hρcut : 0 < ρcut) (hεcut : 0 < εcut) (hDcut : 0 < Dcut),
    ∃ (p₀ : CutoffParameters) (δbound ρbound ε κ v : ℝ),
      p₀.modelAccuracy ≤ εcut ∧ Dcut ≤ p₀.modelRadius ∧ mcut ≤ p₀.modelOrder ∧
      δbound ≤ δcut ∧ ρbound ≤ ρcut ∧ p₀.recenterConstant * δbound ≤ 1 / 2 ∧
      0 < δbound ∧ 0 < ρbound ∧ 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F :=
  @_root_.GC.GeneralFlow.exists_noncollapsed_geometric_observation_with_quality
#guard_msgs (drop warning) in
example :
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B),
    ∃ (p₀ : CutoffParameters) (δbound ρbound ε κ v : ℝ),
      0 < δbound ∧ 0 < ρbound ∧ 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F :=
  @_root_.GC.GeneralFlow.exists_noncollapsed_geometric_observation
end GC.GeneralFlow
end

-- RF.Surgery.Noncollapsing.PreparedDistanceDataPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal ENNReal
namespace GC.GeneralFlow
universe u
#guard_msgs (drop warning) in
example :
    ∀ (Cdist : ℝ≥0)
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B ε κ : ℝ)
    (p₀ : CutoffParameters) (δb ρb : ℝ),
                                          Prop :=
  @_root_.GC.GeneralFlow.PreparedGeometricObservationExtensionWithDistance
#guard_msgs (drop warning) in
example :
    ∀ {Cdist : ℝ≥0} {P : OrientedThreeStage.{u}} {g : P.Metric}
    {B ε κ : ℝ} {p₀ : CutoffParameters} {δb ρb : ℝ}
    (h : PreparedGeometricObservationExtensionWithDistance Cdist P g B ε κ p₀ δb ρb),
    PreparedGeometricObservationExtensionWithNative
      (fun K => ∀ i : Fin K.eventCount,
        (K.toHistory.event i).HasUniformDistanceScalar Cdist) P g B ε κ p₀ δb ρb :=
  @_root_.GC.GeneralFlow.PreparedGeometricObservationExtensionWithDistance.toNative
#guard_msgs (drop warning) in
example :
    ∀ {Cdist : ℝ≥0} {P : OrientedThreeStage.{u}} {g : P.Metric}
    {B ε κ : ℝ} {p₀ : CutoffParameters} {δb ρb : ℝ}
    (h : PreparedGeometricObservationExtensionWithDistance Cdist P g B ε κ p₀ δb ρb),
    PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb :=
  @_root_.GC.GeneralFlow.PreparedGeometricObservationExtensionWithDistance.forget
-- (no example: GC.GeneralFlow.PreparedDistanceClassProvider is not expressible as type_of%)
example : type_of% @GC.GeneralFlow.PreparedDistanceClassProvider.toNative :=
  @GC.GeneralFlow.PreparedDistanceClassProvider.toNative
end GC.GeneralFlow
end

-- RF.Surgery.Noncollapsing.PreparedNativeCertificateDataPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal ENNReal
namespace GC.GeneralFlow
universe u
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)
#guard_msgs (drop warning) in
example :
    ∀ (certificate : RetainedCoreHistory.{u} → Prop)
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B ε κ : ℝ)
    (p₀ : CutoffParameters) (δb ρb : ℝ),
                                          Prop :=
  @_root_.GC.GeneralFlow.PreparedGeometricObservationExtensionWithNative
#guard_msgs (drop warning) in
example :
    ∀ (certificate : RetainedCoreHistory.{u} → Prop)
    (fixed : StaticCapScaffold) (recenter : ℝ),
                                                 Prop :=
  @_root_.GC.GeneralFlow.PreparedClassProviderWithNative
#guard_msgs (drop warning) in
example :
    ∀ {certificate : RetainedCoreHistory.{u} → Prop}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {B ε κ : ℝ}
    {p₀ : CutoffParameters} {δb ρb : ℝ}
    (h : PreparedGeometricObservationExtensionWithNative certificate P g B ε κ p₀ δb ρb),
    PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb :=
  @_root_.GC.GeneralFlow.PreparedGeometricObservationExtensionWithNative.forget
#guard_msgs (drop warning) in
example :
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {B ε κ : ℝ}
    {p₀ : CutoffParameters} {δb ρb : ℝ}
    (h : PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb),
    PreparedGeometricObservationExtensionWithNative (fun _ => True)
      P g B ε κ p₀ δb ρb :=
  @_root_.GC.GeneralFlow.PreparedGeometricObservationExtension.withTrue
example : type_of% @GC.GeneralFlow.PreparedClassProviderWithNative.of_weak :=
  @GC.GeneralFlow.PreparedClassProviderWithNative.of_weak
#guard_msgs (drop warning) in
example :
    ∀ {certificate : RetainedCoreHistory.{u} → Prop}
    {fixed : StaticCapScaffold} {recenter : ℝ}
    (h : PreparedClassProviderWithNative certificate fixed recenter),
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
    ∀ (δcap ρcap εcapRequest DcapRequest : ℝ) (mcapRequest : ℕ),
      0 < δcap → 0 < ρcap → 0 < εcapRequest → 0 < DcapRequest →
    ∃ (p₀ : CutoffParameters) (δb ρb : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
      0 < δb ∧ δb ≤ δcap ∧ 0 < ρb ∧ ρb ≤ ρcap ∧
      p₀.modelAccuracy ≤ εcapRequest ∧ DcapRequest ≤ p₀.modelRadius ∧
      mcapRequest ≤ p₀.modelOrder ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
      (∀ (L : RetainedCoreHistory.{u}) (IL : InitialIdentification P g L.toHistory)
        (pL : CutoffParameters)
        (R : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL),
        L.horizon ≤ B → L.IsCanonicalCutoffRecordFamily p₀ δb ρb R →
        L.NoncollapsedBefore κ ε L.horizon) ∧
      PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb :=
  @_root_.GC.GeneralFlow.PreparedClassProviderWithNative.forget
end GC.GeneralFlow
end

-- RF.Surgery.Noncollapsing.PreparedObservationEstimates  [VERBATIM, PEND]
section
example : type_of% @GC.GeneralFlow.exists_prepared_extension_with_two_estimate_packets :=
  @GC.GeneralFlow.exists_prepared_extension_with_two_estimate_packets
example : type_of% @GC.GeneralFlow.exists_prepared_extension_with_reserved_later_class :=
  @GC.GeneralFlow.exists_prepared_extension_with_reserved_later_class
end

-- RF.Surgery.Noncollapsing.RegularObservationNoncollapse  [VERBATIM, REG]
section
example : type_of% @GC.GeneralFlow.exists_regular_observation_noncollapsed :=
  @GC.GeneralFlow.exists_regular_observation_noncollapsed
end

-- RF.Surgery.Noncollapsing.UniformClosedBirthObservationEstimatesPortC11P  [PORT, PEND]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal
namespace GC.GeneralFlow
universe u
#guard_msgs (drop warning) in
example :
    ∃ εbar : ℝ, 0 < εbar ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar →
    ∃ (C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0),
      1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 1 ≤ Cs ∧
      0 < τmin ∧ 1 ≤ Cbirth ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
    ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
      max 1 (max qcan qs) ≤ Qbirth ∧
      0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (K : RetainedCoreHistory.{u}) (I : InitialIdentification P g K.toHistory)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
      K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      K.NoncollapsedBefore κ ε K.horizon →
      NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
      ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
        (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
        K.toHistory.activeStage t ≠ 0 →
        ∀ y : (K.toHistory.stageAt t).Carrier,
          Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
          ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
            ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε :=
  @_root_.GC.GeneralFlow.exists_uniform_closed_birth_observation_estimate_packet
end GC.GeneralFlow
end

-- RF.Surgery.Topology.CapWindowActionRecentNodePortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
open DifferentialGeometry.Tensor0SBundle in
#guard_msgs (drop warning) in
example :
    ∀ (Aact E rTerm qDeriv a₀ ρ c Rbirth : ℝ) (Cderiv : ℝ≥0)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hρ : 0 < ρ) (hc : 0 < c)
    (hRbirth : StandardCap.transitionEnd ≤ Rbirth),
    ∃ (εreq Rreq : ℝ) (mreq : ℕ) (δreq : ℝ),
      0 < εreq ∧ εreq ≤ 1 / 2 ∧ 0 < Rreq ∧ Rbirth < Rreq ∧
      4 ≤ mreq ∧ 0 < δreq ∧
      (∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} (event : MetricCutCapEvent P Q a s)
        {fixed : StaticCapScaffold} {Dbig ζ : ℝ} {m : ℕ},
        Rreq ≤ Dbig → mreq ≤ m → ζ ≤ εreq →
        ∀ {b : event.RetainedBoundaryIndex}
          (raw : event.PresentedStaticCap fixed Dbig m ζ b), raw.hasCanonicalWindow →
          ∀ x : standardCapWindow Dbig, ‖x.val‖ < Dbig → ∀ ell : ℝ,
            ell ^ 4 * normSq0S event.outputMetric (raw.window x) 4
              (metricRm04At event.outputMetric (raw.window x)) ≤ 1 →
            raw.neck.scale * ell ^ 2 ≤ 18) ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
    ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
    ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
    ∀ (i : Fin H.eventCount) (hf : first ≤ i.succ) (hl : i.succ ≤ H.activeStage t),
      t.val - v ^ 2 ≤ H.time i.succ →
      parameters.recenterConstant ≤ c →
      parameters.delta (H.time i.succ) ≤ δreq →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ δreq) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (Dbig ζ : ℝ) (m : ℕ)
        (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
        Rreq ≤ Dbig → mreq ≤ m → ζ ≤ εreq → S.hasCanonicalWindow →
        S.neck.scale = ((records i).static b).neck.scale →
        gamma ⟨i.succ, hf, hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∉
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ Rbirth} :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_cap_window_exclusion_of_raw_cap_requests_with_window_scale_bound
#guard_msgs (drop warning) in
example :
    ∀ (Aact E rTerm qDeriv a₀ ρ c Rbirth : ℝ) (Cderiv : ℝ≥0)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hρ : 0 < ρ) (hc : 0 < c)
    (hRbirth : StandardCap.transitionEnd ≤ Rbirth),
    ∃ (εreq Rreq : ℝ) (mreq : ℕ) (δreq : ℝ),
      0 < εreq ∧ εreq ≤ 1 / 2 ∧ 0 < Rreq ∧ Rbirth < Rreq ∧
      4 ≤ mreq ∧ 0 < δreq ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
    ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
    ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
    ∀ (i : Fin H.eventCount) (hf : first ≤ i.succ) (hl : i.succ ≤ H.activeStage t),
      t.val - v ^ 2 ≤ H.time i.succ →
      parameters.recenterConstant ≤ c →
      parameters.delta (H.time i.succ) ≤ δreq →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ δreq) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (Dbig ζ : ℝ) (m : ℕ)
        (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
        Rreq ≤ Dbig → mreq ≤ m → ζ ≤ εreq → S.hasCanonicalWindow →
        S.neck.scale = ((records i).static b).neck.scale →
        gamma ⟨i.succ, hf, hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∉
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ Rbirth} :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_cap_window_exclusion_of_raw_cap_requests
#guard_msgs (drop warning) in
example :
    ∀ (Aact E rTerm qDeriv a₀ ρ c Rbirth : ℝ) (Cderiv : ℝ≥0)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hρ : 0 < ρ) (hc : 0 < c)
    (hRbirth : StandardCap.transitionEnd ≤ Rbirth),
    ∃ (εreq Rreq : ℝ) (mreq : ℕ) (δreq : ℝ),
      0 < εreq ∧ 0 < Rreq ∧ 0 < δreq ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
    ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
    ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
    ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
      parameters.recenterConstant ≤ c →
      parameters.delta (H.time i.succ) ≤ δreq →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ δreq) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      (∀ b : (H.event i).RetainedBoundaryIndex,
        ∃ (Dbig ζ : ℝ) (m : ℕ)
          (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
          Rreq ≤ Dbig ∧ mreq ≤ m ∧ ζ ≤ εreq ∧ S.hasCanonicalWindow ∧
          S.neck.scale = ((records i).static b).neck.scale) →
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (t.val - H.time i.succ))) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_regularCrossing_at_node_of_raw_cap_requests
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

-- RF.Surgery.Topology.CutoffRecordCanonicalRadiusPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
#guard_msgs (drop warning) in
example :
    ∀ {R q : ℝ} (hR : 0 < R) (hq : 0 < q),
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ q ≤ (ρ ^ 2)⁻¹ :=
  @_root_.GC.GeneralFlow.exists_canonical_radius_below
example : type_of% @GC.GeneralFlow.exists_canonical_radius_records_at_join :=
  @GC.GeneralFlow.exists_canonical_radius_records_at_join
end GC.GeneralFlow
end

-- RF.Surgery.Topology.CutoffRecordDelayedRadiusPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
open private affine_future_neckRadius_budget from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordCanonicalRadiusPortC11P
#guard_msgs (drop warning) in
example :
    ∀ {H K J : RetainedCoreHistory.{u}}
    (F : AffineEventPrefix K J (H.time (Fin.last H.eventCount)) H.eventCount
      (Fin.last K.eventCount))
    (pH pK q : CutoffParameters)
    (hqneck : q.neckRadius = (pH.spliceAfter
      (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) H.horizon).neckRadius)
    {rOld rNew A : ℝ} (hrNew : 0 < rNew) (hrNewOld : rNew ≤ rOld)
    (hanti : AntitoneOn pH.neckRadius (Ici 0))
    (hflat : ∀ t : ℝ, H.horizon ≤ t → pH.neckRadius t = rOld)
    (hA : H.horizon ≤ A)
    (hcut : ∀ i : Fin K.eventCount, pK.neckRadius (K.time i.succ) ≤ rNew),
    let oldRadius : CutoffParameters := { q with
      neckRadius := pH.neckRadius, neckRadius_pos := pH.neckRadius_pos }
    let newRadius : CutoffParameters := { q with
      neckRadius := fun _ => rNew, neckRadius_pos := fun _ _ => hrNew }
    let p := oldRadius.spliceAfter newRadius A
    AntitoneOn p.neckRadius (Ici 0) ∧
      p.delta = q.delta ∧ p.protectedRadius = q.protectedRadius ∧
      p.fixed = q.fixed ∧ p.modelRadius = q.modelRadius ∧
      p.modelOrder = q.modelOrder ∧ p.modelAccuracy = q.modelAccuracy ∧
      p.recenterConstant = q.recenterConstant ∧
      (∀ t : ℝ, t ≤ A → p.neckRadius t = pH.neckRadius t) ∧
      (∀ t : ℝ, A < t → p.neckRadius t = rNew) ∧
      (∀ t : ℝ, t ≤ H.horizon → p.delta t = q.delta t ∧
        p.neckRadius t = q.neckRadius t ∧ p.protectedRadius t = q.protectedRadius t) ∧
      (∀ i : Fin J.eventCount,
        q.neckRadius (J.time i.succ) ≤ p.neckRadius (J.time i.succ)) ∧
      ∀ R : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i q,
        (∀ i b, ((R i).static b).hasCanonicalWindow) →
        ∃ S : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i p,
          (∀ i, (S i).nominalRadius = (R i).nominalRadius ∧
            (S i).delta = (R i).delta ∧ (S i).order = (R i).order ∧
            HEq (S i).neck (R i).neck ∧ HEq (S i).backward (R i).backward ∧
            HEq (S i).static (R i).static) ∧
          ∀ i b, ((S i).static b).hasCanonicalWindow :=
  @_root_.GC.GeneralFlow.exists_delayed_canonical_radius_records_at_join
end GC.GeneralFlow
end

-- RF.Surgery.Topology.CutoffRecordHistoryRestriction.BasicPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped Manifold ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
open private RetainedCoreHistory.volume_lower_bound_of_stage_index
  RetainedCoreHistory.rm_bound_of_stage_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapse.Basic
namespace RetainedCoreHistory
variable (H : RetainedCoreHistory.{u})
#guard_msgs (drop warning) in
example :
    ∀ (a : Icc (0 : ℝ) H.horizon) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
    ∀ i : Fin (H.restrict a).eventCount, GeometricCutoffRecord (H.restrict a).toHistory i p :=
  _root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.restrictRecords
    H
#guard_msgs (drop warning) in
example :
    ∀ (a : Icc (0 : ℝ) H.horizon) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (i : Fin (H.restrict a).eventCount),
    let j := Fin.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt) i
    HEq (H.restrictRecords a records i).nominalRadius (records j).nominalRadius ∧
      HEq (H.restrictRecords a records i).delta (records j).delta ∧
      HEq (H.restrictRecords a records i).order (records j).order ∧
      HEq (H.restrictRecords a records i).neck (records j).neck ∧
      HEq (H.restrictRecords a records i).static (records j).static :=
  _root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.restrictRecords_preserves
    H
#guard_msgs (drop warning) in
example :
    ∀ (a : Icc (0 : ℝ) H.horizon)
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hwin : ∀ i b, ((records i).static b).hasCanonicalWindow),
    ∀ i b, ((H.restrictRecords a records i).static b).hasCanonicalWindow :=
  _root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.canonicalWindows_restrictRecords
    H
#guard_msgs (drop warning) in
example :
    ∀ (a : Icc (0 : ℝ) H.horizon)
    {p₀ p : CutoffParameters} {δ₀ ρ₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records),
    (H.restrict a).IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ (H.restrictRecords a records) :=
  _root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isCanonicalCutoffRecordFamily_restrict
    H
#guard_msgs (drop warning) in
example :
    ∀ (a : Icc (0 : ℝ) H.horizon) {κ ρ t₀ : ℝ}
    (hH : H.NoncollapsedBefore κ ρ t₀) (ha : (a : ℝ) ≤ t₀),
    (H.restrict a).NoncollapsedBefore κ ρ a :=
  _root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.noncollapsedBefore_restrict
    H
end RetainedCoreHistory
#guard_msgs (drop warning) in
example :
    ∀ {H J : ObservedHistory.{u}} (h : H.IsPrefixOf J)
    (a : Icc (0 : ℝ) J.horizon) (ha : H.horizon ≤ (a : ℝ)),
    H.IsPrefixOf (J.restrict a) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.restrict_right
#guard_msgs (drop warning) in
example :
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {H J : ObservedHistory.{u}}
    {IH : InitialIdentification P g H} {IJ : InitialIdentification P g J}
    (h : IH.IsPrefixOf IJ) (a : Icc (0 : ℝ) J.horizon) (ha : H.horizon ≤ (a : ℝ)),
    IH.IsPrefixOf (IJ.restrict a) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.restrict_right
#guard_msgs (drop warning) in
example :
    ∀ {H J : RetainedCoreHistory.{u}} {pH pJ : CutoffParameters}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH)
    (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i pJ)
    (hp : H.toHistory.IsPrefixOf J.toHistory) (hn : H.eventCount ≤ J.eventCount)
    (hOld : ∀ i : Fin H.eventCount,
      HEq (records (i.castLE hn)).nominalRadius (old i).nominalRadius ∧
      HEq (records (i.castLE hn)).delta (old i).delta ∧
      HEq (records (i.castLE hn)).order (old i).order ∧
      HEq (records (i.castLE hn)).neck (old i).neck ∧
      HEq (records (i.castLE hn)).static (old i).static)
    (a : Icc (0 : ℝ) J.horizon) (ha : H.horizon ≤ (a : ℝ)),
    ∃ hn' : H.eventCount ≤ (J.restrict a).eventCount,
      ∀ i : Fin H.eventCount,
        HEq (J.restrictRecords a records (i.castLE hn')).nominalRadius (old i).nominalRadius ∧
        HEq (J.restrictRecords a records (i.castLE hn')).delta (old i).delta ∧
        HEq (J.restrictRecords a records (i.castLE hn')).order (old i).order ∧
        HEq (J.restrictRecords a records (i.castLE hn')).neck (old i).neck ∧
        HEq (J.restrictRecords a records (i.castLE hn')).static (old i).static :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.restrictRecords_preserves_old
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
#guard_msgs (drop warning) in
example :
    ∀ {H : RetainedCoreHistory.{u}}
    (hH : HistoryEventControl H) (a : Icc (0 : ℝ) H.horizon),
    HistoryEventControl (H.restrict a) :=
  @_root_.GC.GeneralFlow.history_control_restrict
end GC.GeneralFlow
end

-- RF.Surgery.Topology.EventCapNoShortcut  [PATCHED, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter Function Manifold TopologicalSpace Bundle MeasureTheory
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
section WindowQuadraticBound
open StandardCap DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}
end WindowQuadraticBound
private local instance sphereDimension : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) :=
  ⟨by simp [ThreeSpace]⟩
#guard_msgs (drop warning) in
example :
    ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow)
    (hε : ε ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < D)
    (u z : E.old)
    (hu : ∀ b, E.oldOutput u ∉ (S b).window ''
      {x : standardCapWindow D | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (hz : ∀ b, E.oldOutput z ∉ (S b).window ''
      {x : standardCapWindow D | ‖x.val‖ ≤ StandardCap.transitionEnd + 10}),
    riemannianEDistOf E.terminal.metric (E.oldTerminal u) (E.oldTerminal z) ≤
      riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput z) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.oldTerminal_edist_le_of_outside_canonical_cap_windows
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end

-- RF.Surgery.Topology.FiniteOutputDistanceScalarPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set Bundle Filter Function Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
private local instance : Nonempty (Sphere 2) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_uniform_finite_output_distance_scalar :=
  @exists_uniform_finite_output_distance_scalar
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end

-- RF.Surgery.Topology.HistoryNoncollapsePrefix.Basic  [VERBATIM, REG]
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @noncollapsedBefore_of_isPrefixOf := @noncollapsedBefore_of_isPrefixOf
end

-- RF.Surgery.Topology.HistoryNoncollapsingPresentation.Basic  [PATCHED, REG]
section
set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
namespace RetainedCoreHistory
#guard_msgs (drop warning) in
example :
    ∀ {H K : RetainedCoreHistory.{u}} (R : H.toHistory.SamePresentation K.toHistory)
    (κ ρ t₀ : ℝ),
                   H.NoncollapsedBefore κ ρ t₀ ↔ K.NoncollapsedBefore κ ρ t₀ :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.noncollapsedBefore_iff_of_samePresentation
end RetainedCoreHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end

-- RF.Surgery.Topology.TracedRegionVolumePortC11P  [PORT, PEND]
section
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace Manifold
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier := borel P.Carrier
private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩
#guard_msgs (drop warning) in
example :
    ∀ (H : ObservedHistory.{u}) (t v : Icc (0 : ℝ) H.horizon) (hvt : v ≤ t)
    (p : (H.stageAt t).Carrier) {ρ τ K κ R r : ℝ} (hK : 0 ≤ K)
    (h : H.isTracedRegion t p ρ τ K) (hv : (t : ℝ) - τ ≤ v)
    (A : BackwardPointTrace H (H.activeStage v) (H.activeStage t)
      (H.activeStage_mono hvt) p)
    (hRρ : R ≤ ρ)
    (hvolume : ∀ s : ℝ, 0 < s → s ≤ R →
      ENNReal.ofReal κ * ENNReal.ofReal s ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t)
          (riemannianBallOf (H.stageMetric (H.activeStage t) t) p s))
    (hr : 0 < r) (hrR : r ≤ R),
    ENNReal.ofReal (Real.exp (-54 * K * τ) * κ) * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
        (H.stageMetric (H.activeStage v) v)
        (riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) r) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.volume_ball_ge_along_trace_of_isTracedRegion
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

-- RF.Surgery.Topology.UniformBirthSpatialCanonicalWitnessPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open private RetainedCoreHistory.le_static_scale_of_neckRadius_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCrossingContinuationLeaf
open private RetainedCoreHistory.exists_spatialCanonicalWitness_before_birth
  RetainedCoreHistory.curvatureOperatorLowerBoundAt_before_of_eventSlabsPinched from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthTimeZeroBoundPortC11P
universe u
namespace RetainedCoreHistory
#guard_msgs (drop warning) in
example :
    ∃ εbar : ℝ, 0 < εbar ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar →
    ∃ Cbirth : ℝ, 1 ≤ Cbirth ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
      (κ ρ C1s C2s : ℝ) (Ctime Cgrad : ℝ≥0) (phi : ℝ → ℝ) (Q : ℝ),
      0 < κ → 0 < ρ → Perelman.AdmissiblePinchingFunction phi → 1 ≤ Q →
    ∃ (Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      Q ≤ Qbirth ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (H : RetainedCoreHistory.{u})
      (I : InitialIdentification P₀ g₀ H.toHistory)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      H.EventSlabsPinched phi →
      (∀ hfinal : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab hfinal).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi) →
    ∀ t : Icc (0 : ℝ) H.toHistory.horizon,
      (t : ℝ) < H.horizon → H.time (H.toHistory.activeStage t) = (t : ℝ) →
      H.toHistory.activeStage t ≠ 0 →
      H.EventSlabsSpatiallyCanonical ε C1s C2s Q (H.toHistory.activeStage t) →
      H.EventSlabsDerivative Ctime Q (H.toHistory.activeStage t) →
      H.EventSlabsGradient Cgrad Q (H.toHistory.activeStage t) →
      H.NoncollapsedBefore κ ρ (t : ℝ) →
    ∀ (s : ℝ) (G : (H.stage (H.toHistory.activeStage t)).IncomingSlab
        (H.time (H.toHistory.activeStage t)) s),
      (∀ v : ℝ, G.flow.base.metric v =
        H.toHistory.stageMetric (H.toHistory.activeStage t) v) →
      G.DerivativeBoundBefore Ctime Q s → G.GradientBoundBefore Cgrad Q s →
    ∀ y : (H.toHistory.stageAt t).Carrier,
      Qbirth < metricScalarAt (H.initialMetric (H.toHistory.activeStage t)) y →
      ∃ W : SpatialCanonicalWitness (H.initialMetric (H.toHistory.activeStage t))
        ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_uniform_spatialCanonicalWitness_at_nonzero_birth
end RetainedCoreHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end

-- RF.Surgery.Topology.UniformCapWindowBirthSpatialCanonicalWitnessPortC11P  [PORT, REG]
section
set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open private capWindowSpatialSigmaCompact from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformCapWindowSpatialCanonicalWitness
attribute [local instance] capWindowSpatialSigmaCompact
namespace RetainedCoreHistory
#guard_msgs (drop warning) in
example :
    ∀ {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11),
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
    ∀ (Ctime Cgrad : ℝ≥0) (Dw θcap : ℝ), 0 < Dw → θcap < 1 →
    ∃ (Rcap : ℝ) (mcap : ℕ), Dw + 1 < Rcap ∧
    ∀ qcan : ℝ, 0 < qcan →
    ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Rcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ H : RetainedCoreHistory.{u}, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative Ctime qcan k →
      Gk.DerivativeBoundBefore Ctime qcan s → Gk.GradientBoundBefore Cgrad qcan s →
    ∀ y : (H.stage k).Carrier, H.CapWindowPoint records k y (H.time k) Dw θcap →
      qcan < metricScalarAt (H.initialMetric k) y →
      ∃ W : SpatialCanonicalWitness (H.initialMetric k) ε Cs (max Cs (Cgrad : ℝ)) y,
        W.capTubeHasNeckChart ε :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_uniform_capWindowPoint_spatialCanonicalWitness_at_birth
end RetainedCoreHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end

-- RF.Surgery.Topology.UniformFineCutoffScaffoldPortC11P  [PORT, PEND]
section
set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open private
  exists_horn_cutoff_record_at_scale_of_prepared_history_of_fineCutNecks_with_distance_scalars from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecksDistanceC11X
open private
  exists_poincareStandardDiscarded_of_retainedEvent_heq_of_spatiallyCanonical from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecks
open private RetainedCoreHistory.hasCanonicalCutoffRecords_of_appendEvent_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecord
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
#guard_msgs (drop warning) in
example :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εcoarse : ℝ, 0 < εcoarse ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy → ∀ ηrecord : ℝ, 0 < ηrecord →
    ∃ δ ε₀ Λq : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < ε₀ ∧ 0 < Λq ∧
    ∀ q0 : ℝ, 0 < q0 →
    ∀ Λmax coreFloor : ℝ, 1 ≤ Λmax → 0 < coreFloor → ∀ Qlower : ℝ,
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ Λq * max q0 1 ≤ Q ∧ Qlower < Q ∧
      v = Q ^ (-3 / 2 : ℝ) ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ ρold : ℝ, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters),
    G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount) →
    let D : OneStepIncoming := {
      stage := H.stage (Fin.last H.eventCount)
      startTime := H.time (Fin.last H.eventCount)
      endTime := s
      startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
      startTime_lt_endTime := G.lt
      slab := G
      terminal := L
      singular := hsing
      parameters := stepParameters }
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q0 < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q0 < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2) →
    ∀ {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ εcoarse →
      ∀ {εc : ℝ}, 0 < εc → εc ≤ ε → εc ≤ ε₀ → P.FineCutNecks εc Q →
      Λ ≤ Λmax → coreFloor ≤ P.coreRadius →
      ∃ (Qout : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory.{u}) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => D.parameters.neckRadius D.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dbig ∧
        parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, δOriginal j ≤ 2 * εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        (∃ Record : GeometricCutoffRecord K.toHistory i parameters,
          Record.delta = (fun _ => δ) ∧
          Record.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
          HEq Record.neck Nrecord ∧ (∀ j, (Record.neck j).scale = Q) ∧
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
          (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
          Record.DeepNecks_C12X (5 / 4)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) ∧
        (parameters.modelAccuracy ≤ 1 / 2 → standardCapL + 1 ≤ parameters.modelRadius →
          E.HasUniformDistanceScalar Cdist ∧
          (K.toHistory.event i).HasUniformDistanceScalar Cdist) :=
  (@_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_horn_cutoff_record_with_volume_debit_of_fineCutNecks_with_radial_coordinates_with_distance_scalars).imp fun Cdist h =>
    ⟨h.1, h.2.imp fun fixed h => h.imp fun r h => ⟨h.1.1, h.2⟩⟩
#guard_msgs (drop warning) in
example :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εcoarse : ℝ, 0 < εcoarse ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy → ∀ ηrecord : ℝ, 0 < ηrecord →
    ∃ δ ε₀ Λq : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < ε₀ ∧ 0 < Λq ∧
    ∀ q0 : ℝ, 0 < q0 →
    ∀ Λmax coreFloor : ℝ, 1 ≤ Λmax → 0 < coreFloor → ∀ Qlower : ℝ,
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ Λq * max q0 1 ≤ Q ∧ Qlower < Q ∧
      v = Q ^ (-3 / 2 : ℝ) ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ ρold : ℝ, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters),
    G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount) →
    let D : OneStepIncoming := {
      stage := H.stage (Fin.last H.eventCount)
      startTime := H.time (Fin.last H.eventCount)
      endTime := s
      startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
      startTime_lt_endTime := G.lt
      slab := G
      terminal := L
      singular := hsing
      parameters := stepParameters }
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q0 < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q0 < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2) →
    ∀ {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ εcoarse →
      ∀ {εc : ℝ}, 0 < εc → εc ≤ ε → εc ≤ ε₀ → P.FineCutNecks εc Q →
      Λ ≤ Λmax → coreFloor ≤ P.coreRadius →
      ∃ (Qout : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory.{u}) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => D.parameters.neckRadius D.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dbig ∧
        parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, δOriginal j ≤ 2 * εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        (∃ Record : GeometricCutoffRecord K.toHistory i parameters,
          Record.delta = (fun _ => δ) ∧
          Record.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
          HEq Record.neck Nrecord ∧ (∀ j, (Record.neck j).scale = Q) ∧
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
          (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
          Record.DeepNecks_C12X (5 / 4)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_horn_cutoff_record_with_volume_debit_of_fineCutNecks_with_radial_coordinates
open OneStepIncoming in
#guard_msgs (drop warning) in
example :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (η : ℝ), 0 < η →
    ∃ εP εbar : ℝ, 0 < εP ∧ εP ≤ η ∧ 0 < εbar ∧ εbar < 1 / 11 ∧
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy → ∀ ηrecord : ℝ, 0 < ηrecord →
    ∃ δ εcut : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < εcut ∧ εcut ≤ εP ∧
    ∀ C1 C2 : ℝ, 1 ≤ C2 →
    ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧
    ∀ qcan originalCoreFloor protectedFloor Kfine : ℝ,
      0 < qcan → 0 < originalCoreFloor → 0 < protectedFloor → 0 ≤ Kfine →
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ v = Q ^ (-3 / 2 : ℝ) ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ ρold : ℝ, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters),
    G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount) →
    let D : OneStepIncoming := {
      stage := H.stage (Fin.last H.eventCount)
      startTime := H.time (Fin.last H.eventCount)
      endTime := s
      startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
      startTime_lt_endTime := G.lt
      slab := G
      terminal := L
      singular := hsing
      parameters := stepParameters }
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, qcan < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2) →
    originalCoreFloor ≤ D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime →
    protectedFloor ≤ D.parameters.protectedRadius D.endTime →
    G.SpatiallyCanonicalBefore εbar C1 C2 qcan s →
    (∀ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t)
      (P : TerminalCorePresentation (D.withNeckRadius ρ hρ) εP Λ),
      Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Q → P.FineCutNecks εcut Q) →
    ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
      (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
      (Antitone D.parameters.neckRadius → Antitone ρ) ∧
      (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
      (HasRecenterConstants.{u} D.parameters →
        HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
      D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
      let D' := D.withNeckRadius ρ hρ
      ∃ P : TerminalCorePresentation D' εP Λ,
        P.coreRadius = D.parameters.delta D.endTime * ρ D.endTime ∧
        qcan < (P.coreRadius ^ 2)⁻¹ ∧
        (P.coreRadius ^ 2)⁻¹ ≤
          max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
            ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max (C * qcan) 0 + 1) / C) ∧
        (∀ x : D.slab.terminalRegularOpen,
          metricScalarAt D.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹ →
            ∃ c ∈ P.component, x ∈ interior (P.core c)) ∧
        (∀ c e, ∃ (p : D.slab.terminalRegularOpen)
          (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
          |level| ≤ 3 ∧ metricScalarAt D.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹ ∧
          ∀ y, P.horn c e (y, 0) = N.map (y, level)) ∧
      ∃ (Qout : OrientedThreeStage.{u})
        (E : MetricCutCapEvent D'.stage Qout D'.startTime D'.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory.{u}) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D'.slab ∧ HEq E.terminal D'.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D'.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D'.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D'.stage ∧ K.time i.castSucc = D'.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D'.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D'.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => D'.parameters.neckRadius D'.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dbig ∧
        parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D'.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D'.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, δOriginal j ≤ 2 * εcut ∧ ⌊εcut⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        (∃ Record : GeometricCutoffRecord K.toHistory i parameters,
          Record.delta = (fun _ => δ) ∧
          Record.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
          HEq Record.neck Nrecord ∧ (∀ j, (Record.neck j).scale = Q) ∧
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
          (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
          Record.DeepNecks_C12X (5 / 4) ∧
          E.poincareStandardDiscarded ∧ (K.toHistory.event i).poincareStandardDiscarded ∧
          (p₀.fixed = fixed → p₀.recenterConstant = recenterConstant →
            p₀.modelOrder = m → p₀.modelAccuracy = accuracy → ηrecord ≤ δold →
            D.parameters.neckRadius D.endTime ≤ ρold →
              K.hasCanonicalCutoffRecords p₀ δold ρold)) ∧
        (∃ Kvol : Set D'.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D'.slab.terminalRegularOpen D'.terminal.metric
            Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) ∧
        (parameters.modelAccuracy ≤ 1 / 2 → standardCapL + 1 ≤ parameters.modelRadius →
          E.HasUniformDistanceScalar Cdist ∧
          (K.toHistory.event i).HasUniformDistanceScalar Cdist) :=
  (@_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_horn_cutoff_record_of_fineCutNecks_of_le_with_radial_coordinates_with_distance_scalars).imp fun Cdist h =>
    ⟨h.1, h.2.imp fun fixed h => h.imp fun r h => ⟨h.1.1, h.2⟩⟩
open OneStepIncoming in
#guard_msgs (drop warning) in
example :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (η : ℝ), 0 < η →
    ∃ εP εbar : ℝ, 0 < εP ∧ εP ≤ η ∧ 0 < εbar ∧ εbar < 1 / 11 ∧
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy → ∀ ηrecord : ℝ, 0 < ηrecord →
    ∃ δ εcut : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < εcut ∧ εcut ≤ εP ∧
    ∀ C1 C2 : ℝ, 1 ≤ C2 →
    ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧
    ∀ qcan originalCoreFloor protectedFloor Kfine : ℝ,
      0 < qcan → 0 < originalCoreFloor → 0 < protectedFloor → 0 ≤ Kfine →
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ v = Q ^ (-3 / 2 : ℝ) ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ ρold : ℝ, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters),
    G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount) →
    let D : OneStepIncoming := {
      stage := H.stage (Fin.last H.eventCount)
      startTime := H.time (Fin.last H.eventCount)
      endTime := s
      startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
      startTime_lt_endTime := G.lt
      slab := G
      terminal := L
      singular := hsing
      parameters := stepParameters }
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, qcan < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2) →
    originalCoreFloor ≤ D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime →
    protectedFloor ≤ D.parameters.protectedRadius D.endTime →
    G.SpatiallyCanonicalBefore εbar C1 C2 qcan s →
    (∀ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t)
      (P : TerminalCorePresentation (D.withNeckRadius ρ hρ) εP Λ),
      Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Q → P.FineCutNecks εcut Q) →
    ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
      (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
      (Antitone D.parameters.neckRadius → Antitone ρ) ∧
      (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
      (HasRecenterConstants.{u} D.parameters →
        HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
      D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
      let D' := D.withNeckRadius ρ hρ
      ∃ P : TerminalCorePresentation D' εP Λ,
        P.coreRadius = D.parameters.delta D.endTime * ρ D.endTime ∧
        qcan < (P.coreRadius ^ 2)⁻¹ ∧
        (P.coreRadius ^ 2)⁻¹ ≤
          max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
            ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max (C * qcan) 0 + 1) / C) ∧
        (∀ x : D.slab.terminalRegularOpen,
          metricScalarAt D.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹ →
            ∃ c ∈ P.component, x ∈ interior (P.core c)) ∧
        (∀ c e, ∃ (p : D.slab.terminalRegularOpen)
          (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
          |level| ≤ 3 ∧ metricScalarAt D.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹ ∧
          ∀ y, P.horn c e (y, 0) = N.map (y, level)) ∧
      ∃ (Qout : OrientedThreeStage.{u})
        (E : MetricCutCapEvent D'.stage Qout D'.startTime D'.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory.{u}) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D'.slab ∧ HEq E.terminal D'.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D'.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D'.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D'.stage ∧ K.time i.castSucc = D'.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D'.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D'.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => D'.parameters.neckRadius D'.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dbig ∧
        parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D'.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D'.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, δOriginal j ≤ 2 * εcut ∧ ⌊εcut⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        (∃ Record : GeometricCutoffRecord K.toHistory i parameters,
          Record.delta = (fun _ => δ) ∧
          Record.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
          HEq Record.neck Nrecord ∧ (∀ j, (Record.neck j).scale = Q) ∧
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
          (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
          Record.DeepNecks_C12X (5 / 4) ∧
          E.poincareStandardDiscarded ∧ (K.toHistory.event i).poincareStandardDiscarded ∧
          (p₀.fixed = fixed → p₀.recenterConstant = recenterConstant →
            p₀.modelOrder = m → p₀.modelAccuracy = accuracy → ηrecord ≤ δold →
            D.parameters.neckRadius D.endTime ≤ ρold →
              K.hasCanonicalCutoffRecords p₀ δold ρold)) ∧
        (∃ Kvol : Set D'.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D'.slab.terminalRegularOpen D'.terminal.metric
            Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_horn_cutoff_record_of_fineCutNecks_of_le_with_radial_coordinates
#guard_msgs (drop warning) in
example :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εcoarse : ℝ, 0 < εcoarse ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy → ∀ ηrecord : ℝ, 0 < ηrecord →
    ∃ δ ε₀ Λq : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < ε₀ ∧ 0 < Λq ∧
    ∀ q0 : ℝ, 0 < q0 →
    ∀ Λmax coreFloor : ℝ, 1 ≤ Λmax → 0 < coreFloor → ∀ Qlower : ℝ,
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ Λq * max q0 1 ≤ Q ∧ Qlower < Q ∧
      v = Q ^ (-3 / 2 : ℝ) ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ ρold : ℝ, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters),
    G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount) →
    let D : OneStepIncoming := {
      stage := H.stage (Fin.last H.eventCount)
      startTime := H.time (Fin.last H.eventCount)
      endTime := s
      startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
      startTime_lt_endTime := G.lt
      slab := G
      terminal := L
      singular := hsing
      parameters := stepParameters }
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q0 < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q0 < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2) →
    ∀ {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ εcoarse →
      ∀ {εc : ℝ}, 0 < εc → εc ≤ ε → εc ≤ ε₀ → P.FineCutNecks εc Q →
      Λ ≤ Λmax → coreFloor ≤ P.coreRadius →
      ∃ (Qout : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory.{u}) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => D.parameters.neckRadius D.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dbig ∧
        parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, δOriginal j ≤ 2 * εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        (∃ Record : GeometricCutoffRecord K.toHistory i parameters,
          Record.delta = (fun _ => δ) ∧
          Record.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
          HEq Record.neck Nrecord ∧ (∀ j, (Record.neck j).scale = Q) ∧
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_horn_cutoff_record_with_volume_debit_of_fineCutNecks
open OneStepIncoming in
#guard_msgs (drop warning) in
example :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (η : ℝ), 0 < η →
    ∃ εP εbar : ℝ, 0 < εP ∧ εP ≤ η ∧ 0 < εbar ∧ εbar < 1 / 11 ∧
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy → ∀ ηrecord : ℝ, 0 < ηrecord →
    ∃ δ εcut : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < εcut ∧ εcut ≤ εP ∧
    ∀ C1 C2 : ℝ, 1 ≤ C2 →
    ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧
    ∀ qcan originalCoreFloor protectedFloor Kfine : ℝ,
      0 < qcan → 0 < originalCoreFloor → 0 < protectedFloor → 0 ≤ Kfine →
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ v = Q ^ (-3 / 2 : ℝ) ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ ρold : ℝ, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters),
    G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount) →
    let D : OneStepIncoming := {
      stage := H.stage (Fin.last H.eventCount)
      startTime := H.time (Fin.last H.eventCount)
      endTime := s
      startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
      startTime_lt_endTime := G.lt
      slab := G
      terminal := L
      singular := hsing
      parameters := stepParameters }
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, qcan < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2) →
    originalCoreFloor ≤ D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime →
    protectedFloor ≤ D.parameters.protectedRadius D.endTime →
    G.SpatiallyCanonicalBefore εbar C1 C2 qcan s →
    (∀ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t)
      (P : TerminalCorePresentation (D.withNeckRadius ρ hρ) εP Λ),
      Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Q → P.FineCutNecks εcut Q) →
    ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
      (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
      (Antitone D.parameters.neckRadius → Antitone ρ) ∧
      (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
      (HasRecenterConstants.{u} D.parameters →
        HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
      D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
      let D' := D.withNeckRadius ρ hρ
      ∃ P : TerminalCorePresentation D' εP Λ,
        P.coreRadius = D.parameters.delta D.endTime * ρ D.endTime ∧
        qcan < (P.coreRadius ^ 2)⁻¹ ∧
        (P.coreRadius ^ 2)⁻¹ ≤
          max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
            ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max (C * qcan) 0 + 1) / C) ∧
        (∀ x : D.slab.terminalRegularOpen,
          metricScalarAt D.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹ →
            ∃ c ∈ P.component, x ∈ interior (P.core c)) ∧
        (∀ c e, ∃ (p : D.slab.terminalRegularOpen)
          (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
          |level| ≤ 3 ∧ metricScalarAt D.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹ ∧
          ∀ y, P.horn c e (y, 0) = N.map (y, level)) ∧
      ∃ (Qout : OrientedThreeStage.{u})
        (E : MetricCutCapEvent D'.stage Qout D'.startTime D'.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory.{u}) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D'.slab ∧ HEq E.terminal D'.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D'.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D'.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D'.stage ∧ K.time i.castSucc = D'.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D'.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D'.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => D'.parameters.neckRadius D'.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dbig ∧
        parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D'.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D'.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, δOriginal j ≤ 2 * εcut ∧ ⌊εcut⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        (∃ Record : GeometricCutoffRecord K.toHistory i parameters,
          Record.delta = (fun _ => δ) ∧
          Record.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
          HEq Record.neck Nrecord ∧ (∀ j, (Record.neck j).scale = Q) ∧
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
          E.poincareStandardDiscarded ∧ (K.toHistory.event i).poincareStandardDiscarded ∧
          (p₀.fixed = fixed → p₀.recenterConstant = recenterConstant →
            p₀.modelOrder = m → p₀.modelAccuracy = accuracy → ηrecord ≤ δold →
            D.parameters.neckRadius D.endTime ≤ ρold →
              K.hasCanonicalCutoffRecords p₀ δold ρold)) ∧
        (∃ Kvol : Set D'.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D'.slab.terminalRegularOpen D'.terminal.metric
            Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) :=
  @_root_.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_horn_cutoff_record_of_fineCutNecks_of_le
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

-- RF.Surgery.Topology.UniformScaffoldSurgeryStep  [VERBATIM, PEND]
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example :
    type_of% @exists_uniform_scaffold_surgery_step_with_radial_coordinates_with_distance_scalars :=
  @exists_uniform_scaffold_surgery_step_with_radial_coordinates_with_distance_scalars
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_uniform_scaffold_surgery_step_with_radial_coordinates :=
  @exists_uniform_scaffold_surgery_step_with_radial_coordinates
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_uniform_scaffold_surgery_step := @exists_uniform_scaffold_surgery_step
end
