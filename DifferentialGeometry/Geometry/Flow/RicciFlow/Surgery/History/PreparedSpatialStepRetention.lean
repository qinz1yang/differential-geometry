import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordModelRestriction.Basic

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal
namespace GC.GeneralFlow
universe u

/-- The actual fine records and old native extension selected by one prepared step. -/
structure PreparedSpatialStepRetention
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext : ℝ}
    (L : PreparedSpatialState pBase C P g E B)
    (R : PreparedSpatialState pBase C P g B Bnext)
    (d eta εcut Dcut : ℝ) (mcut : ℕ) where
  fineParameters : CutoffParameters
  fineRecords : ∀ i : Fin R.native.eventCount,
    GeometricCutoffRecord R.native.toHistory i fineParameters
  fineWindows : ∀ i b, ((fineRecords i).static b).hasCanonicalWindow
  fineLinked : ∀ i b, ((fineRecords i).static b).hasLinkedCanonicalWindow_C12X
  fine_fixed : fineParameters.fixed = pBase.fixed
  fine_recenter : fineParameters.recenterConstant = pBase.recenterConstant
  fine_accuracy : fineParameters.modelAccuracy ≤ εcut
  fine_radius : Dcut ≤ fineParameters.modelRadius
  fine_order : mcut ≤ fineParameters.modelOrder
  fine_cutoff : ∀ i : Fin R.native.eventCount,
    fineParameters.delta (R.native.time i.succ) ≤ d ∧
      fineParameters.neckRadius (R.native.time i.succ) ≤ min R.radius (eta * R.radius)
  full_radius : L.parameters.modelRadius ≤ fineParameters.modelRadius
  full_order : L.parameters.modelOrder ≤ fineParameters.modelOrder
  full_accuracy : fineParameters.modelAccuracy ≤ L.parameters.modelAccuracy
  reserve_radius : R.prepared.parameters.modelRadius ≤ fineParameters.modelRadius
  reserve_order : R.prepared.parameters.modelOrder ≤ fineParameters.modelOrder
  reserve_accuracy : fineParameters.modelAccuracy ≤ R.prepared.parameters.modelAccuracy
  native_parameters : R.nativeParameters =
    fineParameters.withModelWindow R.prepared.parameters.modelRadius
      R.prepared.parameters.modelOrder R.prepared.parameters.modelAccuracy
      R.prepared.parameters.modelRadius_pos
      (fineParameters.modelAccuracy_pos.trans_le reserve_accuracy)
  native_records : ∀ i : Fin R.native.eventCount,
    HEq (R.nativeRecords i)
      ((fineRecords i).restrictModelWindow (fineWindows i)
        R.prepared.parameters.modelRadius_pos reserve_radius reserve_order reserve_accuracy)
  full_records : ∀ i : Fin R.native.eventCount,
    HEq (R.records (R.affine.eventIndex i)).nominalRadius (fineRecords i).nominalRadius ∧
    HEq (R.records (R.affine.eventIndex i)).delta (fineRecords i).delta ∧
    HEq (R.records (R.affine.eventIndex i)).order (fineRecords i).order ∧
    HEq (R.records (R.affine.eventIndex i)).neck (fineRecords i).neck ∧
    HEq (R.records (R.affine.eventIndex i)).static
      (fun z => translate_presented_static_cap (R.native.coreEvent i) R.shift
        (((fineRecords i).restrictModelWindow (fineWindows i)
          L.parameters.modelRadius_pos full_radius full_order full_accuracy).static z))
  oldNative : RetainedCoreHistory.{u}
  oldNativeInitial : InitialIdentification L.nativeStage L.nativeMetric oldNative.toHistory
  oldNativeParameters : CutoffParameters
  oldNativeRecords : ∀ i : Fin oldNative.eventCount,
    GeometricCutoffRecord oldNative.toHistory i oldNativeParameters
  oldNativeAffine : AffineEventPrefix R.native oldNative
    (L.native.time (Fin.last L.native.eventCount)) L.native.eventCount
    (Fin.last R.native.eventCount)
  oldNativeRawPrefix : RawInitialPrefix L.native oldNative
  oldNativeInitial_prefix : L.nativeInitial.IsPrefixOf oldNativeInitial
  oldNative_horizon : oldNative.horizon = B - L.shift
  oldNative_horizon_affine : oldNative.horizon =
    R.native.horizon + L.native.time (Fin.last L.native.eventCount)
  oldNative_class : oldNative.IsCanonicalCutoffRecordFamily L.prepared.parameters
    L.prepared.deltaBound L.prepared.radiusBound oldNativeRecords
  oldNative_finalMetric : ∀ t : ℝ,
    HEq (oldNative.toHistory.stageMetric (Fin.last oldNative.eventCount)
      (t + L.native.time (Fin.last L.native.eventCount)))
      (R.native.toHistory.stageMetric (Fin.last R.native.eventCount) t)
  oldNative_records_preserved : ∀ i : Fin L.native.eventCount,
    HEq (oldNativeRecords (i.castLE oldNativeRawPrefix.count_le)).nominalRadius
      (L.nativeRecords i).nominalRadius ∧
    HEq (oldNativeRecords (i.castLE oldNativeRawPrefix.count_le)).delta
      (L.nativeRecords i).delta ∧
    HEq (oldNativeRecords (i.castLE oldNativeRawPrefix.count_le)).order
      (L.nativeRecords i).order ∧
    HEq (oldNativeRecords (i.castLE oldNativeRawPrefix.count_le)).neck
      (L.nativeRecords i).neck ∧
    HEq (oldNativeRecords (i.castLE oldNativeRawPrefix.count_le)).static
      (L.nativeRecords i).static
  oldNative_estimates :
    NativeEstimates oldNative C.epsilon C.C1 C.C2 C.C1s C.C2s
      L.prepared.qcan L.prepared.qs C.tauMin C.Ctime C.Cgrad

end GC.GeneralFlow
