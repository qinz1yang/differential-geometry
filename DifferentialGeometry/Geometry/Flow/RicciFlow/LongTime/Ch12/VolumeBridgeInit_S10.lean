import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeEvent_S10
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Covering

set_option autoImplicit false
noncomputable section
open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

theorem initial_volume_eq_S10 {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}
    (A : InitialIdentification P g H) :
    riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0) univ =
      riemannianVolumeMeasure ThreeModel P.Carrier g univ := by
  have hp : IsLocalDiffeomorph ThreeModel ThreeModel ∞ A.map := A.map.isLocalDiffeomorph
  have hpull : localPullMetric (H.initialMetric 0) A.map hp = g := by
    refine SmoothRiemannianMetric.ext_inner fun x v w => ?_
    rw [localPullMetric_inner]
    exact A.metric_eq x v w
  let : MeasurableSpace P.Carrier := borel P.Carrier
  let : BorelSpace P.Carrier := ⟨rfl⟩
  let : MeasurableSpace (H.stage 0).Carrier := borel _
  let : BorelSpace (H.stage 0).Carrier := ⟨rfl⟩
  have hm := riemannianVolumeMeasure_map_eq_natCast_smul_of_localPullMetric
    g (H.initialMetric 0) hp hpull 1 (fun y => by
      have : {x | A.map x = y} = {A.map.symm y} := by
        ext x
        simp only [mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩
      rw [this]; simp)
  have h := congrArg (fun μ : Measure (H.stage 0).Carrier => μ univ) hm
  rw [Measure.map_apply A.map.continuous.measurable MeasurableSet.univ, preimage_univ] at h
  simpa using h.symm

end GC.LongTime.Ch12
