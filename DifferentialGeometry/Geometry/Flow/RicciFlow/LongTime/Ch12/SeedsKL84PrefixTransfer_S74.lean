import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86CnSlice_S63
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TraceRestrictionBack_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86RmBoundSlice_O22

/-!
# CH12-S74: static input (s2) on the slice's tower history over the whole earlier prefix

`rm_bound_prefix_S74`: (b3) `|Rm| ≤ C·Mb` wherever `R ≤ Mb`, `1 ≤ Mb` on the same prefix.
`canonical_prefix_S74`: `Hp.canonical` holds on `N.stageMetric (N.activeStage v) v` for every
`v ≤ s.time` (R4 D-R4-5 (2)), `N := sliceTowerHistory_CX2 s`; obtained from the slice form
`slice_canonical_S63` through the identification `s.history = N.restrict …`
(`restrict_stageAt`, `restrict_sliceMetric`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem canonical_prefix_core_S74 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    (v : Icc (0 : ℝ) s.history.horizon) :
    ∀ x : ((sliceTowerHistory_CX2 s).stage ((sliceTowerHistory_CX2 s).activeStage
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) v))).Carrier,
      (Hp.parameters.neckRadius v ^ 2)⁻¹ <
        metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage
          (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) v))
          (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) v)) x →
      Nonempty (SpatialCanonicalWitness ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage
          (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) v))
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) v))
        Hp.epsilon Hp.C1 Hp.C2 x) := by
  set N := sliceTowerHistory_CX2 s
  set cut := sliceTowerTime_CX2 s
  have hst : s.history.stage (s.history.activeStage v) =
      N.stage (N.activeStage (restrictTime_CX2 N cut v)) := N.restrict_stageAt cut v
  have hm : HEq (s.history.stageMetric (s.history.activeStage v) v)
      (N.stageMetric (N.activeStage (restrictTime_CX2 N cut v)) (restrictTime_CX2 N cut v)) :=
    N.restrict_sliceMetric cut v
  exact stageMetric_transport_O3 hst hm
    (fun Q m => ∀ x : Q.Carrier, (Hp.parameters.neckRadius v ^ 2)⁻¹ < metricScalarAt m x →
      Nonempty (SpatialCanonicalWitness m Hp.epsilon Hp.C1 Hp.C2 x))
    (slice_canonical_S63 Hp s v)

/-- (s2) on the tower history over the whole prefix `v ≤ s.time`. -/
theorem canonical_prefix_S74 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hvs : (v : ℝ) ≤ s.time) :
    ∀ x : ((sliceTowerHistory_CX2 s).stage ((sliceTowerHistory_CX2 s).activeStage v)).Carrier,
      (Hp.parameters.neckRadius v ^ 2)⁻¹ <
        metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v) x →
      Nonempty (SpatialCanonicalWitness ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) Hp.epsilon Hp.C1 Hp.C2 x) := by
  obtain ⟨v1, h0, h1⟩ := v
  exact canonical_prefix_core_S74 Hp s ⟨v1, h0, hvs⟩

/-- (b3) on the tower history over the whole prefix `v ≤ s.time`, one constant `C` for all slices. -/
theorem rm_bound_prefix_S74 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : RegularSlice F.observation)
      (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), (v : ℝ) ≤ s.time →
      ∀ (x : ((sliceTowerHistory_CX2 s).stage ((sliceTowerHistory_CX2 s).activeStage v)).Carrier)
        (Mb : ℝ), 1 ≤ Mb →
      metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) x ≤ Mb →
      Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) x 4
        (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v) x)) ≤ C * Mb := by
  obtain ⟨C, hC, hb⟩ := slice_rm_bound_of_scalar_O22 Hp
  refine ⟨C, hC, fun s v hvs => ?_⟩
  obtain ⟨v1, h0, h1⟩ := v
  set N := sliceTowerHistory_CX2 s
  set cut := sliceTowerTime_CX2 s
  let v' : Icc (0 : ℝ) s.history.horizon := ⟨v1, h0, hvs⟩
  have hst : s.history.stage (s.history.activeStage v') =
      N.stage (N.activeStage (restrictTime_CX2 N cut v')) := N.restrict_stageAt cut v'
  have hm : HEq (s.history.stageMetric (s.history.activeStage v') v')
      (N.stageMetric (N.activeStage (restrictTime_CX2 N cut v')) (restrictTime_CX2 N cut v')) :=
    N.restrict_sliceMetric cut v'
  exact stageMetric_transport_O3 hst hm
    (fun Q m => ∀ (x : Q.Carrier) (Mb : ℝ), 1 ≤ Mb → metricScalarAt m x ≤ Mb →
      Real.sqrt (normSq0S m x 4 (metricRm04At m x)) ≤ C * Mb)
    (hb s v' hvs)

end GC.LongTime.Ch12
