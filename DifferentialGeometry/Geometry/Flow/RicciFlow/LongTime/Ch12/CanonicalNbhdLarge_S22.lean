import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCurvHI_S20

/-!
# CH12-S22 / K2 (KL84.1(b)) : profile part

The profile field `canonical` covers only `R > neckRadius(t)⁻²`.  Hence K2 (canonical
neighbourhoods for `R ≥ C(L)/t` on `B(p, L√t)`) splits into this proved range and the
intermediate range `C(L)/t ≤ R ≤ neckRadius(t)⁻²`, which is the genuine KL84.1(b) content.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

/-- Profile canonical neighbourhood transferred to a regular slice, above the profile threshold. -/
theorem slice_canonical_above_neck_S22 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (y : s.stage.Carrier)
    (hy : (H.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric y) :
    ∃ W : SpatialCanonicalWitness s.metric H.epsilon H.C1 H.C2 y,
      W.capTubeHasNeckChart H.epsilon := by
  have key : ∀ (Y : OrientedThreeStage.{u}) (hY : postStage F.observation s.time = Y)
      (m : Y.Metric), HEq (postMetric F.observation s.time) m → ∀ z : Y.Carrier,
      (H.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt m z →
      ∃ W : SpatialCanonicalWitness m H.epsilon H.C1 H.C2 z,
        W.capTubeHasNeckChart H.epsilon := by
    intro Y hY m hm z hz
    subst hY
    have := eq_of_heq hm
    subst this
    exact H.canonical s.time s.positive.le z hz
  exact key s.stage (postStage_regularSlice F.observation s) s.metric
    (postMetric_regularSlice F.observation s) y hy

/-- Splitting: K2 follows from the intermediate range (the genuine KL84.1(b) statement). -/
theorem k2_of_intermediate_S22 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (y : s.stage.Carrier) {Q : ℝ}
    (hmid : metricScalarAt s.metric y ≤ (H.parameters.neckRadius s.time ^ 2)⁻¹ →
      Q ≤ metricScalarAt s.metric y →
      ∃ W : SpatialCanonicalWitness s.metric H.epsilon H.C1 H.C2 y,
        W.capTubeHasNeckChart H.epsilon)
    (hQ : Q ≤ metricScalarAt s.metric y) :
    ∃ W : SpatialCanonicalWitness s.metric H.epsilon H.C1 H.C2 y,
      W.capTubeHasNeckChart H.epsilon := by
  by_cases h : (H.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric y
  · exact slice_canonical_above_neck_S22 H s y h
  · exact hmid (not_lt.mp h) hQ

end GC.LongTime.Ch12
