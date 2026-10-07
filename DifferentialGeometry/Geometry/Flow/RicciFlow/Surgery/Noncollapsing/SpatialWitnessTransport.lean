import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal
namespace GC.GeneralFlow
universe u

private def overlapCastPoint {P Q : OrientedThreeStage.{u}}
    (h : P = Q) (x : P.Carrier) : Q.Carrier := h ▸ x

private theorem overlapCastPoint_heq {P Q : OrientedThreeStage.{u}}
    (h : P = Q) (x : P.Carrier) : HEq (overlapCastPoint h x) x := by
  cases h
  exact HEq.rfl

private theorem overlap_scalar_eq {P Q : OrientedThreeStage.{u}}
    (h : P = Q) {g : P.Metric} {g' : Q.Metric} (hg : HEq g g')
    {x : P.Carrier} {y : Q.Carrier} (hx : HEq x y) :
    metricScalarAt g x = metricScalarAt g' y := by
  cases h
  cases eq_of_heq hg
  cases eq_of_heq hx
  rfl

/-- Equality of the actual stage, metric and point transports the whole spatial
witness, including its neck-chart assertion. The returned witness is HEq to
the supplied witness; no new geometric producer is used. -/
private theorem overlap_spatialWitness_transport {P Q : OrientedThreeStage.{u}}
    (h : P = Q) {g : P.Metric} {g' : Q.Metric} (hg : HEq g g')
    {x : P.Carrier} {y : Q.Carrier} (hx : HEq x y)
    {ε C1 C2 : ℝ} (W : SpatialCanonicalWitness g ε C1 C2 x)
    (hW : W.capTubeHasNeckChart ε) :
    ∃ W' : SpatialCanonicalWitness g' ε C1 C2 y,
      W'.capTubeHasNeckChart ε ∧ HEq W' W := by
  cases h
  cases eq_of_heq hg
  cases eq_of_heq hx
  exact ⟨W, hW, HEq.rfl⟩

end GC.GeneralFlow
