import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialState

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace GC.GeneralFlow
universe u

/-- Four bounds retained on the same class before radius and fine-quality requests. -/
def ClosedBirthPreparedClass.HasReserveQuality
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {B : ℝ}
    (prepared : ClosedBirthPreparedClass pBase C P g B)
    (Dstar εReserve : ℝ) : Prop :=
  Dstar ≤ prepared.parameters.modelRadius ∧
  prepared.parameters.modelAccuracy ≤ εReserve ∧
  2 ≤ prepared.parameters.modelOrder ∧
  32 * prepared.Qall * prepared.radiusBound ^ 2 ≤ 1

/-- Transport all four bounds through the full dependent identity of the same class. -/
private theorem reserve_quality_of_same_prepared_class
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {Dstar εReserve : ℝ}
    {P Q : OrientedThreeStage.{u}} {g : P.Metric} {g' : Q.Metric} {B B' : ℝ}
    {K : ClosedBirthPreparedClass pBase C P g B}
    {K' : ClosedBirthPreparedClass pBase C Q g' B'}
    (hP : P = Q) (hg : HEq g g') (hB : B = B') (hK : HEq K K')
    (h : K.HasReserveQuality Dstar εReserve) : K'.HasReserveQuality Dstar εReserve := by
  cases hP
  cases (eq_of_heq hg)
  cases hB
  cases (eq_of_heq hK)
  exact h

end GC.GeneralFlow
