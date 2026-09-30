import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureDerivativeFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelExistenceClean

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem high_curvature_derivatives_of_windowedWitnessJetTransfer_and_universalMixedJetBound
    {a b : ℕ} {C eta : ℝ} (hC : 0 < C) (heta : 0 < eta)
    (hmodel : HighCurvatureModelWitnessExistence.{u})
    (htransfer : WindowedWitnessJetTransfer.{u} a b eta)
    (hU : DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.UniversalMixedJetBound.{u}
      a b C) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧ JetLocalBound.{u} a b C eta :=
  exists_jetLocalBound_of_modelWitnessExistence_and_transfer hC heta hmodel htransfer
    (ancientModelMixedBound_of_universalMixedJetBound a b hU)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
