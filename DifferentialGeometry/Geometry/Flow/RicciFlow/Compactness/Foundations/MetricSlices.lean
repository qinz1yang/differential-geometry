import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

def PointedCGHMaps.atTimeWithMetric
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps X P phi) (t : ℝ) (g : SmoothRiemannianMetric I P.M) :
    PointedRiemannianConvergenceMaps (X.atTime t)
      ({ P with metric := g } : PointedRiemannianManifold (I := I)) phi where
  partialDiffeomorph k := Phi.partialDiffeomorph k
  source_exhausts := Phi.source_exhausts
  base_mem k := Phi.base_mem k
  basepoint_map k := Phi.basepoint_map k

end DifferentialGeometry.CheegerGromovCompactness

end
