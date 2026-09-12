import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RiemannFromRicci
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

structure MixedCurvatureJet (S : SolutionOn (I := I3) (M := M) D) where
  value : ∀ a : ℕ, ℕ → ℝ → Tensor0SField (I := I3) (M := M) (n := ∞) (a + 4)
  spatial : ∀ a t, value a 0 t = curvCovDeriv (I := I3) (S.base.metric t) a
  time : ∀ a b t, t ∈ D.carrier → ∀ x (v : Fin (a + 4) → TangentSpace I3 x),
    value a (b + 1) t x v = derivWithin (fun s => value a b s x v) (D.carrier ∩ Set.Iic t) t +
      ∑ j : Fin (a + 4), value a b t x (Function.update v j
        (ricciEndAt (S.base.metric t) (metricRicciAt (S.base.metric t) x) (v j)))

def MixedCurvatureJet.norm {S : SolutionOn (I := I3) (M := M) D}
    (J : MixedCurvatureJet S) (a b : ℕ) (t : ℝ) (x : M) : ℝ :=
  Real.sqrt (normSq0S (I := I3) (S.base.metric t) x (a + 4) (J.value a b t x))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
