import DifferentialGeometry.Topology.Homology.PathChains



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {x y : X}



theorem integralPathSimplex_apply (p : Path x y) (t : stdSimplex ℝ (Fin 2)) :
    integralSingularSimplexEquiv 1 X (integralPathSimplex p) t =
      p (stdSimplexHomeomorphUnitInterval t) := by
  exact congrArg (fun f : C(stdSimplex ℝ (Fin 2), X) => f t)
    ((integralSingularSimplexEquiv 1 X).apply_symm_apply
      (p.toContinuousMap.comp ⟨stdSimplexHomeomorphUnitInterval,
        stdSimplexHomeomorphUnitInterval.continuous⟩))

end DifferentialGeometry.Topology
