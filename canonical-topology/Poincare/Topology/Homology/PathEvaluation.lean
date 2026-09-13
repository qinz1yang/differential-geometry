import Poincare.Topology.Homology.PathChains

/-! # Evaluation of the same original path simplex -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap
open scoped Simplicial Topology

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X] {x y : X}

/-- The actual singular path simplex evaluates the original path at the
original barycentric interval parameter. -/
theorem integralPathSimplex_apply (p : Path x y) (t : stdSimplex ℝ (Fin 2)) :
    integralSingularSimplexEquiv 1 X (integralPathSimplex p) t =
      p (stdSimplexHomeomorphUnitInterval t) := by
  exact congrArg (fun f : C(stdSimplex ℝ (Fin 2), X) => f t)
    ((integralSingularSimplexEquiv 1 X).apply_symm_apply
      (p.toContinuousMap.comp ⟨stdSimplexHomeomorphUnitInterval,
        stdSimplexHomeomorphUnitInterval.continuous⟩))

end Poincare.Topology
