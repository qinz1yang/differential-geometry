import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

structure SmoothCompatibleAtlas (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Type*) [TopologicalSpace X] (ι : Type*) where
  chart : ι → OpenPartialHomeomorph X E
  mem_source : ∀ x, ∃ i, x ∈ (chart i).source
  contDiffOn_transition : ∀ i j,
    ContDiffOn ℝ ∞ ((chart i).symm.trans (chart j)) ((chart i).symm.trans (chart j)).source

def SmoothCompatibleAtlas.IsCompatible {E X ι ι' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] (A : SmoothCompatibleAtlas E X ι)
    (φ : ι' → OpenPartialHomeomorph X E) (r : ℕ) : Prop :=
  ∀ i j,
    ContDiffOn ℝ r ((φ i).symm.trans (A.chart j)) ((φ i).symm.trans (A.chart j)).source ∧
      ContDiffOn ℝ r ((A.chart j).symm.trans (φ i)) ((A.chart j).symm.trans (φ i)).source

end DifferentialGeometry.Topology.Manifold
