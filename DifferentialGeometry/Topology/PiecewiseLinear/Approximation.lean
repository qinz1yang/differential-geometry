import DifferentialGeometry.Topology.PiecewiseLinear.Groupoid
import DifferentialGeometry.Topology.Manifold.PartialAtlas

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.Manifold (AtlasOn)

universe u

def PLApproximation (n : ℕ) : Prop :=
  ∀ {X₁ X₂ : Type u} [TopologicalSpace X₁] [T2Space X₁] [SecondCountableTopology X₁]
    [MetricSpace X₂] [SecondCountableTopology X₂] {O₁ : Set X₁} {O₂ : Set X₂}
    (A : AtlasOn (plGroupoid n) O₁) (B : AtlasOn (plGroupoid n) O₂)
    (h : OpenPartialHomeomorph X₁ X₂), h.source = O₁ → h.target = O₂ →
    ∀ φ : X₁ → ℝ, ContinuousOn φ O₁ → (∀ x ∈ O₁, 0 < φ x) →
    ∃ f : OpenPartialHomeomorph X₁ X₂, f.source = O₁ ∧ f.target = O₂ ∧
      (∀ x ∈ O₁, dist (f x) (h x) < φ x) ∧
      ∀ e ∈ A.charts, ∀ e' ∈ B.charts, e.symm ≫ₕ f ≫ₕ e' ∈ plGroupoid n

end DifferentialGeometry.Topology.PiecewiseLinear
