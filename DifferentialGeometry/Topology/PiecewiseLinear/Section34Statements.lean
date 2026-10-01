import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def Section34ControlStatement : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [Nonempty M₁] [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)] {U : Set M₁}, IsOpen U →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (U.domRestrict h) →
    ∀ η : M₁ → ℝ, ContinuousOn η U → (∀ x ∈ U, 0 < η x) →
    ∃ (N : ℕ) (𝒦 : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin N)) 3 M₁ U)
      (H : Finset (EuclideanSpace ℝ (Fin N)) → Set M₂),
      IsCombinatorialManifold 3 𝒦.complex ∧ Section34CarrierControl U 𝒦 h η H

end DifferentialGeometry.Topology.PiecewiseLinear
