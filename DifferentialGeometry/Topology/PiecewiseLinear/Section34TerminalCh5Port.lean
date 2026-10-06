import DifferentialGeometry.Topology.PiecewiseLinear.Section34Terminal

/-!
Ch5 port (P0-PORT): the ch5 workbench (baseline b0f2c40,
`Approximation/CellDecomposition/Existence.lean`) states the controlled cell decomposition as
the theorem `exists_controlled_cell_decomposition`; dg-ch15 packages the same statement as the
`Prop` `Section34CellDiagram` with producer `section34CellDiagram`. This file exposes the ch5
name, proved from the dg-ch15 producer.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_controlled_cell_decomposition
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h)) (η : M₁ → ℝ)
    (hηc : ContinuousOn η U) (hηpos : ∀ x ∈ U, 0 < η x) :
    ∃ (Λ : Type u) (dim : Λ → ℕ) (face : Λ → Set Λ)
      (P Q : Λ → Set (EuclideanSpace ℝ (Fin 3)))
      (r : (l : Λ) → (Fin (dim l + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
      (s : (l : Λ) → (Fin (dim l + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
      (u : Λ → EuclideanSpace ℝ (Fin 3) → M₁) (v : Λ → EuclideanSpace ℝ (Fin 3) → M₂)
      (sourceCell : Λ → Set M₁) (targetCell : Λ → Set M₂) (carrier : Λ → Set M₂),
      (∀ l, dim l ≤ 3) ∧
      (∀ l, IsPLHomeomorphOn (r l) (Convexity.StdSimplex.coordinateSet ℝ (Fin (dim l + 1))) (P l)) ∧
      (∀ l, IsPLHomeomorphOn (s l) (Convexity.StdSimplex.coordinateSet ℝ (Fin (dim l + 1))) (Q l)) ∧
      (∀ l, IsPLHomeomorphInto 3 (u l) (P l)) ∧ (∀ l, IsPLHomeomorphInto 3 (v l) (Q l)) ∧
      (∀ l, sourceCell l = u l '' P l) ∧ (∀ l, targetCell l = v l '' Q l) ∧
      (∀ l m, m ∈ face l → m = l ∨ dim m < dim l) ∧
      (∀ l, u l '' (r l '' stdSimplexBoundary (dim l)) = ⋃ m ∈ face l \ {l}, sourceCell m) ∧
      (∀ l, v l '' (s l '' stdSimplexBoundary (dim l)) = ⋃ m ∈ face l \ {l}, targetCell m) ∧
      (∀ l m, sourceCell l ∩ sourceCell m = ⋃ k ∈ face l ∩ face m, sourceCell k) ∧
      (∀ l m, targetCell l ∩ targetCell m = ⋃ k ∈ face l ∩ face m, targetCell k) ∧
      (∀ x ∈ ⋃ l, sourceCell l, ∃ W ∈ 𝓝 x, {l | (sourceCell l ∩ W).Nonempty}.Finite) ∧
      (∀ y ∈ ⋃ l, targetCell l, ∃ W ∈ 𝓝 y, {l | (targetCell l ∩ W).Nonempty}.Finite) ∧
      (⋃ l, sourceCell l) = U ∧
      (∀ l, h '' sourceCell l ∪ targetCell l ⊆ carrier l) ∧
      ∀ l, ∀ x ∈ sourceCell l, ∀ y ∈ carrier l, ∀ z ∈ carrier l, dist y z < η x :=
  section34CellDiagram hU hh η hηc hηpos

end DifferentialGeometry.Topology.PiecewiseLinear
