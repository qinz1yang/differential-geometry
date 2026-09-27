/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
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

def ControlledGraphNeighborhoodStatement : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)] {U : Set M₁}, IsOpen U →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (U.domRestrict h) →
    ∀ (Ea : Type) [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
      (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U), IsCombinatorialManifold 3 𝒦.complex →
    ∀ (η : M₁ → ℝ) (H : Finset Ea → Set M₂), Section34CarrierControl U 𝒦 h η H →
    ∀ {W : Set M₁}, IsOpen W → graphSkeletonSpace 𝒦 ⊆ W → W ⊆ U →
    ∀ ψ : M₁ → ℝ, ContinuousOn ψ U → (∀ x ∈ U, 0 < ψ x) →
    ∃ (𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea) (f₁ : M₁ → M₂),
      Section34CutFrame U 𝒦 𝒦' src srcBd ∧
        Section34GraphFrame U W h ψ H 𝒦 𝒦' src car f₁

end DifferentialGeometry.Topology.PiecewiseLinear
