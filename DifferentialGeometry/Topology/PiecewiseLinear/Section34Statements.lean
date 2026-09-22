/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

/-!
# The two intermediate endpoints of Section 34

`Section34ControlStatement` is the endpoint of the P0 skeleton: for an open subset `U` of a
nonempty piecewise linear `3`-manifold, an embedding `h` of `U` and a continuous positive scale
`η` on `U`, a locally finite triangulation of `U` realised in some `ℝ^N` whose complex is a
combinatorial `3`-manifold, together with a carrier system satisfying
`Section34CarrierControl`.  `ControlledGraphNeighborhoodStatement` is the endpoint of the
controlled form of Moise 35.1: it takes exactly those two objects as hypotheses and produces
the cut frame and the graph frame of Section 34.

Both statements are proved in skeleton files from `sorry` leaves; skeletons cannot be imported,
so the statements live here, as named propositions, for the skeletons that consume them as
hypotheses.  The text of each definition is the text frozen by external review; `M₁` is
required nonempty in the first because `LocallyFinitePLPieceIn` has a total realisation map,
and not in the second because the triangulation is one of its inputs.
-/

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
