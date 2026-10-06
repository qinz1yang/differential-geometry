import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportEdge74
import DifferentialGeometry.Topology.Embedding.CrossModelHalfSpaceOCX
import DifferentialGeometry.Topology.Handle.Manifold

/-!
# Draft 74, D74-6: smooth embeddings followed by a carrier diffeomorphism of ANY kinds

Lane O-CROSS (G1 consumer, base of G3). `isSmoothEmbedding_comp_carrier_R74` (lane
C14-REG-CHAIN) needs `W₀.kind = W₁.kind`; with the cross-model kernels of
`CrossModelHalfSpaceOCX` the four kind pairs are covered:

* same kind: `IsSmoothEmbedding.diffeomorph_comp` (one model);
* `closed → withBoundary` (`𝓡 3 → 𝓡∂ 3`): HARD direction
  `IsSmoothEmbedding.diffeomorph_comp_toHalfSpace_OCX` (needs a nonzero range-preserving
  translation `s₀` of the source model);
* `withBoundary → closed` (`𝓡∂ 3 → 𝓡 3`): EASY direction
  `IsSmoothEmbedding.diffeomorph_comp_fromHalfSpace_OCX`.

`isSmoothEmbedding_comp_carrier_cross_R74` is the general statement and
`isSmoothEmbedding_comp_carrier_cross_disk_R74` the case of the closed disk `ClosedCell 2`
(model `𝓡∂ 2`, translation `e₁` along the boundary) used by `EdgeBundle.fibre_disk`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

variable {W₀ W₁ : CompactCarrier.{u}}

/-- **A smooth embedding followed by a carrier diffeomorphism, carriers of any kinds** (the source
model has a nonzero translation `s₀` preserving its range, used only from a closed carrier to a
carrier with boundary). -/
theorem isSmoothEmbedding_comp_carrier_cross_R74 {EQ HQ : Type*} [NormedAddCommGroup EQ]
    [NormedSpace ℝ EQ] [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ} {Q : Type*}
    [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold IQ ∞ Q] (s₀ : EQ) (hs₀ : s₀ ≠ 0)
    (hs₀I : ∀ v, v + s₀ ∈ range IQ ↔ v ∈ range IQ)
    (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {φ : Q → W₀.Carrier} (hφ : IsSmoothEmbedding IQ W₀.model ∞ φ) :
    IsSmoothEmbedding IQ W₁.model ∞ (e ∘ φ) := by
  cases W₀ with
  | mk k₀ M₀ o₀ =>
    cases W₁ with
    | mk k₁ M₁ o₁ =>
      cases k₀ <;> cases k₁
      · exact hφ.diffeomorph_comp e
      · exact hφ.diffeomorph_comp_toHalfSpace_OCX s₀ hs₀ hs₀I e
      · exact hφ.diffeomorph_comp_fromHalfSpace_OCX e
      · exact hφ.diffeomorph_comp e

local instance diskCharts_OCX : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_OCX : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- **The edge-bundle case**: a smooth embedding of the closed disk followed by a carrier
diffeomorphism of any kinds. -/
theorem isSmoothEmbedding_comp_carrier_cross_disk_R74
    (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {φ : ClosedCell 2 → W₀.Carrier} (hφ : IsSmoothEmbedding (𝓡∂ 2) W₀.model ∞ φ) :
    IsSmoothEmbedding (𝓡∂ 2) W₁.model ∞ (e ∘ φ) := by
  have hs₀ : (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
    simp at h1
  have hs₀I : ∀ v : EuclideanSpace ℝ (Fin 2),
      v + EuclideanSpace.single 1 1 ∈ range (𝓡∂ 2) ↔ v ∈ range (𝓡∂ 2) := by
    intro v
    rw [range_modelWithCornersEuclideanHalfSpace]
    simp
  exact isSmoothEmbedding_comp_carrier_cross_R74 (IQ := 𝓡∂ 2) _ hs₀ hs₀I e hφ

/-- Consistency with the same-kind lemma of lane C14-REG-CHAIN. -/
example (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier) (hk : W₀.kind = W₁.kind)
    {φ : ClosedCell 2 → W₀.Carrier} (hφ : IsSmoothEmbedding (𝓡∂ 2) W₀.model ∞ φ) :
    IsSmoothEmbedding (𝓡∂ 2) W₁.model ∞ (e ∘ φ) ∧
      IsSmoothEmbedding (𝓡∂ 2) W₁.model ∞ (e ∘ φ) :=
  ⟨isSmoothEmbedding_comp_carrier_R74 e hk hφ, isSmoothEmbedding_comp_carrier_cross_disk_R74 e hφ⟩

end GC.GraphManifold.Assembly
