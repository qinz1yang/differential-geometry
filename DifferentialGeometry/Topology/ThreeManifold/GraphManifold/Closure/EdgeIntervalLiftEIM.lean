import DifferentialGeometry.Topology.Embedding.CrossModelHalfSpaceOCX
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier

/-!
# E3 kernel, part 2: an embedded disk in a carrier interior, with the interior charts (lane
# S-EDGE-INT2)

Draft 74, package E3. A smooth embedding `φ : X → W.Carrier` (`X` modelled on `𝓡∂ 2`, e.g. a fibre
disk of the edge bundle) whose image lies in the interior `W.pieceInterior O` of an open piece
lifts to a smooth embedding `D : X → W.pieceInterior O` into the piece interior with its
boundaryless interior charts (`interiorChartedSpace`, model `𝓘(ℝ, ℝ³)`):

* `isSmoothEmbedding_interiorChart_EIM`: the identification of the piece interior with the
  interior charts post-composed to a smooth embedding (the closed kind by a diffeomorphism of
  one model, the kind with boundary by the cross-model kernel of lane O-CROSS);
* `exists_interiorLift_isSmoothEmbedding_EIM`: the lift `D` with `↑(D x) = φ x`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-- **Interior charts of a boundaryless-in-the-model manifold keep smooth embeddings** (both
carrier kinds). -/
theorem isSmoothEmbedding_interiorChart_EIM (k : CarrierModel) {N : Type*} [TopologicalSpace N]
    [cN : ChartedSpace k.Space N] [IsManifold k.model ∞ N] [BoundarylessManifold k.model N]
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
    {f : X → N} (hf : IsSmoothEmbedding (𝓡∂ 2) k.model ∞ f) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace k.model ∞ (M := N)
    let _ := DifferentialGeometry.Manifold.interiorIsManifold k.model ∞ (M := N)
    IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ f := by
  intro c₂ m₂
  cases k with
  | closed =>
    exact @IsSmoothEmbedding.diffeomorph_comp ℝ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cN _ c₂ ∞ f
      m₂ hf (@DifferentialGeometry.Manifold.interiorAtlasDiffeomorph ℝ _ _ _ _ _ N _ _ cN
        (𝓡 3) ∞ _ _)
  | withBoundary =>
    exact hf.diffeomorph_comp_fromHalfSpace_OCX
      (DifferentialGeometry.Manifold.interiorAtlasDiffeomorph (𝓡∂ 3) ∞ (M := N))

/-- **The lift of an embedded disk into the interior of an open piece** (model `𝓘(ℝ, ℝ³)`
interior charts): `↑(D x) = φ x` and `D` is a smooth embedding. -/
theorem exists_interiorLift_isSmoothEmbedding_EIM (W : CompactCarrier.{u})
    (O : TopologicalSpace.Opens W.Carrier) {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace 2) X] {φ : X → W.Carrier}
    (hφ : IsSmoothEmbedding (𝓡∂ 2) W.model ∞ φ) (hO : ∀ x, φ x ∈ W.pieceInterior O) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞
      (M := W.pieceInterior O)
    ∃ D : X → W.pieceInterior O, (∀ x, (D x : W.Carrier) = φ x) ∧
      IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ D := by
  have hD1 : IsSmoothEmbedding (𝓡∂ 2) W.model ∞
      (fun x => (⟨φ x, hO x⟩ : W.pieceInterior O)) :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡∂ 2) W.model
      (W.pieceInterior O) _ hφ
  have hD2 := isSmoothEmbedding_interiorChart_EIM W.kind hD1
  intro _
  exact ⟨fun x => ⟨φ x, hO x⟩, fun x => rfl, hD2⟩

end GC.GraphManifold.Assembly.FC39P0
