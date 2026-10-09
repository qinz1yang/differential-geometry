import DifferentialGeometry.Topology.ThreeManifold.Geometrization.HyperbolicPieceGroupFI

/-!
# The piece profile of admission (b) and the inputs of the initial relative stage

Lane BE, deliverable 1 (X38 survey row BE, review 20 §9.1, review 26 §1.2). Admission (b) of
`GM/Refinement.lean` gives every piece of a torus decomposition `D` as a value of the frozen
inductive `HyperbolicOrGraph`: an interior geometry of the piece of model `.hyperbolic`, or a raw
graph presentation of the actual component carrier. Proof files may not import that file (D6), so
`PieceProfile` mirrors it constructor by constructor; the admission file converts by
`.hyperbolic g hg ↦ .hyperbolic g hg`, `.graph G ↦ .graph G`. `PieceProfile.toOr` is the inline
proposition consumed by K17b's endpoints.

The initial stage of the relative normalisation starts from B0's presentation `T₀` of `D`
(`decompositionPresentationOfWidth`: same cut carrier and components, seams
`primeSeam j (t, δ s)`) and needs, for every piece, either the geometry of the actual compact
carrier `componentCarrier T₀.cutCarrier T₀.components i` on its whole interior or a raw
presentation of that carrier. A hyperbolic piece is never cut: its geometry is moved to the whole
interior by `D.componentGeometry i g`, keeping the model (`D.componentGeometry_model`); a graph
piece keeps its raw presentation. `exists_initialStageInputs` packages this together with the
invariant (Inc) of the normalisation at the start — every seam torus of `T₀` is π₁-injective in
`M` at every basepoint, because it is the zero torus `torusInPrime j` of the incompressible
`D` (`DecompositionPresentation.seamTorus_eq`) — and B0's port bridge (every port of every piece
is π₁-injective in the piece).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.Endpoint

inductive PieceProfile (C : CompactCarrier.{u}) (D : C.Components) (i : Fin D.count)
  | hyperbolic (geometry : C.InteriorGeometry (D.piece i))
      (model_eq :
        letI := Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior (D.piece i))
        letI := Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior (D.piece i))
        geometry.model = .hyperbolic)
  | graph (presentation : RawGraphPresentation (componentCarrier C D i))

namespace PieceProfile

variable {C : CompactCarrier.{u}} {D : C.Components} {i : Fin D.count}

theorem toOr : PieceProfile C D i →
    (∃ g : C.InteriorGeometry (D.piece i),
      letI := Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior (D.piece i))
      letI := Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior (D.piece i))
      g.model = .hyperbolic) ∨
      Nonempty (RawGraphPresentation (componentCarrier C D i))
  | .hyperbolic g hg => Or.inl ⟨g, hg⟩
  | .graph G => Or.inr ⟨G⟩

theorem exists_hyperbolic_of_forall_ne_graph (p : PieceProfile C D i)
    (h : ∀ G, p ≠ .graph G) :
    ∃ g : C.InteriorGeometry (D.piece i),
      letI := Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior (D.piece i))
      letI := Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior (D.piece i))
      g.model = .hyperbolic := by
  cases p with
  | hyperbolic g hg => exact ⟨g, hg⟩
  | graph G => exact absurd rfl (h G)

end PieceProfile

end GC.Endpoint

namespace GC.Topology.TorusDecomposition

variable {M : ConnectedClosedOrientedManifold.{u} 3} {D : TorusDecomposition M}

theorem DecompositionPresentation.seamTorus_eq (P : DecompositionPresentation D)
    (j : Fin D.boundary.count) :
    P.presentation.seamTorus (P.seamIndex j) =
      D.reconstructionAtlas.torusInPrime D.reconstruction j := by
  ext t
  exact P.seam_zero_eq j t

theorem DecompositionPresentation.injective_seamTorus (P : DecompositionPresentation D)
    (hinj : D.reconstructionAtlas.Incompressible D.reconstruction)
    (k : Fin P.presentation.pairing.count) (t₀ : Torus) :
    Function.Injective (FundamentalGroup.map (P.presentation.seamTorus k) t₀) := by
  obtain ⟨j, rfl⟩ := P.seamIndex.surjective k
  rw [P.seamTorus_eq j]
  exact hinj j t₀

end GC.Topology.TorusDecomposition

namespace GC.Endpoint

theorem exists_initialStageInputs (M : ConnectedClosedOrientedManifold.{u} 3)
    (D : TorusDecomposition M)
    (hinj : D.reconstructionAtlas.Incompressible D.reconstruction)
    (pieces : ∀ i : Fin D.components.count, PieceProfile D.carrier D.components i) :
    ∃ P : TorusDecomposition.DecompositionPresentation D,
      (∀ k t₀, Function.Injective (FundamentalGroup.map (P.presentation.seamTorus k) t₀)) ∧
      (∀ i, (P.presentation.pieceBoundaryTori i).incompressible) ∧
      ∀ i, (∃ g : (componentCarrier P.presentation.cutCarrier P.presentation.components i
          ).InteriorGeometry ⊤,
        letI := Manifold.interiorChartedSpace
          (componentCarrier P.presentation.cutCarrier P.presentation.components i).model ∞
          (M := (componentCarrier P.presentation.cutCarrier P.presentation.components i
            ).pieceInterior ⊤)
        letI := Manifold.interiorIsManifold
          (componentCarrier P.presentation.cutCarrier P.presentation.components i).model ∞
          (M := (componentCarrier P.presentation.cutCarrier P.presentation.components i
            ).pieceInterior ⊤)
        g.model = .hyperbolic) ∨
        Nonempty (RawGraphPresentation
          (componentCarrier P.presentation.cutCarrier P.presentation.components i)) := by
  obtain ⟨δ, hδ, hδ1, hdisj⟩ := D.exists_width
  refine ⟨D.decompositionPresentationOfWidth hδ hδ1 hdisj,
    (D.decompositionPresentationOfWidth hδ hδ1 hdisj).injective_seamTorus hinj,
    (D.decompositionPresentationOfWidth hδ hδ1 hdisj).pieceBoundaryTori_incompressible hinj,
    fun i => ?_⟩
  cases pieces i with
  | hyperbolic g hg =>
    exact Or.inl ⟨D.componentGeometry i g, (D.componentGeometry_model i g).trans hg⟩
  | graph G => exact Or.inr ⟨G⟩

end GC.Endpoint
