import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedSmoothCore74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereZero
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideBallGerm

/-!
# Draft 74, D74-8 / Z1: consumer on the S³ zero ball (real inhabitant)

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G27 (consumer). The outer zero ball of the S³ inhabitant
(`cycleBallPiece true`, the cap `q₀ ≥ 3/5`) as a selected core of the BALL branch
(`sphereOuterSolid74`: the solid `ClosedCell 3` smoothly embedded by `cycleBallAmbient true ∘ val`,
`isSmoothEmbedding_comp_partialDiffeomorph`), carried along the identity `Ψ` and the identity
carrier diffeomorphism `e`:

* `sphereOuterPiece74` is the tree's outer ball piece (same map), with `ZeroModel.ball`
  (`sphereOuterModel74`, a non-closed branch) and the model boundary the level `q₀ = 3/5`
  (`sphereOuterPiece74_boundary`, via `SolidParam74.boundary_eq`, i.e. derived from the embedding);
* `piece_of_selected_core_isotopy74` produces a piece of range `range (cycleBallPiece true).map`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

attribute [local instance] ballCharts_ASMCERT ballSmooth_ASMCERT ballConnected_FC39P0

/-- The solid `ClosedCell 3` embedded as the outer zero ball of S³. -/
def sphereOuterSolid74 : SolidParam74.{0, 0} (range (cycleBallPiece true).map) where
  Piece := ClosedCell 3
  param := (cycleBallPiece true).map
  embedding :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph (cycleBallAmbient true)
      isSmoothEmbedding_cellVal (by rw [cycleBallAmbient_source]; exact subset_univ _)
  range_eq := rfl

/-- The outer zero ball of S³ as a selected core of the ball branch. -/
def sphereOuterCore74 : SelectedSmoothCore74.{0, 0} (range (cycleBallPiece true).map) :=
  .ball sphereOuterSolid74 (Diffeomorph.refl (𝓡∂ 3) (ClosedCell 3) ∞)

/-- The identity carrier diffeomorphism of the S³ carrier (model form `𝓡 3`). -/
def sphereId74 : sphereW.Carrier ≃ₘ⟮𝓡 3, sphereW.model⟯ sphereW.Carrier :=
  Diffeomorph.refl sphereW.model sphereW.Carrier ∞

/-- The row piece of the selected core along the identity. -/
def sphereOuterPiece74 : PieceEmbedding sphereW :=
  sphereOuterCore74.piece (Diffeomorph.refl (𝓡 3) sphereW.Carrier ∞) sphereId74

/-- It is the tree's outer ball piece (same map). -/
theorem sphereOuterPiece74_map : sphereOuterPiece74.map = (cycleBallPiece true).map :=
  rfl

/-- Its model is the ball model (a non-closed branch). -/
def sphereOuterModel74 : ZeroModel sphereOuterPiece74 :=
  .ball (Diffeomorph.refl (𝓡∂ 3) (ClosedCell 3) ∞)

theorem sphereOuterCore74_model :
    sphereOuterCore74.model (Diffeomorph.refl (𝓡 3) sphereW.Carrier ∞) sphereId74 =
      .inl sphereOuterModel74 :=
  rfl

/-- The model boundary of the carried core is the level `q₀ = 3/5` (derived from the embedding). -/
theorem sphereOuterPiece74_boundary :
    pieceBoundary sphereOuterPiece74 = {x | 3 / 5 - sphereHeight x = 0} := by
  rw [← pieceBoundary_outerBall]
  refine (sphereOuterSolid74.pieceBoundary_toPiece
    (Diffeomorph.refl (𝓡 3) sphereW.Carrier ∞) sphereId74).trans ?_
  exact ((Set.image_image _ _ _).trans (Set.image_id' _)).trans
    sphereOuterSolid74.boundary_eq.symm

/-- **Z1 on the S³ inhabitant**: the theorem of draft 74 §5.2 B applied to the outer ball. -/
theorem sphereOuter_piece_of_core74 :
    ∃ P : PieceEmbedding sphereW, range P.map = range (cycleBallPiece true).map ∧
      pieceBoundary P = {x | 3 / 5 - sphereHeight x = 0} ∧
      ∃ iso : sphereOuterCore74.solid.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ P.Piece,
        (∀ q, P.map (iso q) = (cycleBallPiece true).map q) ∧
        ∃ m : ZeroModel P ⊕ {C : ClosedZeroPiece sphereW // C.piece = P},
          m.isRight = true ↔ sphereOuterCore74.IsClosed := by
  obtain ⟨P, h1, h2, iso, h3, m, h4⟩ := piece_of_selected_core_isotopy74 sphereOuterCore74
    (Diffeomorph.refl (𝓡 3) sphereW.Carrier ∞) sphereId74
    (Z := range (cycleBallPiece true).map) (Set.image_id _)
  refine ⟨P, h1.trans (Set.image_id _), ?_, iso, h3, m, h4⟩
  rw [h2, ← pieceBoundary_outerBall]
  exact (Set.image_id' _).trans sphereOuterSolid74.boundary_eq.symm

end GC.GraphManifold.Assembly.FC39P0
