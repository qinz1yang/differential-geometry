import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransport74
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier

/-!
# Draft 74, D74-8 / package Z1: the selected solid core as a smooth parametrization

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G27. Draft 74 §3.1 (`ZeroDomains.piece` / `model`) and §5.2 B.
A ZSP02 zero domain `Z = Ψ(A)` is the image of the ACTUAL selected LFR54 sublevel `A` of the
original source `X` (a closed three-manifold, model `𝓡 3`) under ZSP02's ambient diffeomorphism
`Ψ`; the row piece is the SOLID core, not its frontier (D70-5, D74-8: a standard smooth frontier
`S²` / `T²` is not the solid piece).

* `SolidParam74 A`: a compact connected three-manifold with boundary `Piece` and a smooth
  embedding `param : Piece → X` whose range is `A`; its model boundary is then `frontier A`
  (`SolidParam74.boundary_eq`, from `image_boundary_eq_frontier_of_fullRank_closedEmbedding`:
  the "model boundary" of D74-8 is derived, not stored).
* `SelectedSmoothCore74 A`: the five-branch adapter of D74-8, with the model identification of
  each branch exactly as in `ZeroModel` / `ClosedZeroPiece` (ball `ClosedCell 3`, solid torus,
  twisted interval bundle, punctured `ℝP³` by a smooth embedding into the fixed
  `projectiveThreeSpaceLift`, closed nonnegative model with `Q, metric, nonneg, ident,
  boundary_empty`). The closed branch keeps the metric of the selected model.
* `SolidParam74.toPiece S Ψ e`: the row piece `PieceEmbedding W` with map `e ∘ Ψ ∘ param`
  (`e` the closed-route `M.ψ`), through `PieceEmbedding.ofComp74`; `range_toPiece`,
  `pieceBoundary_toPiece`.
* `SelectedSmoothCore74.piece` / `.model`: the row piece and the `ZeroDomains.model` value
  (`ZeroModel (piece) ⊕ {C : ClosedZeroPiece W // C.piece = piece}`), the SAME solid core
  carried by `Ψ` and `e`; `model_closed` records the metric of the closed branch.
* **`piece_of_selected_core_isotopy74`**: the draft §5.2 B theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Geometry.Boundary
open Manifold
open scoped Manifold ContDiff Topology

universe u v

namespace GC.GraphManifold.Assembly

attribute [local instance] ballCharts_ASMCERT ballSmooth_ASMCERT

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Solid smooth parametrization** of a subset `A` of a three-manifold `X`: a compact connected
three-manifold with boundary, smoothly embedded with range `A`. -/
structure SolidParam74 {X : Type v} [TopologicalSpace X] [ChartedSpace E3 X]
    [IsManifold (𝓡 3) ∞ X] (A : Set X) where
  Piece : Type u
  [topology : TopologicalSpace Piece]
  [charts : ChartedSpace (EuclideanHalfSpace 3) Piece]
  [manifold : IsManifold (𝓡∂ 3) ∞ Piece]
  [compact : CompactSpace Piece]
  [hausdorff : T2Space Piece]
  [secondCountable : SecondCountableTopology Piece]
  [connected : ConnectedSpace Piece]
  param : Piece → X
  embedding : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ param
  range_eq : range param = A

attribute [instance] SolidParam74.topology SolidParam74.charts SolidParam74.manifold
  SolidParam74.compact SolidParam74.hausdorff SolidParam74.secondCountable
  SolidParam74.connected

/-- **The five-branch selected core** (draft 74 D74-8): the solid parametrization together with
the identification with the selected LFR54 model, branch by branch. -/
inductive SelectedSmoothCore74 {X : Type v} [TopologicalSpace X] [ChartedSpace E3 X]
    [IsManifold (𝓡 3) ∞ X] (A : Set X) : Type (max (u + 1) v)
  | ball (S : SolidParam74.{u, v} A) (e : S.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
  | solidTorus (S : SolidParam74.{u, v} A)
      (e : solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯ S.Piece)
  | twistedIBundle (S : SolidParam74.{u, v} A)
      (e : mobiusBundleCarrier.{u}.Carrier ≃ₘ⟮mobiusBundleCarrier.{u}.model, 𝓡∂ 3⟯ S.Piece)
  | puncturedRP3 (S : SolidParam74.{u, v} A)
      (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (f : S.Piece → projectiveThreeSpaceLift.{u}.Carrier)
      (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
      (hrange : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
  | closed (S : SolidParam74.{u, v} A) (Q : ConnectedClosedOrientedManifold.{u} 3)
      (metric : SmoothRiemannianMetric (𝓡 3) Q.Carrier)
      (nonneg : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow metric 0)
      (ident : S.Piece ≃ₘ⟮𝓡∂ 3, 𝓡 3⟯ Q.Carrier)
      (boundary_empty : (𝓡∂ 3).boundary S.Piece = ∅)

variable {X : Type v} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold (𝓡 3) ∞ X]
  {A : Set X}

namespace SolidParam74

/-- The differential of the parametrization is bijective (full-dimensional immersion). -/
theorem mfderiv_bijective (S : SolidParam74.{u, v} A) (q : S.Piece) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3) S.param q) :=
  DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt (𝓡∂ 3) (𝓡 3)
    S.param q (S.embedding.isImmersion.isImmersionAt q) (by simp)

/-- **The row piece** of the solid core carried by the ambient diffeomorphism `Ψ` and the
closed-route identification `e` (`M.ψ`): map `e ∘ Ψ ∘ param`. -/
def toPiece {W : CompactCarrier.{u}} (S : SolidParam74.{u, v} A) (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X)
    (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) : PieceEmbedding W :=
  PieceEmbedding.ofComp74 S.Piece S.param S.embedding.contMDiff S.mfderiv_bijective
    S.embedding.isEmbedding.injective (Ψ.trans e)

/-- The row piece map is `e ∘ Ψ ∘ param`. -/
theorem toPiece_map {W : CompactCarrier.{u}} (S : SolidParam74.{u, v} A)
    (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X) (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) (q : S.Piece) :
    (S.toPiece Ψ e).map q = e (Ψ (S.param q)) :=
  rfl

/-- The row piece has range `e (Ψ A)`. -/
theorem range_toPiece {W : CompactCarrier.{u}} (S : SolidParam74.{u, v} A)
    (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X) (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) :
    range (S.toPiece Ψ e).map = e '' (Ψ '' A) := by
  refine (PieceEmbedding.ofComp74_range S.Piece S.param S.embedding.contMDiff
    S.mfderiv_bijective S.embedding.isEmbedding.injective (Ψ.trans e)).1.trans ?_
  rw [S.range_eq, Set.image_image]
  rfl

end SolidParam74

section Boundary

variable [T2Space X]

namespace SolidParam74

/-- **The model boundary is the frontier**: the image of the model boundary of the solid core is
the frontier of `A`. -/
theorem boundary_eq (S : SolidParam74.{u, v} A) :
    S.param '' (𝓡∂ 3).boundary S.Piece = frontier A := by
  have h := image_boundary_eq_frontier_of_fullRank_closedEmbedding S.param
    S.embedding.contMDiff
    (S.embedding.contMDiff.continuous.isClosedEmbedding S.embedding.isEmbedding.injective)
    (fun q => (S.mfderiv_bijective q).1) (by simp)
  rwa [S.range_eq] at h

/-- The model boundary image of the row piece is `e (Ψ (frontier A))`, i.e. `e` of the frontier
of `Ψ A`. -/
theorem pieceBoundary_toPiece {W : CompactCarrier.{u}} (S : SolidParam74.{u, v} A)
    (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X) (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) :
    FC39P0.pieceBoundary (S.toPiece Ψ e) = e '' (Ψ '' frontier A) := by
  refine (PieceEmbedding.ofComp74_range S.Piece S.param S.embedding.contMDiff
    S.mfderiv_bijective S.embedding.isEmbedding.injective (Ψ.trans e)).2.trans ?_
  rw [S.boundary_eq, Set.image_image]
  rfl

/-- The model boundary image of the row piece is `e` of the frontier of the image `Ψ A`. -/
theorem pieceBoundary_toPiece_frontier {W : CompactCarrier.{u}} (S : SolidParam74.{u, v} A)
    (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X) (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) :
    FC39P0.pieceBoundary (S.toPiece Ψ e) = e '' frontier (Ψ '' A) := by
  rw [S.pieceBoundary_toPiece, image_frontier_R74 Ψ A]

end SolidParam74

end Boundary

namespace SelectedSmoothCore74

/-- The solid parametrization underlying a selected core. -/
def solid : SelectedSmoothCore74.{u, v} A → SolidParam74.{u, v} A
  | .ball S _ => S
  | .solidTorus S _ => S
  | .twistedIBundle S _ => S
  | .puncturedRP3 S _ _ _ _ => S
  | .closed S _ _ _ _ _ => S

/-- The closed (compact nonnegative model) branch. -/
def IsClosed : SelectedSmoothCore74.{u, v} A → Prop
  | .closed .. => True
  | _ => False

/-- The row piece of a selected core. -/
def piece {W : CompactCarrier.{u}} (Q : SelectedSmoothCore74.{u, v} A) (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X)
    (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) : PieceEmbedding W :=
  Q.solid.toPiece Ψ e

/-- **The `ZeroDomains.model` value** of the selected core: the SAME solid core, by branch. The
closed branch keeps `Q`, the metric, nonnegativity, the identification and `boundary_empty` of
the selected model. -/
def model {W : CompactCarrier.{u}} (Q : SelectedSmoothCore74.{u, v} A)
    (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X) (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) :
    ZeroModel (Q.piece Ψ e) ⊕ {C : ClosedZeroPiece W // C.piece = Q.piece Ψ e} :=
  match Q with
  | .ball _ eb => .inl (.ball eb)
  | .solidTorus _ es => .inl (.solidTorus es)
  | .twistedIBundle _ em => .inl (.twistedIBundle em)
  | .puncturedRP3 _ c f hf hr => .inl (.puncturedRP3 c f hf hr)
  | .closed S Qm metric nonneg ident be =>
      .inr ⟨⟨S.toPiece Ψ e, be, Qm, metric, nonneg, ident⟩, rfl⟩

/-- A non-closed branch gives a `ZeroModel`, the closed branch a `ClosedZeroPiece`. -/
theorem model_isRight_iff {W : CompactCarrier.{u}} {Q : SelectedSmoothCore74.{u, v} A}
    (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X) (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) :
    (Q.model Ψ e).isRight = true ↔ Q.IsClosed := by
  cases Q <;> simp [model, IsClosed]

/-- The closed branch's closed zero piece has the metric, model and identification of the
selected model. -/
theorem model_closed {W : CompactCarrier.{u}} (S : SolidParam74.{u, v} A)
    (Qm : ConnectedClosedOrientedManifold.{u} 3) (metric : SmoothRiemannianMetric (𝓡 3) Qm.Carrier)
    (nonneg : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow metric 0)
    (ident : S.Piece ≃ₘ⟮𝓡∂ 3, 𝓡 3⟯ Qm.Carrier) (be : (𝓡∂ 3).boundary S.Piece = ∅)
    (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X) (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) :
    (SelectedSmoothCore74.closed S Qm metric nonneg ident be).model Ψ e =
      .inr ⟨⟨S.toPiece Ψ e, be, Qm, metric, nonneg, ident⟩, rfl⟩ :=
  rfl

/-- The row piece map of a selected core is `e ∘ Ψ ∘ param`. -/
theorem piece_map {W : CompactCarrier.{u}} (Q : SelectedSmoothCore74.{u, v} A)
    (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X) (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) (q : Q.solid.Piece) :
    (Q.piece Ψ e).map q = e (Ψ (Q.solid.param q)) :=
  rfl

end SelectedSmoothCore74

section Z1

variable [T2Space X]

/-- **Z1, draft 74 §5.2 B** (`piece_of_selected_core_isotopy74`): the selected solid core carried by
ZSP02's ambient diffeomorphism `Ψ` (`Ψ A = Z`) and the closed-route identification `e` is a row
piece of `W` with range `e Z`, model boundary `e (frontier Z)`, and the model link: the same solid
parametrization (the piece IS the core: `P.map ∘ iso = e ∘ Ψ ∘ param`), and a
`ZeroDomains.model` value of the branch of `Q` (`ZeroModel` unless `Q` is the closed branch, then
the `ClosedZeroPiece` with `C.piece = P` and the metric of the selected model). -/
theorem piece_of_selected_core_isotopy74 {W : CompactCarrier.{u}}
    (Q : SelectedSmoothCore74.{u, v} A) (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X)
    (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) {Z : Set X} (hZ : Ψ '' A = Z) :
    ∃ P : PieceEmbedding W, range P.map = e '' Z ∧ FC39P0.pieceBoundary P = e '' frontier Z ∧
      ∃ iso : Q.solid.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ P.Piece,
        (∀ q, P.map (iso q) = e (Ψ (Q.solid.param q))) ∧
        ∃ m : ZeroModel P ⊕ {C : ClosedZeroPiece W // C.piece = P},
          m.isRight = true ↔ Q.IsClosed := by
  subst hZ
  exact ⟨Q.piece Ψ e, Q.solid.range_toPiece Ψ e, Q.solid.pieceBoundary_toPiece_frontier Ψ e,
    Diffeomorph.refl (𝓡∂ 3) Q.solid.Piece ∞, fun _ => rfl, Q.model Ψ e,
    SelectedSmoothCore74.model_isRight_iff Ψ e⟩

end Z1

end GC.GraphManifold.Assembly
