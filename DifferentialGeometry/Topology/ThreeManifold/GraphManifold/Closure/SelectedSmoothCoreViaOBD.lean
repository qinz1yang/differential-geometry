import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedSmoothCore74

/-!
# Selected solid cores carried into a carrier with boundary (lane O-BD2b)

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G3 (kernel of the boundary zero rows). The closed
route (`SolidParam74.toPiece`) carries a selected solid core of `A ⊆ X` into `W` by
`e ∘ Ψ ∘ param` with a diffeomorphism `e : X ≃ W` (`M.ψ`, `∂W = ∅`). On a carrier with boundary the
source `X` is the interior `W°` and there is no such `e`; the core is carried instead by an
injective full-rank immersion `ι : X → W` (the inclusion `W° → W`) followed by an AMBIENT
diffeomorphism `Ψ` of `W` (ZSP02 (ZH)):

* `SolidParam74.toPieceVia_OBD S ι … Ψ`: the row piece with map `Ψ ∘ ι ∘ param`;
  `range_toPieceVia_OBD` (`Ψ (ι A)`), `pieceBoundary_toPieceVia_OBD` (`Ψ (ι (frontier A))`);
* `SelectedSmoothCore74.pieceVia_OBD` / `.modelVia_OBD`: the row piece and the
  `ZeroDomains.model` value of a selected core, branch by branch exactly as
  `SelectedSmoothCore74.model` (the closed branch keeps the metric of the selected model);
  `modelVia_isRight_iff_OBD`;
* `image_frontier_of_isOpenEmbedding_OBD`: an open embedding carries the frontier of a compact set
  onto the frontier of its image.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u v

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Frontier under an open embedding**: an open embedding into a Hausdorff space carries the
frontier of a compact set onto the frontier of its image. -/
theorem image_frontier_of_isOpenEmbedding_OBD {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {ι : X → Y} (hι : Topology.IsOpenEmbedding ι) {A : Set X}
    (hA : IsCompact A) : ι '' frontier A = frontier (ι '' A) := by
  have hpre : ι ⁻¹' frontier (ι '' A) = frontier A := by
    rw [hι.isOpenMap.preimage_frontier_eq_frontier_preimage hι.continuous,
      hι.injective.preimage_image]
  have hsub : frontier (ι '' A) ⊆ range ι := by
    have hcl : IsClosed (ι '' A) := (hA.image hι.continuous).isClosed
    exact (frontier_subset_closure.trans hcl.closure_subset).trans (image_subset_range ι A)
  rw [← hpre, image_preimage_eq_of_subset hsub]

variable {X : Type v} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold (𝓡 3) ∞ X]
  {A : Set X} {W : CompactCarrier.{u}}

namespace SolidParam74

/-- The composite `ι ∘ param` has bijective differential. -/
theorem mfderiv_comp_bijective_OBD (S : SolidParam74.{u, v} A) {ι : X → W.Carrier}
    (hι : ContMDiff (𝓡 3) W.model ∞ ι) (hιb : ∀ x, Bijective (mfderiv (𝓡 3) W.model ι x))
    (q : S.Piece) : Bijective (mfderiv (𝓡∂ 3) W.model (ι ∘ S.param) q) := by
  have h1 : MDifferentiableAt (𝓡∂ 3) (𝓡 3) S.param q :=
    (S.embedding.contMDiff q).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt (𝓡 3) W.model ι (S.param q) := (hι _).mdifferentiableAt (by simp)
  rw [mfderiv_comp q h2 h1]
  exact (hιb _).comp (S.mfderiv_bijective q)

/-- **The row piece through an immersion**: the solid core carried by an injective full-rank
immersion `ι : X → W` and an ambient diffeomorphism `Ψ` of `W`; map `Ψ ∘ ι ∘ param`. -/
def toPieceVia_OBD (S : SolidParam74.{u, v} A) (ι : X → W.Carrier)
    (hι : ContMDiff (𝓡 3) W.model ∞ ι) (hιb : ∀ x, Bijective (mfderiv (𝓡 3) W.model ι x))
    (hιi : Injective ι) (Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier) : PieceEmbedding W :=
  PieceEmbedding.ofComp74 S.Piece (ι ∘ S.param) (hι.comp S.embedding.contMDiff)
    (S.mfderiv_comp_bijective_OBD hι hιb) (hιi.comp S.embedding.isEmbedding.injective) Ψ

/-- The row piece map is `Ψ ∘ ι ∘ param`. -/
theorem toPieceVia_map_OBD (S : SolidParam74.{u, v} A) (ι : X → W.Carrier)
    (hι : ContMDiff (𝓡 3) W.model ∞ ι) (hιb : ∀ x, Bijective (mfderiv (𝓡 3) W.model ι x))
    (hιi : Injective ι) (Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier) (q : S.Piece) :
    (S.toPieceVia_OBD ι hι hιb hιi Ψ).map q = Ψ (ι (S.param q)) :=
  rfl

/-- The row piece has range `Ψ (ι A)`. -/
theorem range_toPieceVia_OBD (S : SolidParam74.{u, v} A) (ι : X → W.Carrier)
    (hι : ContMDiff (𝓡 3) W.model ∞ ι) (hιb : ∀ x, Bijective (mfderiv (𝓡 3) W.model ι x))
    (hιi : Injective ι) (Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier) :
    range (S.toPieceVia_OBD ι hι hιb hιi Ψ).map = Ψ '' (ι '' A) := by
  change range (Ψ ∘ ι ∘ S.param) = _
  rw [range_comp, range_comp, S.range_eq]

/-- The model boundary image of the row piece is `Ψ (ι (frontier A))`. -/
theorem pieceBoundary_toPieceVia_OBD [T2Space X] (S : SolidParam74.{u, v} A) (ι : X → W.Carrier)
    (hι : ContMDiff (𝓡 3) W.model ∞ ι) (hιb : ∀ x, Bijective (mfderiv (𝓡 3) W.model ι x))
    (hιi : Injective ι) (Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier) :
    FC39P0.pieceBoundary (S.toPieceVia_OBD ι hι hιb hιi Ψ) = Ψ '' (ι '' frontier A) := by
  change (Ψ ∘ ι ∘ S.param) '' (𝓡∂ 3).boundary S.Piece = _
  rw [image_comp, image_comp, S.boundary_eq]

/-- The parametrized set is compact. -/
theorem isCompact_OBD (S : SolidParam74.{u, v} A) : IsCompact A := by
  rw [← S.range_eq]
  exact isCompact_range S.embedding.contMDiff.continuous

end SolidParam74

namespace SelectedSmoothCore74

/-- The row piece of a selected core through an immersion `ι` and an ambient diffeomorphism. -/
def pieceVia_OBD (Q : SelectedSmoothCore74.{u, v} A) (ι : X → W.Carrier)
    (hι : ContMDiff (𝓡 3) W.model ∞ ι) (hιb : ∀ x, Bijective (mfderiv (𝓡 3) W.model ι x))
    (hιi : Injective ι) (Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier) : PieceEmbedding W :=
  Q.solid.toPieceVia_OBD ι hι hιb hιi Ψ

/-- **The `ZeroDomains.model` value** of the selected core carried through `ι` and `Ψ`: the SAME
solid core, by branch (as `SelectedSmoothCore74.model`). -/
def modelVia_OBD (Q : SelectedSmoothCore74.{u, v} A) (ι : X → W.Carrier)
    (hι : ContMDiff (𝓡 3) W.model ∞ ι) (hιb : ∀ x, Bijective (mfderiv (𝓡 3) W.model ι x))
    (hιi : Injective ι) (Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier) :
    ZeroModel (Q.pieceVia_OBD ι hι hιb hιi Ψ) ⊕
      {C : ClosedZeroPiece W // C.piece = Q.pieceVia_OBD ι hι hιb hιi Ψ} :=
  match Q with
  | .ball _ eb => .inl (.ball eb)
  | .solidTorus _ es => .inl (.solidTorus es)
  | .twistedIBundle _ em => .inl (.twistedIBundle em)
  | .puncturedRP3 _ c f hf hr => .inl (.puncturedRP3 c f hf hr)
  | .closed S Qm metric nonneg ident be =>
      .inr ⟨⟨S.toPieceVia_OBD ι hι hιb hιi Ψ, be, Qm, metric, nonneg, ident⟩, rfl⟩

/-- A non-closed branch gives a `ZeroModel`, the closed branch a `ClosedZeroPiece`. -/
theorem modelVia_isRight_iff_OBD {Q : SelectedSmoothCore74.{u, v} A} (ι : X → W.Carrier)
    (hι : ContMDiff (𝓡 3) W.model ∞ ι) (hιb : ∀ x, Bijective (mfderiv (𝓡 3) W.model ι x))
    (hιi : Injective ι) (Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier) :
    (Q.modelVia_OBD ι hι hιb hιi Ψ).isRight = true ↔ Q.IsClosed := by
  cases Q <;> simp [modelVia_OBD, IsClosed]

/-- The row piece of a selected core has range `Ψ (ι A)`. -/
theorem range_pieceVia_OBD (Q : SelectedSmoothCore74.{u, v} A) (ι : X → W.Carrier)
    (hι : ContMDiff (𝓡 3) W.model ∞ ι) (hιb : ∀ x, Bijective (mfderiv (𝓡 3) W.model ι x))
    (hιi : Injective ι) (Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier) :
    range (Q.pieceVia_OBD ι hι hιb hιi Ψ).map = Ψ '' (ι '' A) :=
  Q.solid.range_toPieceVia_OBD ι hι hιb hιi Ψ

/-- **Model boundary of the carried core** (`ι` an open embedding): `Ψ` of the frontier of
`ι A`. -/
theorem pieceBoundary_pieceVia_OBD [T2Space X] (Q : SelectedSmoothCore74.{u, v} A)
    (ι : X → W.Carrier) (hι : ContMDiff (𝓡 3) W.model ∞ ι)
    (hιb : ∀ x, Bijective (mfderiv (𝓡 3) W.model ι x)) (hιi : Injective ι)
    (Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier) (hιo : Topology.IsOpenEmbedding ι) :
    FC39P0.pieceBoundary (Q.pieceVia_OBD ι hι hιb hιi Ψ) = frontier (Ψ '' (ι '' A)) := by
  refine (Q.solid.pieceBoundary_toPieceVia_OBD ι hι hιb hιi Ψ).trans ?_
  rw [image_frontier_of_isOpenEmbedding_OBD hιo Q.solid.isCompact_OBD]
  exact Ψ.toHomeomorph.image_frontier _

end SelectedSmoothCore74

end GC.GraphManifold.Assembly
