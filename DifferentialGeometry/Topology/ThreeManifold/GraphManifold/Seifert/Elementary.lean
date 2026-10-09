import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Flatten
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClassicalInputs

/-!
# Elementary presentations

Chapter 6, packet E0 of the P1 survey (`20261003-survey-p1-elementarize.md`, §5), statements only.
An `ElementaryPresentation W` is a torus presentation of `W` all of whose pieces are product
fibred over a planar base `Pₖ`, `k ∈ {1, 2, 3}` (`ProductFibredPiece`); `toRaw` flattens it by
`toRawOfProductPieces`, and its torus presentation is the given one by `rfl`.

`Elementarize` is the target of P1: every raw graph presentation of `W` admits an elementary
presentation of `W` with as many external tori, whose external half collars are the old ones up
to a diffeomorphism `ψ i` of the torus factor. `ElementarizePiece` is the same for the single
piece `ofPiece i` of a torus presentation carrying one circle fibration (the input of P2); it is
the instance of `Elementarize` at `(ofPiece i).withFibration` (`elementarizePiece_of_elementarize`).

RG01 and RG03 of `ClassicalInputs.lean` use `discModel`, `annulusModel` and `pantsModel`, so they
are restated against `PlanarBase k`. A `MobiusBase` is a compact surface with one collared
boundary circle and a smooth embedding onto `mobiusModel` sending that circle to `mobiusPoint · 0`;
an `ElementaryBase` is a `PlanarBase k` with `k ∈ {1, 2, 3}` or a `MobiusBase`. A
`PlanarDecomposition B` is a finite family of disjoint bicollared circles `cut c` in the interior
of `B` and finitely many elementary bases smoothly embedded in `B`, covering `B` and meeting only
on the cuts; the two sides of a cut are distinct boundary circles of pieces whose half collars are
the half bicollars up to a diffeomorphism of the circle, and every other boundary circle of a
piece lies in `∂B`. RG01′ is `CircleBundlesOverPlanarBasesStandard` (a circle fibration over a
base diffeomorphic to `Pₖ` is a product over `Pₖ`, over a `MobiusBase` it has a twisted chart) and
RG03′ is `PlanarSurfaceDecomposition` (every compact surface has a planar decomposition). Neither
is compared with its predecessor, since the models differ by planar diffeomorphisms not built
here. `TorusMatrixLinear` is proved in `Seifert/Adapters.lean`.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

structure ElementaryPresentation (W : CompactCarrier.{u}) where
  toTorus : TorusPresentation.{u} W
  kind : Fin toTorus.components.count → ℕ
  kind_mem : ∀ i, kind i ∈ ({1, 2, 3} : Finset ℕ)
  piece : ∀ i, ProductFibredPiece toTorus i (kind i)

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}}

def toRaw (E : ElementaryPresentation W) : RawGraphPresentation W :=
  E.toTorus.toRawOfProductPieces E.kind E.piece

@[simp]
theorem toRaw_toTorusPresentation (E : ElementaryPresentation W) :
    E.toRaw.toTorusPresentation = E.toTorus := rfl

theorem toRaw_fibration (E : ElementaryPresentation W) (i : Fin E.toTorus.components.count) :
    E.toRaw.fibration i = (E.piece i).fibration := rfl

@[simp]
theorem toRaw_externalCount (E : ElementaryPresentation W) :
    E.toRaw.externalCount = E.toTorus.externalCount := rfl

@[simp]
theorem toRaw_external (E : ElementaryPresentation W) : E.toRaw.external = E.toTorus.external :=
  rfl

end ElementaryPresentation

def Elementarize : Prop :=
  ∀ (W : CompactCarrier.{u}) (G : RawGraphPresentation W),
    ∃ E : ElementaryPresentation W, ∃ h : E.toTorus.externalCount = G.externalCount,
      ∃ ψ : Fin G.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
        ∀ i p, p ∈ halfCollarSource →
          E.toTorus.external.collar (Fin.cast h.symm i) p = G.external.collar i (ψ i p.1, p.2)

def ElementarizePiece : Prop :=
  ∀ (W : CompactCarrier.{u}) (T : TorusPresentation.{u} W) (i : Fin T.components.count),
    CircleFibration T.cutCarrier (T.components.piece i) →
      ∃ E : ElementaryPresentation (GC.Topology.componentCarrier T.cutCarrier T.components i),
        ∃ h : E.toTorus.externalCount = (T.ofPiece i).externalCount,
          ∃ ψ : Fin (T.ofPiece i).externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
            ∀ j p, p ∈ halfCollarSource → E.toTorus.external.collar (Fin.cast h.symm j) p =
              (T.ofPiece i).external.collar j (ψ j p.1, p.2)

theorem elementarizePiece_of_elementarize (h : Elementarize.{u}) : ElementarizePiece.{u} :=
  fun _ T i F => h _ ((T.ofPiece i).withFibration fun _ => F.toComponent T.components i)

structure MobiusBase where
  surface : CompactSurface.{u}
  collar : PartialDiffeomorph circleCollarModel (SurfaceModel.model surface.kind)
    (Circle × EuclideanHalfSpace 1) surface.Carrier ∞
  source_eq : collar.source = circleCollarSource
  boundary_exhausted : (SurfaceModel.model surface.kind).boundary surface.Carrier =
    range fun t => collar (t, halfZero)
  embedding : surface.Carrier → EuclideanSpace ℝ (Fin 3)
  isSmoothEmbedding : Manifold.IsSmoothEmbedding (SurfaceModel.model surface.kind)
    𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ embedding
  range_embedding : range embedding = mobiusModel
  embedding_collar : ∀ t, embedding (collar (t, halfZero)) = mobiusPoint t 0

inductive ElementaryBase : Type (u + 1)
  | planar (k : ℕ) (hk : k ∈ ({1, 2, 3} : Finset ℕ)) (P : PlanarBase.{u} k)
  | mobius (M : MobiusBase.{u})

namespace ElementaryBase

def surface : ElementaryBase.{u} → CompactSurface.{u}
  | planar _ _ P => P.surface
  | mobius M => M.surface

def boundaryCount : ElementaryBase.{u} → ℕ
  | planar k _ _ => k
  | mobius _ => 1

def collar : (P : ElementaryBase.{u}) → Fin P.boundaryCount →
    PartialDiffeomorph circleCollarModel (SurfaceModel.model P.surface.kind)
      (Circle × EuclideanHalfSpace 1) P.surface.Carrier ∞
  | planar _ _ P, j => P.collar j
  | mobius M, _ => M.collar

end ElementaryBase

structure PlanarDecomposition (B : CompactSurface.{u}) where
  cutCount : ℕ
  cut : Fin cutCount → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
    (Circle × ℝ) B.Carrier ∞
  cut_source : ∀ c, (cut c).source = {p | -1 < p.2 ∧ p.2 < 1}
  cut_interior : ∀ c, (cut c).target ⊆ (SurfaceModel.model B.kind).interior B.Carrier
  cut_disjoint : Pairwise fun c d => Disjoint (cut c).target (cut d).target
  pieceCount : ℕ
  piece : Fin pieceCount → ElementaryBase.{u}
  inclusion : ∀ j, (piece j).surface.Carrier → B.Carrier
  isSmoothEmbedding : ∀ j, Manifold.IsSmoothEmbedding
    (SurfaceModel.model (piece j).surface.kind) (SurfaceModel.model B.kind) ∞ (inclusion j)
  covers : ⋃ j, range (inclusion j) = univ
  cutSide : Fin cutCount → Bool → Σ j, Fin (piece j).boundaryCount
  cutSide_injective : Function.Injective (Function.uncurry cutSide)
  cutSide_collar : ∀ c b, ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
    inclusion (cutSide c b).1 ((piece (cutSide c b).1).collar (cutSide c b).2
      (t, halfPoint s hs)) = cut c (σ t, if b then s else -s)
  boundary_side : ∀ j l, (∀ c b, cutSide c b ≠ ⟨j, l⟩) → ∀ t,
    (SurfaceModel.model B.kind).IsBoundaryPoint (inclusion j ((piece j).collar l (t, halfZero)))
  overlap : ∀ j j' x x', j ≠ j' → inclusion j x = inclusion j' x' →
    ∃ c t, inclusion j x = cut c (t, 0)

def CircleBundlesOverPlanarBasesStandard : Prop :=
  ∀ (C : CompactCarrier.{u}) (U : TopologicalSpace.Opens C.Carrier) (F : CircleFibration C U),
    (∀ k, k ∈ ({1, 2, 3} : Finset ℕ) → ∀ (P : PlanarBase.{u} k)
      (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
        SurfaceModel.model P.surface.kind⟯ P.surface.Carrier),
      ∃ Φ : U ≃ₘ⟮C.model, (SurfaceModel.model P.surface.kind).prod (𝓡 1)⟯
          P.surface.Carrier × Circle, ∀ x, (Φ x).1 = e (F.projection x)) ∧
    ∀ (M : MobiusBase.{u}) (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
        SurfaceModel.model M.surface.kind⟯ M.surface.Carrier),
      ∃ Ψ : (Circle × unitInterval) × Circle → U, IsTwistedChart F (M.embedding ∘ e) Ψ

def PlanarSurfaceDecomposition : Prop :=
  ∀ B : CompactSurface.{u}, Nonempty (PlanarDecomposition B)

end GC.Seifert
