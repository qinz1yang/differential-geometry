import DifferentialGeometry.Topology.Manifold.CompactModel
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.NoCuts

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold
universe u

abbrev SurfaceModel := ModelBoundaryKind
abbrev SurfaceModel.Space (k : SurfaceModel) := ModelBoundaryKind.Space k 2
abbrev SurfaceModel.model (k : SurfaceModel) := ModelBoundaryKind.model k 2
structure CompactSurface extends CompactModelManifold.{u} 2 where
  [connected : ConnectedSpace Carrier]
attribute [instance] CompactSurface.connected

structure CircleFibration (C : CompactCarrier.{u}) (U : TopologicalSpace.Opens C.Carrier) where
  base : CompactSurface.{u}
  projection : C(U, base.Carrier)
  surjective : Function.Surjective projection
  smooth : ContMDiff C.model (SurfaceModel.model base.kind) ∞ projection
  neighborhood : base.Carrier → TopologicalSpace.Opens base.Carrier
  mem_neighborhood : ∀ b, b ∈ neighborhood b
  trivialization : (b : base.Carrier) →
    (TopologicalSpace.Opens.comap projection (neighborhood b))
      ≃ₘ⟮C.model, (SurfaceModel.model base.kind).prod (𝓡 1)⟯ ((neighborhood b) × Circle)
  projection_trivialization : ∀ b x, ((trivialization b x).1).val = projection x.val

structure BoundaryTori (C : CompactCarrier.{u}) (n : ℕ) where
  collar : Fin n →
    PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞
  source_eq : ∀ i, (collar i).source = halfCollarSource
  boundary_zero : ∀ i t, C.model.IsBoundaryPoint (collar i (t, halfZero))
  disjoint : Pairwise (fun i j => Disjoint (collar i).target (collar j).target)

namespace BoundaryTori

def torusMap {C : CompactCarrier.{u}} {n : ℕ} (T : BoundaryTori C n) (i : Fin n) :
    Torus → C.Carrier := fun t => T.collar i (t, halfZero)

def image {C : CompactCarrier.{u}} {n : ℕ} (T : BoundaryTori C n) : Set C.Carrier :=
  ⋃ i, Set.range (T.torusMap i)

private theorem zero_mem_source {C : CompactCarrier.{u}} {n : ℕ}
    (T : BoundaryTori C n) (i : Fin n) (t : Torus) :
    (t, halfZero) ∈ (T.collar i).source := by
  rw [T.source_eq]
  change (0 : ℝ) < 1
  norm_num

theorem torusMap_smooth {C : CompactCarrier.{u}} {n : ℕ} (T : BoundaryTori C n)
    (i : Fin n) : ContMDiff torusModel C.model ∞ (T.torusMap i) :=
  (T.collar i).contMDiffOn.comp_contMDiff
    (contMDiff_id.prodMk contMDiff_const) (T.zero_mem_source i)

def boundaryMap {C : CompactCarrier.{u}} {n : ℕ} (T : BoundaryTori C n)
    (i : Fin n) : C(Torus, C.Carrier) :=
  ⟨T.torusMap i, (T.torusMap_smooth i).continuous⟩

theorem torusMap_isEmbedding {C : CompactCarrier.{u}} {n : ℕ}
    (T : BoundaryTori C n) (i : Fin n) : _root_.Topology.IsEmbedding (T.torusMap i) := by
  apply ((T.torusMap_smooth i).continuous.isClosedEmbedding ?_).isEmbedding
  intro x y h
  exact congrArg Prod.fst ((T.collar i).toOpenPartialHomeomorph.injOn
    (T.zero_mem_source i x) (T.zero_mem_source i y) h)

def incompressible {C : CompactCarrier.{u}} {n : ℕ} (T : BoundaryTori C n) : Prop :=
  ∀ i : Fin n, ∀ x : Torus, Function.Injective (FundamentalGroup.map (T.boundaryMap i) x)

end BoundaryTori

structure TorusPairing (C : CompactCarrier.{u}) where
  count : ℕ
  gluing : BoundaryGluing C.Carrier (Fin count)
  leftParam : (i : Fin count) → Torus ≃ₜ gluing.left i
  rightParam : (i : Fin count) → Torus ≃ₜ gluing.right i
  matching : Fin count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  matching_eq : ∀ i t, gluing.attaching i (leftParam i t) = rightParam i (matching i t)
  leftCollar : Fin count →
    PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞
  rightCollar : Fin count →
    PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞
  left_source : ∀ i, (leftCollar i).source = halfCollarSource
  right_source : ∀ i, (rightCollar i).source = halfCollarSource
  left_zero : ∀ i t, leftCollar i (t, halfZero) = (leftParam i t).val
  right_zero : ∀ i t, rightCollar i (t, halfZero) = (rightParam i t).val
  reversing : ∀ i, ReversesBoundaryOrientation C (leftCollar i)
    (fun p => rightCollar i (matching i p.1, p.2))

namespace TorusPairing

abbrev QuotientSpace {C : CompactCarrier.{u}} (G : TorusPairing C) :=
  Quotient G.gluing.setoid

instance {C : CompactCarrier.{u}} (G : TorusPairing C) : T2Space G.QuotientSpace :=
  BoundaryGluing.instT2SpaceQuotient G.gluing

def quotientMap {C : CompactCarrier.{u}} (G : TorusPairing C) : C(C.Carrier, G.QuotientSpace) :=
  ⟨Quotient.mk'', continuous_quotient_mk'⟩

end TorusPairing

structure RawGraphPresentation (W : CompactCarrier.{u}) where
  cutCarrier : CompactCarrier.{u}
  components : cutCarrier.Components
  fibration : (i : Fin components.count) → CircleFibration cutCarrier (components.piece i)
  pairing : TorusPairing cutCarrier
  externalCount : ℕ
  external : BoundaryTori W externalCount
  cutExternal : BoundaryTori cutCarrier externalCount
  external_exhausted : W.model.boundary W.Carrier = external.image
  cut_boundary_exhausted : cutCarrier.model.boundary cutCarrier.Carrier =
    (⋃ i, pairing.gluing.block i) ∪ cutExternal.image
  external_disjoint : Disjoint (⋃ i, pairing.gluing.block i) cutExternal.image
  reconstruction : pairing.QuotientSpace ≃ₜ W.Carrier
  quotient_smooth : ContMDiff cutCarrier.model W.model ∞
    (reconstruction ∘ pairing.quotientMap)
  quotient_oriented : ∀ x : cutCarrier.Carrier,
    ∃ L : TangentSpace cutCarrier.model x ≃ₗ[ℝ]
        TangentSpace W.model (reconstruction (pairing.quotientMap x)),
      (∀ v, L v = mfderiv cutCarrier.model W.model
        (reconstruction ∘ pairing.quotientMap) x v) ∧
      Orientation.map (Fin 3) L (cutCarrier.orientation.orientation x) =
        W.orientation.orientation (reconstruction (pairing.quotientMap x))
  interiorImage : TopologicalSpace.Opens W.Carrier
  interiorDiffeomorph : cutCarrier.interior ≃ₘ⟮cutCarrier.model, W.model⟯ interiorImage
  interior_map : ∀ x : cutCarrier.interior,
    (interiorDiffeomorph x).val = reconstruction (pairing.quotientMap x.val)
  seam : Fin pairing.count →
    PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞
  seam_source : ∀ i, (seam i).source = signedCollarSource
  seam_zero : ∀ i t, seam i (t, 0) =
    reconstruction (pairing.quotientMap (pairing.leftParam i t))
  seam_positive : ∀ i t s (hs : 0 ≤ s), s < 1 → seam i (t, s) =
    reconstruction (pairing.quotientMap (pairing.rightCollar i
      (pairing.matching i t, halfPoint s hs)))
  seam_negative : ∀ i t s (hs : s ≤ 0), -1 < s → seam i (t, s) =
    reconstruction (pairing.quotientMap (pairing.leftCollar i
      (t, halfPoint (-s) (neg_nonneg.mpr hs))))
  seam_interior : ∀ i, (seam i).target ⊆ W.interior
  seam_disjoint : Pairwise (fun i j => Disjoint (seam i).target (seam j).target)
  marked_collar : ∀ i p, p ∈ halfCollarSource →
    reconstruction (pairing.quotientMap (cutExternal.collar i p)) = external.collar i p
  external_seam_disjoint : ∀ i j, Disjoint (external.collar i).target (seam j).target
  leftPiece : Fin pairing.count → Fin components.count
  rightPiece : Fin pairing.count → Fin components.count
  left_owned : ∀ i, pairing.gluing.left i ⊆ components.piece (leftPiece i)
  right_owned : ∀ i, pairing.gluing.right i ⊆ components.piece (rightPiece i)
  externalPiece : Fin externalCount → Fin components.count
  external_owned : ∀ i, Set.range (cutExternal.torusMap i) ⊆
    components.piece (externalPiece i)

end GC.GraphManifold
