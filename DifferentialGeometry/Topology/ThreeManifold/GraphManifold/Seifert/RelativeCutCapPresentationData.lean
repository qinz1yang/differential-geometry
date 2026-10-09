import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeCutCapPresentationProducts
import DifferentialGeometry.Topology.ThreeManifold.CutCap

/-!
# Protected cut-cap presentation data with independent profiles and support

Every actual capped component receives a presentation. Protected seams have complete source
ledgers, while the full surviving enumeration includes unprotected seams. All passive pieces
have actual positive compact maps; new pieces have strict planar product certificates.
-/

set_option autoImplicit false
noncomputable section
open Set Function GC.Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert

structure RelativeCapNativeProduct {W : CompactCarrier.{u}} {kind : CarrierModel}
    (S : EmbeddedCutSystem W kind) (i : Fin S.count) (k : ℕ) where
  base : PlanarBase.{u} k
  map :
    (base.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model base.surface.kind).prod (𝓡 1),
      kind.model⟯ S.Piece i
  port : Fin k ≃ Fin (S.torusCount i)
  collar : ∀ l p, p ∈ halfCollarSource →
    S.collar i (port l) p = map (base.collar l (p.1.1, p.2), p.1.2)

def RelativeCapNativeProduct.piece {W : CompactCarrier.{u}} {kind : CarrierModel}
    {S : EmbeddedCutSystem W kind} {i : Fin S.count} {k : ℕ}
    (D : RelativeCapNativeProduct S i k) : ProductFibredPiece S.toTorusPresentation i k :=
  relativeCapNativeProductPiece S i D.base D.map D.port D.collar

def relativeCapNativeProductTransport {C W : CompactCarrier.{u}} {kind : CarrierModel}
    {T : TorusPresentation C} {a : Fin T.components.count} {k : ℕ}
    (P : ProductFibredPiece T a k) (S : EmbeddedCutSystem W kind) (i : Fin S.count)
    (e : T.components.piece a ≃ₘ⟮T.cutCarrier.model, kind.model⟯ S.Piece i)
    (port : Fin k ≃ Fin (S.torusCount i))
    (hcollar : ∀ l p, p ∈ halfCollarSource → S.collar i (port l) p =
      e (P.trivialization (P.base.collar l (p.1.1, p.2), p.1.2))) :
    RelativeCapNativeProduct S i k where
  base := P.base
  map := P.trivialization.trans e
  port := port
  collar := hcollar

structure ControlledCapPresentation {M : ConnectedClosedOrientedManifold.{u} 3}
    {Q : ClosedOrientedManifold.{u} 3} (T : TorusPresentation (NoCuts.carrier M))
    (X : SphericalCutCapTransition M.toClosedOrientedManifold Q)
    (j : Fin T.pairing.count) (prot : Finset (Fin T.pairing.count))
    (support frozen : Finset (Fin T.components.count))
    (oldKind : Fin T.components.count → ℕ) where
  presentation : ∀ c : ConnectedComponents X.capped.Carrier,
    TorusPresentation (NoCuts.carrier (X.capped.component c))
  seamEquiv : (Σ c, Fin (presentation c).pairing.count) ≃
    {r : Fin T.pairing.count // r ≠ j}
  marked : {r : Fin T.pairing.count // r ∈ prot} →
    Σ c, Fin (presentation c).pairing.count
  marked_injective : Injective marked
  marked_old : ∀ r, (seamEquiv (marked r)).val = r.val
  marked_matching : ∀ r,
    (presentation (marked r).1).pairing.matching (marked r).2 = T.pairing.matching r.val
  marked_collar : ∀ r p, p ∈ signedCollarSource → ∃ x : X.tubes.core,
    x.val = T.seam r.val p ∧ X.capping.coreInclusion x =
      ((presentation (marked r).1).seam (marked r).2 p).val
  uncut : {i : Fin T.components.count // i ∉ support} →
    Σ c, Fin (presentation c).components.count
  uncut_injective : Injective uncut
  uncutDiffeomorph : ∀ i : {i : Fin T.components.count // i ∉ support},
    (componentCarrier T.cutCarrier T.components i.val).Carrier
      ≃ₘ⟮(componentCarrier T.cutCarrier T.components i.val).model,
      (componentCarrier (presentation (uncut i).1).cutCarrier
        (presentation (uncut i).1).components (uncut i).2).model⟯
      (componentCarrier (presentation (uncut i).1).cutCarrier
        (presentation (uncut i).1).components (uncut i).2).Carrier
  uncut_oriented : ∀ i, (uncutDiffeomorph i).preservesOrientation
    (componentCarrier T.cutCarrier T.components i.val).orientation
    (componentCarrier (presentation (uncut i).1).cutCarrier
      (presentation (uncut i).1).components (uncut i).2).orientation
  uncut_map : ∀ i (z : (componentCarrier T.cutCarrier T.components i.val).Carrier),
    ∃ x : X.tubes.core, x.val = T.cutMap z.val ∧ X.capping.coreInclusion x =
      ((presentation (uncut i).1).cutMap (uncutDiffeomorph i z).val).val
  uncut_kind_mem : ∀ i : {i : Fin T.components.count // i ∉ support}, i.val ∉ frozen →
    oldKind i.val ∈ ({1, 2, 3} : Finset ℕ)
  uncut_product : ∀ i, i.val ∉ frozen →
    ProductFibredPiece (presentation (uncut i).1) (uncut i).2 (oldKind i.val)
  uncut_hyperbolic : ∀ i, i.val ∈ frozen →
    ∃ g : (presentation (uncut i).1).cutCarrier.InteriorGeometry
      ((presentation (uncut i).1).components.piece (uncut i).2),
      letI := Manifold.interiorChartedSpace (presentation (uncut i).1).cutCarrier.model ∞
        (M := (presentation (uncut i).1).cutCarrier.pieceInterior
          ((presentation (uncut i).1).components.piece (uncut i).2))
      letI := Manifold.interiorIsManifold (presentation (uncut i).1).cutCarrier.model ∞
        (M := (presentation (uncut i).1).cutCarrier.pieceInterior
          ((presentation (uncut i).1).components.piece (uncut i).2))
      g.model = .hyperbolic
  newPiece : Bool → Σ c, Fin (presentation c).components.count
  newPiece_injective : Injective newPiece
  newPiece_ne_uncut : ∀ b i, newPiece b ≠ uncut i
  piece_exhausted : ∀ z, (∃ i, uncut i = z) ∨ ∃ b, newPiece b = z
  new_product : ∀ b, ProductFibredPiece (presentation (newPiece b).1) (newPiece b).2 1
  origin : ∀ c, Fin (presentation c).components.count → Fin T.components.count
  uncut_origin : ∀ i, origin (uncut i).1 (uncut i).2 = i.val
  retained_origin : ∀ c i (z : (presentation c).components.piece i) (x : X.tubes.core),
    ((presentation c).cutMap z).val = X.capping.coreInclusion x →
      x.val ∈ T.cutMap '' (T.components.piece (origin c i) : Set T.cutCarrier.Carrier)

end GC.Seifert
