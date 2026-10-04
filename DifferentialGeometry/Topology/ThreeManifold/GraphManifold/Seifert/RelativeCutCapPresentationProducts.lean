import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces

/-!
# Native product models with every actual half collar

A native planar product diffeomorphism, its complete port bijection and its collar equations
produce the actual ProductFibredPiece of the assembled cut system. Neither a Raw profile nor
a preassembled product-piece certificate is supplied as an input.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert

def relativeCapNativeProductPiece {W : CompactCarrier.{u}} {kind : CarrierModel}
    (S : EmbeddedCutSystem W kind) (i : Fin S.count) {k : ℕ}
    (B : PlanarBase.{u} k)
    (e :
      (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
        kind.model⟯ S.Piece i)
    (port : Fin k ≃ Fin (S.torusCount i))
    (hcollar : ∀ l p, p ∈ halfCollarSource →
      S.collar i (port l) p = e (B.collar l (p.1.1, p.2), p.1.2)) :
    ProductFibredPiece S.toTorusPresentation i k where
  base := B
  port := port.trans (S.port i)
  trivialization := e.trans (S.pieceDiffeomorph i)
  collar_eq l p hp := by
    apply Subtype.ext
    refine (TorusPresentation.pieceCollar_apply S.toTorusPresentation i
      (S.port i (port l)) hp).trans ?_
    rw [S.sideCollar_eq, S.sideOf_port, S.sideCollar_apply, hcollar l p hp]
    rfl

end GC.Seifert
