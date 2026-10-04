import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensSpacePresentation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockCharts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CliffordBlocks
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierIncidence

/-!
# Canonical solid-piece germs for the actual lens carrier

An arbitrary actual solid piece admits a standard unit-disc product diffeomorphism whose
positive collar germ agrees with the given port. Universe changes preserve the standard collar.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u v

namespace GC.Seifert

def lensUnitDiscChangeUniverse : UnitDisc.{u} ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ UnitDisc.{v} :=
  (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).symm.trans
    (uliftDiffeomorph (𝓡∂ 2) unitDiscSet)

theorem lensUnitDiscChangeUniverse_collar (t : Circle) (s : EuclideanHalfSpace 1) :
    lensUnitDiscChangeUniverse.{u, v} (cliffordDiscCollarMap.{u} (t, s)) =
      cliffordDiscCollarMap.{v} (t, s) := by
  apply ULift.ext
  apply Subtype.ext
  change (cliffordDiscCollarMap.{u} (t, s)).down.val =
    (cliffordDiscCollarMap.{v} (t, s)).down.val
  rw [cliffordDiscCollarMap_val, cliffordDiscCollarMap_val]

theorem SolidTorusPiece.exists_lensUnitDisc_germ {W : CompactCarrier.{u}}
    {T : TorusPresentation W} {i : Fin T.components.count} (P : SolidTorusPiece T i) :
    ∃ δ > (0 : ℝ), ∃ Θ : (UnitDisc.{v} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      T.cutCarrier.model⟯ T.components.piece i,
      ∀ p, p ∈ halfCollarSource → p.2.val 0 < δ →
        T.pieceCollar i (P.port 0) p = Θ (cliffordDiscCollarMap (p.1.1, p.2), p.1.2) := by
  obtain ⟨δ, hδ, Θ, hΘ⟩ := P.exists_standard_germ unitDiscPlanarBase
  refine ⟨δ, hδ, (lensUnitDiscChangeUniverse.{v, u}.prodCongr
    (Diffeomorph.refl (𝓡 1) Circle ∞)).trans Θ, fun p hp hlt => ?_⟩
  rw [hΘ 0 p hp hlt]
  change Θ (cliffordDiscCollarMap (p.1.1, p.2), p.1.2) =
    Θ (lensUnitDiscChangeUniverse (cliffordDiscCollarMap (p.1.1, p.2)), p.1.2)
  rw [lensUnitDiscChangeUniverse_collar]

end GC.Seifert
