import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawUniverseLift

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold Set
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold
universe u

attribute [local instance] uliftChartedSpace isManifold_ulift

/-- **Lift of a universe-`0` raw graph presentation to any universe along an oriented
diffeomorphism**: the tree's `RawUniverseLift.raw` (ULift) followed by the same-universe
`RawGraphPresentation.transport`. -/
def RawGraphPresentation.liftAlong_UL {W₀ : CompactCarrier.{0}} {W : CompactCarrier.{u}}
    (G : RawGraphPresentation.{0} W₀) (ψ : W₀.Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier)
    (hψ : ψ.preservesOrientation W₀.orientation W.orientation) :
    RawGraphPresentation.{u} W :=
  let ψ' : (RawUniverseLift.carrier.{u} W₀).Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier :=
    (RawUniverseLift.up.{u} W₀).symm.trans ψ
  have hψ' : ψ'.preservesOrientation (RawUniverseLift.carrier.{u} W₀).orientation
      W.orientation :=
    Diffeomorph.preservesOrientation_trans
      (Diffeomorph.preservesOrientation_symm
        (uliftDiffeomorph_preservesOrientation W₀.model W₀.Carrier W₀.orientation)) hψ
  (RawUniverseLift.raw.{u} W₀ G).transport ψ' hψ'

theorem RawGraphPresentation.liftAlong_UL_externalCount {W₀ : CompactCarrier.{0}}
    {W : CompactCarrier.{u}} (G : RawGraphPresentation.{0} W₀)
    (ψ : W₀.Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier)
    (hψ : ψ.preservesOrientation W₀.orientation W.orientation) :
    (G.liftAlong_UL ψ hψ).externalCount = G.externalCount := rfl

theorem RawGraphPresentation.liftAlong_UL_range {W₀ : CompactCarrier.{0}}
    {W : CompactCarrier.{u}} (G : RawGraphPresentation.{0} W₀)
    (ψ : W₀.Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier)
    (hψ : ψ.preservesOrientation W₀.orientation W.orientation) (i : Fin G.externalCount) :
    Set.range ((G.liftAlong_UL ψ hψ).external.torusMap i) =
      ψ '' Set.range (G.external.torusMap i) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨G.external.torusMap i t, ⟨t, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩

/-- **Raw presentations transport across universes** along an oriented diffeomorphism
(external review 82, A3/A4): the corollary of `RawGraphPresentation.liftAlong_UL`. -/
theorem nonempty_rawGraphPresentation_transport_universe {W₀ : CompactCarrier.{0}}
    {W : CompactCarrier.{u}} (ψ : W₀.Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier)
    (hψ : ψ.preservesOrientation W₀.orientation W.orientation)
    (h : Nonempty (RawGraphPresentation.{0} W₀)) : Nonempty (RawGraphPresentation.{u} W) :=
  h.elim fun G => ⟨G.liftAlong_UL ψ hψ⟩

end GC.GraphManifold
