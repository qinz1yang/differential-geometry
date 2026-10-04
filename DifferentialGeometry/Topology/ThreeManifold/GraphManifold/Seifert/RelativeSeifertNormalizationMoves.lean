import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationStage
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationLedger

/-!
# The move contracts of the relative normalisation

Lane BR, tier R5, contracts (design `handoffs/20261004-design-br-relative-normalisation.md` §3.3–3.4
with review 26 §2–5). These are the exact types of the three explicit hypotheses of the step; they
are used only as arguments, never as conclusions, as P0a did with `MoveSplitTerminalRaw`.

`FrozenLedger κ σ i σ' i'` is the ledger of a passive frozen piece: an orientation-preserving
diffeomorphism of the actual compact component carriers commuting with the cut maps up to `κ`
(`Eq` for a move on the same manifold, `coreTrack X c` through a surgery). It is never the identity
by fiat: a contraction changes the cut carrier and the piece indices.

`MX` (ledger-retaining mixed merge and absorb, Codex lane X56): at an inner merge or absorb seam
of a mixed stage there is a mixed stage of the same manifold with one inner seam fewer, a bijection
of protected seams with exact `CollarLedger Eq` collar equations (torus reparametrisation and
positive rescaling allowed), and a bijection of frozen pieces with frozen ledgers.

`MixedSplit` (controlled mixed split producer: N2c's split tube and capped assembly with N4's side
data and frozen pieces carried passively): at an inner split seam there is an actual single-tube
spherical cut-cap transition whose surgery region avoids every protected zero torus, a mixed stage
on EVERY actual capped component (retained and discarded) of smaller inner-seam count, and
bijections of protected seams and frozen pieces onto the disjoint unions over the components, with
`CollarLedger (coreTrack X c)` collar equations and frozen ledgers through the core.

`OrientedSingleSphere` is the statement of tier R7: a single-tube transition of a closed connected
oriented `M` gives `M ≅⁺ A # B` (two components) or `M ≅⁺ A # S² × S¹` (one component), with the
capped components oriented as components of the capped manifold.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

local macro "OIso " A:term:max ppSpace B:term:max : term =>
  `(Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
    (ConnectedClosedOrientedManifold.toClosedOrientedManifold $A)
    (ConnectedClosedOrientedManifold.toClosedOrientedManifold $B)))

structure FrozenLedger {Q Q' : ConnectedClosedOrientedManifold.{u} 3}
    (κ : Q.Carrier → Q'.Carrier → Prop) (σ : MixedStage Q) (i : Fin σ.toTorus.components.count)
    (σ' : MixedStage Q') (i' : Fin σ'.toTorus.components.count) where
  diffeo : (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components i).Carrier ≃ₘ⟮
    (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components i).model,
    (componentCarrier σ'.toTorus.cutCarrier σ'.toTorus.components i').model⟯
    (componentCarrier σ'.toTorus.cutCarrier σ'.toTorus.components i').Carrier
  oriented : diffeo.preservesOrientation
    (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components i).orientation
    (componentCarrier σ'.toTorus.cutCarrier σ'.toTorus.components i').orientation
  map : ∀ x, κ (σ.toTorus.cutMap x.val) (σ'.toTorus.cutMap (diffeo x).val)

def MX : Prop :=
  ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (σ : MixedStage Q)
    (j : Fin σ.toTorus.pairing.count) (b : Bool), σ.IsMergeSeam j b ∨ σ.IsAbsorbSeam j b →
      ∃ (σ' : MixedStage Q) (e : σ.ProtSeam ≃ σ'.ProtSeam) (f : σ.Frozen ≃ σ'.Frozen),
        σ'.innerCount + 1 = σ.innerCount ∧
        (∀ k, Nonempty (CollarLedger Eq (σ.toTorus.seam k.1) (σ'.toTorus.seam (e k).1))) ∧
        ∀ i, Nonempty (FrozenLedger Eq σ i.1 σ' (f i).1)

def MixedSplit : Prop :=
  ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (σ : MixedStage Q)
    (j : Fin σ.toTorus.pairing.count) (b : Bool), σ.IsSplitSeam j b →
      ∃ (P : ClosedOrientedManifold.{u} 3)
        (X : SphericalCutCapTransition Q.toClosedOrientedManifold P)
        (τ : ∀ c : ConnectedComponents X.capped.Carrier, MixedStage (X.capped.component c))
        (e : σ.ProtSeam ≃ Σ c, (τ c).ProtSeam) (f : σ.Frozen ≃ Σ c, (τ c).Frozen),
        Subsingleton X.tubes.Index ∧ Nonempty X.tubes.Index ∧
        (∀ k ∈ σ.prot, Disjoint (range (σ.toTorus.seamTorus k)) X.tubes.surgeryRegion) ∧
        (∀ c, (τ c).innerCount < σ.innerCount) ∧
        (∀ k, Nonempty (CollarLedger (coreTrack X (e k).1) (σ.toTorus.seam k.1)
          ((τ (e k).1).toTorus.seam (e k).2.1))) ∧
        ∀ i, Nonempty (FrozenLedger (coreTrack X (f i).1) σ i.1 (τ (f i).1) (f i).2.1)

def OrientedSingleSphere : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3) (P : ClosedOrientedManifold.{u} 3)
    (X : SphericalCutCapTransition M.toClosedOrientedManifold P) (a : X.tubes.Index),
    Subsingleton X.tubes.Index →
      (X.cutCapVertex a false ≠ X.cutCapVertex a true →
        OIso (connectedSum (X.capped.component (X.cutCapVertex a false))
          (X.capped.component (X.cutCapVertex a true))) M) ∧
      (X.cutCapVertex a false = X.cutCapVertex a true →
        OIso (connectedSum (X.capped.component (X.cutCapVertex a false))
          sphereTwoTimesCircleLift.ulift.{0, u}) M)

end GC.Seifert.RelativeNormalization
