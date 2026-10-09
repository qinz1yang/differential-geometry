import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.NormalizeTerminal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedBelow
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.HopfSphere
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.ConnectedSum.OppositeSumOrientation

/-!
# The strengthened split move from the capped surgery

Chapter 5 plan P0, the backend of `MoveSplitTerminalRaw` (review 19 §6.2). Three steps.

The terminal leaf `S² × S¹`. The product chart of `sphereTwoTimesCircleLift`, read through the
universe lifts of the carrier and of the two-sphere (`sphereTwoSurfaceLift`), is a circle
fibration of the whole universe-lifted carrier (`CircleFibration.ofProductDiffeomorph`), hence
the one-piece raw presentation `sphereTwoTimesCircleUliftRawGraphPresentation`, the universe-`u`
form of `sphereTwoTimesCircleRawGraphPresentation`. With the standard-factor proofs of `S² × S¹`
and of its opposite this gives terminal presentations of both
(`TerminalPresentation.sphereTwoTimesCircle`,
`TerminalPresentation.nonempty_sphereTwoTimesCircle_opposite`).

Oriented reconstruction. `FibreFillingSphereSurgery` gives `Q ≅ A # B` with
`n_A + n_B + 1 = n` when the split sphere separates, and `Q ≅ A # S² × S¹` with `n_A + 1 = n`
otherwise, by unoriented diffeomorphisms. If such a diffeomorphism reverses orientation,
`Q ≅ A̅ # B̅` orientedly (`connectedSum_opposite`); opposite elementary presentations keep the
count (`terminalBelow_of_complexity_lt`) and `S² × S¹` is terminal in both orientations. So the
summands with an elementary presentation descend strictly and the `S² × S¹` summand is an
immediate terminal leaf: `moveSplitTerminalRaw_of_fibreFillingSphereSurgery`.

The capped surgery. For a linear split seam N2c's `exists_splitSeamSurgery` gives the explicit
cut-cap transition along the split tube with its separating/non-separating dichotomy,
`exists_cappedConditions` the avoidance of every other piece and every other seam collar, and
`exists_cappedElementary_of_sideData` the capped elementary presentations with the seam counts
`n_A + n_B + 1 = n` and `n′ + 1 = n`, from the capped solid tori `SideData` of the two sides;
`TorusMappingClassLinear`, proved, linearizes every presentation. The only input left is the
existence of `SideData`, the ledger item N4 (`exists_sideData`), which enters here as the
explicit hypothesis `hN4` with exactly that statement: `fibreFillingSphereSurgery_of_sideData`
and `moveSplitTerminalRaw_of_sideData`.
-/

set_option autoImplicit false

noncomputable section
open Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

attribute [local instance] uliftChartedSpace isManifold_ulift

def sphereTwoTimesCircleUliftProduct :
    (sphereTwoTimesCircleLift.ulift.{0, u}).Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯
      (SphereTwoLift.{u} × Circle) :=
  (ClosedOrientedManifold.uliftDiffeomorph.{0, u}
      sphereTwoTimesCircleLift.toClosedOrientedManifold).symm.trans
    (sphereTwoTimesCircleModelCopy.equiv.symm.trans
      ((uliftDiffeomorph (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwoLift.{u}).prodCongr
        sphereOneDiffeomorphCircle))

def sphereTwoTimesCircleUliftRawGraphPresentation :
    RawGraphPresentation (NoCuts.carrier sphereTwoTimesCircleLift.ulift.{0, u}) :=
  RawGraphPresentation.ofClosedCircleFibration _
    (CircleFibration.ofProductDiffeomorph sphereTwoSurfaceLift.{u}
      ((topOpensDiffeomorph (I := 𝓡 3) sphereTwoTimesCircleLift.ulift.{0, u}.Carrier).trans
        sphereTwoTimesCircleUliftProduct))

end GC.GraphManifold

namespace GC.Seifert

open ElementaryPresentation

namespace TerminalPresentation

def sphereTwoTimesCircle : TerminalPresentation sphereTwoTimesCircleLift.ulift.{0, u} where
  raw := sphereTwoTimesCircleUliftRawGraphPresentation
  factor := seifertFactor_sphereTwoTimesCircle

theorem nonempty_sphereTwoTimesCircle_opposite :
    Nonempty (TerminalPresentation sphereTwoTimesCircleLift.ulift.{0, u}.opposite) := by
  obtain ⟨G⟩ := rawGraphPresentation_of_diffeomorph
    (N := sphereTwoTimesCircleLift.ulift.{0, u}.opposite)
    sphereTwoTimesCircleUliftRawGraphPresentation (Diffeomorph.refl (𝓡 3) _ ∞)
  exact ⟨⟨G, seifertFactor_sphereTwoTimesCircle_opposite⟩⟩

end TerminalPresentation

theorem terminalBelow_of_complexity_lt {n : ℕ} {A : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier A)) (h : E.complexity < n) :
    TerminalBelow n A ∧ TerminalBelow n A.opposite := by
  obtain ⟨E', hE'⟩ := E.exists_of_diffeomorph (N := A.opposite)
    (Diffeomorph.refl (𝓡 3) A.Carrier ∞)
  exact ⟨Or.inr ⟨E, h⟩, Or.inr ⟨E', hE'.trans_lt h⟩⟩

theorem exists_terminalBelow_split_of_diffeomorph {n : ℕ}
    {Q A B : ConnectedClosedOrientedManifold.{u} 3}
    (d : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum A B).Carrier)
    (hA : TerminalBelow n A ∧ TerminalBelow n A.opposite)
    (hB : TerminalBelow n B ∧ TerminalBelow n B.opposite) :
    ∃ A' B' : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum A' B').toClosedOrientedManifold Q.toClosedOrientedManifold) ∧
      TerminalBelow n A' ∧ TerminalBelow n B' := by
  rcases orientedDiffeomorph_or_opposite_of_diffeomorph Q (connectedSum A B) d with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact ⟨A, B, ⟨e.symm⟩, hA.1, hB.1⟩
  · obtain ⟨c⟩ := connectedSum_opposite A B
    exact ⟨A.opposite, B.opposite, ⟨(e.trans c).symm⟩, hA.2, hB.2⟩

theorem moveSplitTerminalRaw_of_fibreFillingSphereSurgery (h : FibreFillingSphereSurgery.{u}) :
    MoveSplitTerminalRaw.{u} := by
  intro Q E j b hs
  rcases h Q E j b hs with ⟨A, B, EA, EB, ⟨d⟩, hc⟩ | ⟨A, EA, ⟨d⟩, hc⟩
  · exact exists_terminalBelow_split_of_diffeomorph d
      (terminalBelow_of_complexity_lt EA (by omega))
      (terminalBelow_of_complexity_lt EB (by omega))
  · exact exists_terminalBelow_split_of_diffeomorph d
      (terminalBelow_of_complexity_lt EA (by omega))
      ⟨Or.inl ⟨TerminalPresentation.sphereTwoTimesCircle⟩,
        Or.inl TerminalPresentation.nonempty_sphereTwoTimesCircle_opposite⟩

theorem fibreFillingSphereSurgery_of_sideData
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂)) :
    FibreFillingSphereSurgery.{u} := by
  intro Q E₀ j b h₀
  set E := E₀.linearize torusMappingClassLinear_holds
  have h : E.IsSplitSeam j b := (E₀.isSplitSeam_linearize torusMappingClassLinear_holds j b).mpr h₀
  have hlin : E.IsLinearSeam j := E₀.hasLinearSeams_linearize torusMappingClassLinear_holds j
  obtain ⟨P, X, a, hsub, hX, -, hdich⟩ := E.exists_splitSeamSurgery j b h hlin
  have := hsub
  obtain ⟨δ₁, hδ₁, hcond⟩ := E.exists_cappedConditions h hlin hX a
  obtain ⟨δ₀, hδ₀, hside⟩ := hN4 Q E h hlin hX X.capping a
  obtain ⟨D⟩ := hside (min δ₁ δ₀) (lt_min hδ₁ hδ₀) (min_le_right _ _)
  have hC := hcond (min δ₁ δ₀) (lt_min hδ₁ hδ₀) (min_le_left _ _)
  have hE := exists_cappedElementary_of_sideData E h X a D hC
  rcases hdich with ⟨hne, hd⟩ | ⟨heq, hd⟩
  · obtain ⟨EA, EB, hc⟩ := hE.1 hne
    exact Or.inl ⟨_, _, EA, EB, hd, hc⟩
  · obtain ⟨EA, hc⟩ := hE.2 heq
    exact Or.inr ⟨_, EA, hd, hc⟩

theorem moveSplitTerminalRaw_of_sideData
    (hN4 : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
      {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
      {T : SphericalTubeSystem Q.toClosedOrientedManifold}
      (_ : T = E.splitSeamTube j b h hlin) {N : ClosedOrientedManifold.{u} 3}
      (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
        ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂)) :
    MoveSplitTerminalRaw.{u} :=
  moveSplitTerminalRaw_of_fibreFillingSphereSurgery (fibreFillingSphereSurgery_of_sideData hN4)

end GC.Seifert
