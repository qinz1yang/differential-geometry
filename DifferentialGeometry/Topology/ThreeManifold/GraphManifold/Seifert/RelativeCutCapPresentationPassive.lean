import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeCutCapPresentationData
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeCutCapPresentationProfiles
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitSphere

/-!
# Passive hyperbolic profiles and complete seam counts

The old hyperbolic geometry is transported from its actual piece interior to the compact
component carrier. The surviving-seam equivalence counts all capped components together and
keeps the deleted seam separate from the protected subset.
-/

set_option autoImplicit false
noncomputable section
open Set Function GC.Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert

theorem relativeCapComponentHyperbolicProfile {W : CompactCarrier.{u}}
    (T : TorusPresentation W) (i : Fin T.components.count)
    (g : T.cutCarrier.InteriorGeometry (T.components.piece i))
    (hg :
      letI := Manifold.interiorChartedSpace T.cutCarrier.model ∞
        (M := T.cutCarrier.pieceInterior (T.components.piece i))
      letI := Manifold.interiorIsManifold T.cutCarrier.model ∞
        (M := T.cutCarrier.pieceInterior (T.components.piece i))
      g.model = .hyperbolic) :
    ∃ h : (componentCarrier T.cutCarrier T.components i).InteriorGeometry ⊤,
      letI := Manifold.interiorChartedSpace
        (componentCarrier T.cutCarrier T.components i).model ∞
        (M := (componentCarrier T.cutCarrier T.components i).pieceInterior ⊤)
      letI := Manifold.interiorIsManifold
        (componentCarrier T.cutCarrier T.components i).model ∞
        (M := (componentCarrier T.cutCarrier T.components i).pieceInterior ⊤)
      h.model = .hyperbolic :=
  relativeCapHyperbolicProfile (componentInteriorDiffeomorph T.cutCarrier T.components i) g hg

theorem controlledCapPresentation_surviving_count
    {M : ConnectedClosedOrientedManifold.{u} 3} {Q : ClosedOrientedManifold.{u} 3}
    {T : TorusPresentation (NoCuts.carrier M)}
    {X : SphericalCutCapTransition M.toClosedOrientedManifold Q}
    {j : Fin T.pairing.count} {prot : Finset (Fin T.pairing.count)}
    {support frozen : Finset (Fin T.components.count)}
    {oldKind : Fin T.components.count → ℕ}
    (D : ControlledCapPresentation T X j prot support frozen oldKind) :
    Nat.card (Σ c, Fin (D.presentation c).pairing.count) + 1 = T.pairing.count := by
  rw [Nat.card_congr D.seamEquiv, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  have hp := Fin.pos j
  omega

theorem controlledCapPresentation_protected_ne_removed
    {M : ConnectedClosedOrientedManifold.{u} 3} {Q : ClosedOrientedManifold.{u} 3}
    {T : TorusPresentation (NoCuts.carrier M)}
    {X : SphericalCutCapTransition M.toClosedOrientedManifold Q}
    {j : Fin T.pairing.count} {prot : Finset (Fin T.pairing.count)}
    {support frozen : Finset (Fin T.components.count)}
    {oldKind : Fin T.components.count → ℕ}
    (D : ControlledCapPresentation T X j prot support frozen oldKind)
    (r : {r : Fin T.pairing.count // r ∈ prot}) : r.val ≠ j := by
  rw [← D.marked_old r]
  exact (D.seamEquiv (D.marked r)).property

section SingleTube

variable {M : ConnectedClosedOrientedManifold.{u} 3} {Q : ClosedOrientedManifold.{u} 3}
  {T : TorusPresentation (NoCuts.carrier M)}
  {X : SphericalCutCapTransition M.toClosedOrientedManifold Q}
  {j : Fin T.pairing.count} {prot : Finset (Fin T.pairing.count)}
  {support frozen : Finset (Fin T.components.count)}
  {oldKind : Fin T.components.count → ℕ}
  (D : ControlledCapPresentation T X j prot support frozen oldKind) (a : X.tubes.Index)
  [Subsingleton X.tubes.Index]

theorem controlledCapPresentation_separating_count
    (hne : X.cutCapVertex a false ≠ X.cutCapVertex a true) :
    (D.presentation (X.cutCapVertex a false)).pairing.count +
      (D.presentation (X.cutCapVertex a true)).pairing.count + 1 = T.pairing.count := by
  have hinj : Injective (X.cutCapVertex a) := by
    intro b b' hb
    cases b <;> cases b'
    · rfl
    · exact False.elim (hne hb)
    · exact False.elim (hne hb.symm)
    · rfl
  have hsur : Surjective (X.cutCapVertex a) := by
    intro c
    rcases eq_cutCapVertex_of_subsingleton X a c with hc | hc
    · exact ⟨false, hc.symm⟩
    · exact ⟨true, hc.symm⟩
  let e := Equiv.ofBijective (X.cutCapVertex a) ⟨hinj, hsur⟩
  have hcard := Nat.card_congr
    (Equiv.sigmaCongrLeft (β := fun c => Fin (D.presentation c).pairing.count) e)
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin, Fintype.sum_bool] at hcard
  have htotal := controlledCapPresentation_surviving_count D
  rw [← hcard] at htotal
  change (D.presentation (X.cutCapVertex a true)).pairing.count +
    (D.presentation (X.cutCapVertex a false)).pairing.count + 1 = _ at htotal
  omega

theorem controlledCapPresentation_nonseparating_count
    (heq : X.cutCapVertex a false = X.cutCapVertex a true) :
    (D.presentation (X.cutCapVertex a false)).pairing.count + 1 = T.pairing.count := by
  have hall : ∀ c, c = X.cutCapVertex a false := by
    intro c
    exact (eq_cutCapVertex_of_subsingleton X a c).elim id (fun h => h.trans heq.symm)
  let e : Unit ≃ ConnectedComponents X.capped.Carrier :=
    { toFun := fun _z => X.cutCapVertex a false
      invFun := fun _c => ()
      left_inv := fun z => by cases z; rfl
      right_inv := fun c => (hall c).symm }
  have hcard := Nat.card_congr
    (Equiv.sigmaCongrLeft (β := fun c => Fin (D.presentation c).pairing.count) e)
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin, Fintype.sum_unique] at hcard
  have htotal := controlledCapPresentation_surviving_count D
  rw [← hcard] at htotal
  exact htotal

end SingleTube

end GC.Seifert
