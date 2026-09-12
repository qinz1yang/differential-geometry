import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

private theorem nonemptyOrientedDiffeomorph_symm {X Y : ClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph X Y)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Y X) :=
  h.elim fun f => ⟨f.symm⟩

private theorem nonemptyOrientedDiffeomorph_trans {X Y Z : ClosedOrientedManifold.{u} 3}
    (h₁ : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph X Y))
    (h₂ : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Y Z)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph X Z) :=
  h₁.elim fun f => h₂.elim fun g => ⟨f.trans g⟩

def binaryConnectedSumLaws : Prop :=
  (∀ X : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum standardThreeSphereLift.{u} X).toClosedOrientedManifold
      X.toClosedOrientedManifold)) ∧
  (∀ X : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold
      X.toClosedOrientedManifold)) ∧
  (∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).toClosedOrientedManifold
      (connectedSum Y X).toClosedOrientedManifold)) ∧
  (∀ X Y Z : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum (connectedSum X Y) Z).toClosedOrientedManifold
      (connectedSum X (connectedSum Y Z)).toClosedOrientedManifold)) ∧
  (∀ (X X' Y Y' : ConnectedClosedOrientedManifold.{u} 3),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      X.toClosedOrientedManifold X'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      Y.toClosedOrientedManifold Y'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).toClosedOrientedManifold
      (connectedSum X' Y').toClosedOrientedManifold))

def connectedSumLaws : Prop :=
  (∀ X : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold
      X.toClosedOrientedManifold)) ∧
  (∀ X : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum standardThreeSphereLift.{u} X).toClosedOrientedManifold
      X.toClosedOrientedManifold)) ∧
  (∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).toClosedOrientedManifold
      (connectedSum Y X).toClosedOrientedManifold)) ∧
  (∀ X Y Z : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum (connectedSum X Y) Z).toClosedOrientedManifold
      (connectedSum X (connectedSum Y Z)).toClosedOrientedManifold)) ∧
  (∀ (X X' Y : ConnectedClosedOrientedManifold.{u} 3),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      X.toClosedOrientedManifold X'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).toClosedOrientedManifold
      (connectedSum X' Y).toClosedOrientedManifold)) ∧
  (∀ (X Y Y' : ConnectedClosedOrientedManifold.{u} 3),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      Y.toClosedOrientedManifold Y'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).toClosedOrientedManifold
      (connectedSum X Y').toClosedOrientedManifold))

theorem connectedSumLaws_of_binaryConnectedSumLaws
    (h : binaryConnectedSumLaws.{u}) : connectedSumLaws.{u} := by
  rcases h with ⟨hunitL, hunitR, hcomm, hassoc, htransport⟩
  refine ⟨hunitR, hunitL, hcomm, hassoc, ?_, ?_⟩
  · intro X X' Y hX
    exact htransport X X' Y Y hX ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  · intro X Y Y' hY
    exact htransport X X Y Y' ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩ hY

def oppositeConnectedSumLaws : Prop :=
  (∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).opposite.toClosedOrientedManifold
      (connectedSum X.opposite Y.opposite).toClosedOrientedManifold)) ∧
  Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
    standardThreeSphereLift.{u}.opposite.toClosedOrientedManifold
    standardThreeSphereLift.{u}.toClosedOrientedManifold)

theorem finiteConnectedSum_append_of_connectedSumLaws (h : connectedSumLaws.{u})
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold) := by
  rcases h with ⟨hunitR, hunitL, -, hassoc, -, htransportR⟩
  induction L generalizing K with
  | nil =>
      rw [List.nil_append, finiteConnectedSum_nil]
      exact nonemptyOrientedDiffeomorph_symm (hunitL (finiteConnectedSum K))
  | cons M L ih =>
      cases L with
      | nil =>
          cases K with
          | nil =>
              simp only [List.append_nil, finiteConnectedSum_nil, finiteConnectedSum_singleton]
              exact nonemptyOrientedDiffeomorph_symm (hunitR M)
          | cons N K =>
              simp only [List.cons_append, List.nil_append, finiteConnectedSum_singleton,
                finiteConnectedSum_cons_cons]
              exact ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
      | cons N L =>
          simp only [List.cons_append, finiteConnectedSum_cons_cons]
          exact nonemptyOrientedDiffeomorph_trans
            (htransportR M (finiteConnectedSum ((N :: L) ++ K))
              (connectedSum (finiteConnectedSum (N :: L)) (finiteConnectedSum K)) (ih K))
            (nonemptyOrientedDiffeomorph_symm
              (hassoc M (finiteConnectedSum (N :: L)) (finiteConnectedSum K)))

theorem finiteConnectedSum_perm_of_connectedSumLaws (h : connectedSumLaws.{u})
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)} (hp : L.Perm K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) := by
  rcases h with ⟨-, -, hcomm, hassoc, htransportL, htransportR⟩
  refine List.Perm.rec (motive := fun L K _ =>
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold)) ?_ ?_ ?_ ?_ hp
  · exact ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  · intro x l₁ l₂ hl ih
    cases l₁ with
    | nil =>
        have hl₂ : l₂ = [] := List.Perm.eq_nil hl.symm
        subst hl₂
        exact ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
    | cons a l₁' =>
        cases l₂ with
        | nil => exact absurd (List.Perm.eq_nil hl) (by simp)
        | cons b l₂' =>
            simp only [finiteConnectedSum_cons_cons]
            exact htransportR x (finiteConnectedSum (a :: l₁'))
              (finiteConnectedSum (b :: l₂')) ih
  · intro x y l
    cases l with
    | nil =>
        simp only [finiteConnectedSum_singleton, finiteConnectedSum_cons_cons]
        exact hcomm y x
    | cons z l =>
        simp only [finiteConnectedSum_cons_cons]
        exact nonemptyOrientedDiffeomorph_trans
          (nonemptyOrientedDiffeomorph_symm (hassoc y x (finiteConnectedSum (z :: l))))
          (nonemptyOrientedDiffeomorph_trans
            (htransportL (connectedSum y x) (connectedSum x y) (finiteConnectedSum (z :: l))
              (hcomm y x))
            (hassoc x y (finiteConnectedSum (z :: l))))
  · intro l₁ l₂ l₃ h₁ h₂ ih₁ ih₂
    exact nonemptyOrientedDiffeomorph_trans ih₁ ih₂

theorem finiteConnectedSum_congr_of_connectedSumLaws (h : connectedSumLaws.{u})
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hf : List.Forall₂ (fun (M N : ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) := by
  rcases h with ⟨-, -, -, -, htransportL, htransportR⟩
  refine List.Forall₂.rec (motive := fun L K _ =>
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold)) ?_ ?_ hf
  · exact ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  · intro M N L' K' hM hL' ih
    cases L' with
    | nil =>
        have hK' : K' = [] := List.forall₂_nil_left_iff.mp hL'
        subst hK'
        simp only [finiteConnectedSum_singleton]
        exact hM
    | cons M2 L'' =>
        cases K' with
        | nil => exact absurd (List.forall₂_nil_right_iff.mp hL') (by simp)
        | cons N2 K'' =>
            simp only [finiteConnectedSum_cons_cons]
            exact nonemptyOrientedDiffeomorph_trans
              (htransportL M N (finiteConnectedSum (M2 :: L'')) hM)
              (htransportR N (finiteConnectedSum (M2 :: L''))
                (finiteConnectedSum (N2 :: K'')) ih)

theorem finiteConnectedSum_opposite_of_connectedSumLaws
    (h : connectedSumLaws.{u})
    (hbin : ∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum X Y).opposite.toClosedOrientedManifold
        (connectedSum X.opposite Y.opposite).toClosedOrientedManifold))
    (hsphere : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      standardThreeSphereLift.{u}.opposite.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold))
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).opposite.toClosedOrientedManifold
      (finiteConnectedSum (L.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold) := by
  rcases h with ⟨-, -, -, -, htransportL, htransportR⟩
  induction L with
  | nil => simpa only [List.map_nil, finiteConnectedSum_nil] using hsphere
  | cons M L ih =>
      cases L with
      | nil => exact ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
      | cons N L' =>
          simp only [List.map_cons, finiteConnectedSum_cons_cons]
          exact nonemptyOrientedDiffeomorph_trans
            (hbin M (finiteConnectedSum (N :: L')))
            (htransportR M.opposite (finiteConnectedSum (N :: L')).opposite
              (finiteConnectedSum ((N :: L').map ConnectedClosedOrientedManifold.opposite)) ih)

end DifferentialGeometry.Topology
