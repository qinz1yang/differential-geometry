import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

noncomputable section

namespace DifferentialGeometry.Topology

universe u v

def finiteConnectedSum : List (ConnectedClosedOrientedManifold.{u} 3) →
    ConnectedClosedOrientedManifold.{u} 3
  | [] => standardThreeSphereLift
  | [M] => M
  | M :: N :: L => connectedSum M (finiteConnectedSum (N :: L))

@[simp]
theorem finiteConnectedSum_nil :
    finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold.{u} 3)) =
      standardThreeSphereLift := rfl

@[simp]
theorem finiteConnectedSum_singleton (M : ConnectedClosedOrientedManifold.{u} 3) :
    finiteConnectedSum [M] = M := rfl

@[simp]
theorem finiteConnectedSum_cons_cons (M N : ConnectedClosedOrientedManifold.{u} 3)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    finiteConnectedSum (M :: N :: L) = connectedSum M (finiteConnectedSum (N :: L)) := rfl


private theorem nonemptyOrientedDiffeomorph_symm {X Y : ClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph X Y)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Y X) :=
  h.elim fun f => ⟨f.symm⟩

private theorem nonemptyOrientedDiffeomorph_trans {X Y Z : ClosedOrientedManifold.{u} 3}
    (h₁ : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph X Y))
    (h₂ : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Y Z)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph X Z) :=
  h₁.elim fun f => h₂.elim fun g => ⟨f.trans g⟩

theorem finiteConnectedSum_append_of_unit_assoc_transport
    (hunitR : ∀ X : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold
        X.toClosedOrientedManifold))
    (hunitL : ∀ X : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum standardThreeSphereLift.{u} X).toClosedOrientedManifold
        X.toClosedOrientedManifold))
    (hassoc : ∀ X Y Z : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum (connectedSum X Y) Z).toClosedOrientedManifold
        (connectedSum X (connectedSum Y Z)).toClosedOrientedManifold))
    (htransportR : ∀ X Y Y' : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        Y.toClosedOrientedManifold Y'.toClosedOrientedManifold) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum X Y).toClosedOrientedManifold
        (connectedSum X Y').toClosedOrientedManifold))
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold) := by
  induction L generalizing K with
  | nil =>
      rw [List.nil_append, finiteConnectedSum_nil]
      exact nonemptyOrientedDiffeomorph_symm (hunitL (finiteConnectedSum K))
  | cons M L ih =>
      cases L with
      | nil =>
          cases K with
          | nil =>
              simp only [finiteConnectedSum_nil, finiteConnectedSum_singleton]
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

theorem finiteConnectedSum_perm_of_comm_assoc_transport
    (hcomm : ∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum X Y).toClosedOrientedManifold
        (connectedSum Y X).toClosedOrientedManifold))
    (hassoc : ∀ X Y Z : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum (connectedSum X Y) Z).toClosedOrientedManifold
        (connectedSum X (connectedSum Y Z)).toClosedOrientedManifold))
    (htransportL : ∀ X X' Y : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        X.toClosedOrientedManifold X'.toClosedOrientedManifold) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum X Y).toClosedOrientedManifold
        (connectedSum X' Y).toClosedOrientedManifold))
    (htransportR : ∀ X Y Y' : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        Y.toClosedOrientedManifold Y'.toClosedOrientedManifold) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum X Y).toClosedOrientedManifold
        (connectedSum X Y').toClosedOrientedManifold))
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)} (hp : L.Perm K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) := by
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

theorem finiteConnectedSum_opposite_of_binary_transport
    (hbin : ∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum X Y).opposite.toClosedOrientedManifold
        (connectedSum X.opposite Y.opposite).toClosedOrientedManifold))
    (htransportR : ∀ X Y Y' : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        Y.toClosedOrientedManifold Y'.toClosedOrientedManifold) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum X Y).toClosedOrientedManifold
        (connectedSum X Y').toClosedOrientedManifold))
    (hsphere : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      standardThreeSphereLift.{u}.opposite.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold))
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).opposite.toClosedOrientedManifold
      (finiteConnectedSum
        (L.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold) := by
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

theorem standardThreeSphereLift_orientedDiffeomorph :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (standardThreeSphereLift.{u}).toClosedOrientedManifold
      (standardThreeSphereLift.{v}).toClosedOrientedManifold) :=
  ⟨(ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, u}
      standardThreeSphere.toClosedOrientedManifold).symm.trans
    (ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, v}
      standardThreeSphere.toClosedOrientedManifold)⟩

theorem finiteConnectedSum_congr_of_binary_transport
    (h : ∀ (M : ConnectedClosedOrientedManifold.{u} 3)
      (M' : ConnectedClosedOrientedManifold.{v} 3)
      (N : ConnectedClosedOrientedManifold.{u} 3)
      (N' : ConnectedClosedOrientedManifold.{v} 3),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold M'.toClosedOrientedManifold) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        N.toClosedOrientedManifold N'.toClosedOrientedManifold) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum M N).toClosedOrientedManifold
        (connectedSum M' N').toClosedOrientedManifold))
    {L : List (ConnectedClosedOrientedManifold.{u} 3)}
    {K : List (ConnectedClosedOrientedManifold.{v} 3)}
    (hf : List.Forall₂ (fun (M : ConnectedClosedOrientedManifold.{u} 3)
      (N : ConnectedClosedOrientedManifold.{v} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) := by
  induction hf with
  | nil => exact standardThreeSphereLift_orientedDiffeomorph
  | cons hhead htail ih =>
      cases htail with
      | nil => exact hhead
      | cons hhead' htail' =>
          exact h _ _ _ _ hhead ih

theorem finiteConnectedSum_unique
    (f : List (ConnectedClosedOrientedManifold.{u} 3) → ConnectedClosedOrientedManifold.{u} 3)
    (h0 : f [] = standardThreeSphereLift.{u})
    (h1 : ∀ M : ConnectedClosedOrientedManifold.{u} 3, f [M] = M)
    (h2 : ∀ (M N : ConnectedClosedOrientedManifold.{u} 3)
      (L : List (ConnectedClosedOrientedManifold.{u} 3)),
      f (M :: N :: L) = connectedSum M (f (N :: L))) :
    f = finiteConnectedSum := by
  funext L
  induction L with
  | nil => exact h0
  | cons M t ih =>
      cases t with
      | nil => exact h1 M
      | cons N L =>
          rw [h2 M N L, ih]
          rfl

end DifferentialGeometry.Topology
