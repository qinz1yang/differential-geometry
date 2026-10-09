import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import DifferentialGeometry.Topology.Manifold.BallChartTransport

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

theorem finiteConnectedSum_append_of_connectedSumLaws (h : connectedSumLaws.{u})
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold) := by
  rcases h with ⟨hunitR, hunitL, -, hassoc, -, htransportR⟩
  exact finiteConnectedSum_append_of_unit_assoc_transport
    hunitR hunitL hassoc htransportR L K

theorem finiteConnectedSum_perm_of_connectedSumLaws (h : connectedSumLaws.{u})
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)} (hp : L.Perm K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) := by
  rcases h with ⟨-, -, hcomm, hassoc, htransportL, htransportR⟩
  exact finiteConnectedSum_perm_of_comm_assoc_transport
    hcomm hassoc htransportL htransportR hp

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
      (finiteConnectedSum
        (L.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold) := by
  exact finiteConnectedSum_opposite_of_binary_transport hbin h.2.2.2.2.2 hsphere L

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u v u' v'

def connectedSumTransport : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3) (M' : ConnectedClosedOrientedManifold.{v} 3)
    (N : ConnectedClosedOrientedManifold.{u'} 3) (N' : ConnectedClosedOrientedManifold.{v'} 3),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      M.toClosedOrientedManifold M'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      N.toClosedOrientedManifold N'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum M N).toClosedOrientedManifold
      (connectedSum M' N').toClosedOrientedManifold)

theorem standardThreeSphereLift_orientedDiffeomorph :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (standardThreeSphereLift.{u}).toClosedOrientedManifold
      (standardThreeSphereLift.{v}).toClosedOrientedManifold) :=
  ⟨(ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, u}
      standardThreeSphere.toClosedOrientedManifold).symm.trans
    (ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, v}
      standardThreeSphere.toClosedOrientedManifold)⟩

theorem finiteConnectedSum_congr_of_connectedSumTransport
    (h : connectedSumTransport.{u, v, u, v})
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

theorem connectedSumTransport_of_binaryConnectedSumLaws
    (h : binaryConnectedSumLaws.{u}) : connectedSumTransport.{u, u, u, u} :=
  h.2.2.2.2

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

def SelfTransport : Prop :=
  ∀ {M : ConnectedClosedOrientedManifold.{u} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold),
    OrientedBallChartTransport c c'

def OrientedBallChartPullback : Prop :=
  ∀ {M M' : ClosedOrientedManifold.{u} 3}
    (Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier)
    (c' : OrientedBallChart M'),
    Φ.preservesOrientation M.orientation M'.orientation →
    ∃ c : OrientedBallChart M,
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        Φ (c.toBallChart.chart x) = c'.toBallChart.chart x

theorem connectedSumQuotient_diffeomorph_of_selfTransport (h : SelfTransport.{u})
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{u} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    letI := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    letI := ConnectedSumQuotient.csChartedSpace c'.toBallChart d'.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c'.toBallChart d'.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    Nonempty (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) :=
  nonempty_connectedSumQuotient_diffeomorph_of_orientedBallChartTransport c c' d d' a
    (h c c') (h d d')

theorem connectedSum_diffeomorph_of_ballChartTransport
    (M : ConnectedClosedOrientedManifold.{u} 3) (P P' : ConnectedClosedOrientedManifold.{u} 3)
    (d : OrientedBallChart P.toClosedOrientedManifold)
    (d' : OrientedBallChart P'.toClosedOrientedManifold)
    (hP : Manifold.BallChartTransport (orientedBallChart P).toBallChart d.toBallChart)
    (hP' : Manifold.BallChartTransport (orientedBallChart P').toBallChart d'.toBallChart)
    (Ψ : P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P'.Carrier)
    (hΨ : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      Ψ (d.toBallChart.chart x) = d'.toBallChart.chart x) :
    Nonempty ((connectedSum M P).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum M P').toClosedOrientedManifold.Carrier) := by
  have hcanon : Manifold.BallChartTransport
      (orientedBallChart M).toBallChart (orientedBallChart M).toBallChart :=
    Manifold.BallChartTransport.refl _
  let W : ConnectedClosedOrientedManifold.{u} 3 :=
    (smoothConnectedSum M P (orientedBallChart M) d boundaryAttachment)
      |>.toConnectedClosedOrientedManifold
  let W' : ConnectedClosedOrientedManifold.{u} 3 :=
    (smoothConnectedSum M P' (orientedBallChart M) d' boundaryAttachment)
      |>.toConnectedClosedOrientedManifold
  have step1 : Nonempty
      ((connectedSum M P).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ W.Carrier) :=
    nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
      (orientedBallChart M) (orientedBallChart M) (orientedBallChart P) d boundaryAttachment
      hcanon hP
  have step2 : Nonempty (W.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ W'.Carrier) :=
    csTransportDiffeomorph (orientedBallChart M) (orientedBallChart M) d d'
      boundaryAttachment (Diffeomorph.refl (𝓡 3) M.Carrier ∞) Ψ (fun _ _ => rfl) hΨ
  have step3 : Nonempty (W'.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum M P').toClosedOrientedManifold.Carrier) :=
    nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
      (orientedBallChart M) (orientedBallChart M) d' (orientedBallChart P') boundaryAttachment
      hcanon (Manifold.BallChartTransport.symm hP')
  exact step1.elim fun f => step2.elim fun g => step3.elim fun k => ⟨f.trans (g.trans k)⟩

theorem connectedSum_diffeomorph_of_ballChartTransport_left
    (Q : ConnectedClosedOrientedManifold.{u} 3) (P P' : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart P.toClosedOrientedManifold)
    (c' : OrientedBallChart P'.toClosedOrientedManifold)
    (hP : Manifold.BallChartTransport (orientedBallChart P).toBallChart c.toBallChart)
    (hP' : Manifold.BallChartTransport (orientedBallChart P').toBallChart c'.toBallChart)
    (Φ : P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P'.Carrier)
    (hΦ : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      Φ (c.toBallChart.chart x) = c'.toBallChart.chart x) :
    Nonempty ((connectedSum P Q).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum P' Q).toClosedOrientedManifold.Carrier) := by
  have hcanon : Manifold.BallChartTransport
      (orientedBallChart Q).toBallChart (orientedBallChart Q).toBallChart :=
    Manifold.BallChartTransport.refl _
  let W : ConnectedClosedOrientedManifold.{u} 3 :=
    (smoothConnectedSum P Q c (orientedBallChart Q) boundaryAttachment)
      |>.toConnectedClosedOrientedManifold
  let W' : ConnectedClosedOrientedManifold.{u} 3 :=
    (smoothConnectedSum P' Q c' (orientedBallChart Q) boundaryAttachment)
      |>.toConnectedClosedOrientedManifold
  have step1 : Nonempty
      ((connectedSum P Q).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ W.Carrier) :=
    nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
      (orientedBallChart P) c (orientedBallChart Q) (orientedBallChart Q) boundaryAttachment
      hP hcanon
  have step2 : Nonempty (W.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ W'.Carrier) :=
    csTransportDiffeomorph c c' (orientedBallChart Q) (orientedBallChart Q)
      boundaryAttachment Φ (Diffeomorph.refl (𝓡 3) Q.Carrier ∞) hΦ (fun _ _ => rfl)
  have step3 : Nonempty (W'.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum P' Q).toClosedOrientedManifold.Carrier) :=
    nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
      c' (orientedBallChart P') (orientedBallChart Q) (orientedBallChart Q) boundaryAttachment
      (Manifold.BallChartTransport.symm hP') hcanon
  exact step1.elim fun f => step2.elim fun g => step3.elim fun k => ⟨f.trans (g.trans k)⟩

theorem connectedSum_transport_right_of_orientedPullback
    (hself : SelfTransport.{u}) (hpull : OrientedBallChartPullback.{u})
    (M : ConnectedClosedOrientedManifold.{u} 3) (P P' : ConnectedClosedOrientedManifold.{u} 3)
    (Ψ : P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P'.Carrier)
    (hΨ : Ψ.preservesOrientation P.orientation P'.orientation) :
    Nonempty ((connectedSum M P).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum M P').toClosedOrientedManifold.Carrier) := by
  obtain ⟨d, hd⟩ := hpull Ψ (orientedBallChart P') hΨ
  exact connectedSum_diffeomorph_of_ballChartTransport M P P' d (orientedBallChart P')
    (hself (orientedBallChart P) d).toBallChartTransport (Manifold.BallChartTransport.refl _) Ψ hd

theorem connectedSum_transport_left_of_orientedPullback
    (hself : SelfTransport.{u}) (hpull : OrientedBallChartPullback.{u})
    (M M' : ConnectedClosedOrientedManifold.{u} 3) (Q : ConnectedClosedOrientedManifold.{u} 3)
    (Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier)
    (hΦ : Φ.preservesOrientation M.orientation M'.orientation) :
    Nonempty ((connectedSum M Q).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum M' Q).toClosedOrientedManifold.Carrier) := by
  obtain ⟨c, hc⟩ := hpull Φ (orientedBallChart M') hΦ
  exact connectedSum_diffeomorph_of_ballChartTransport_left Q M M' c (orientedBallChart M')
    (hself (orientedBallChart M) c).toBallChartTransport (Manifold.BallChartTransport.refl _) Φ hc

end DifferentialGeometry.Topology
