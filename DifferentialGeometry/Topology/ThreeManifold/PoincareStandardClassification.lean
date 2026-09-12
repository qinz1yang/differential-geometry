import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormTrivial
import DifferentialGeometry.Topology.FundamentalGroup.SphericalQuotient
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private theorem exists_orientedDiffeomorph_finiteConnectedSum_standardThreeSphere
    (hunit : ∀ M : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum M standardThreeSphereLift.{u}).toClosedOrientedManifold
        M.toClosedOrientedManifold))
    (hcongr : ∀ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
      List.Forall₂ (fun (M N : ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold
        (finiteConnectedSum K).toClosedOrientedManifold))
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F.toClosedOrientedManifold standardThreeSphereLift.{u}.toClosedOrientedManifold)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  induction L with
  | nil =>
    exact ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  | cons M L ih =>
    cases L with
    | nil => exact hL M (by simp)
    | cons N L =>
      have ih' : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (finiteConnectedSum (N :: L)).toClosedOrientedManifold
          standardThreeSphereLift.{u}.toClosedOrientedManifold) :=
        ih fun F hF => hL F (by simp [hF])
      have hforall : List.Forall₂ (fun (M N : ConnectedClosedOrientedManifold.{u} 3) =>
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            M.toClosedOrientedManifold N.toClosedOrientedManifold))
          [M, finiteConnectedSum (N :: L)] [M, standardThreeSphereLift.{u}] :=
        List.Forall₂.cons ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
          (List.Forall₂.cons ih' List.Forall₂.nil)
      obtain ⟨c⟩ := hcongr [M, finiteConnectedSum (N :: L)] [M, standardThreeSphereLift.{u}]
        hforall
      obtain ⟨u⟩ := hunit M
      obtain ⟨s⟩ := hL M (by simp)
      exact ⟨c.trans (u.trans s)⟩

private theorem not_subsingleton_multiplicative_int :
    ¬ Subsingleton (Multiplicative ℤ) := fun h =>
  Int.zero_ne_one (Multiplicative.ofAdd.injective (h.elim _ _))

private theorem exists_orientedDiffeomorph_standardThreeSphere_of_isStandardFactor
    (hquot : ∀ (G : SphericalSpaceFormGroup) (p : G.manifold.Carrier),
      Nonempty (FundamentalGroup G.manifold.Carrier p ≃* G.group))
    (htrivial : ∀ (G : SphericalSpaceFormGroup), Subsingleton G.group →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        G.manifold.toClosedOrientedManifold
        standardThreeSphereLift.{u}.toClosedOrientedManifold))
    (hproduct : ∀ p : SphereTwoTimesCircle,
      Nonempty (FundamentalGroup SphereTwoTimesCircle p ≃* Multiplicative ℤ))
    (F : ConnectedClosedOrientedManifold.{u} 3) (p : F.Carrier)
    (hstd : isStandardFactor F) (hsub : Subsingleton (FundamentalGroup F.Carrier p)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F.toClosedOrientedManifold standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  rcases hstd with ⟨G, ⟨e⟩⟩ | ⟨f, _hf⟩
  · have hsubG : Subsingleton ↥G.group := by
      let eiso := fundamentalGroupMulEquivOfHomotopyEquiv e.1.toHomeomorph.toHomotopyEquiv
        p (e.1 p) rfl
      let qiso := (hquot G (e.1 p)).some
      have h₁ : Subsingleton (FundamentalGroup G.manifold.Carrier (e.1 p)) :=
        @Equiv.subsingleton.symm _ _ eiso.toEquiv hsub
      exact @Equiv.subsingleton.symm _ _ qiso.toEquiv h₁
    obtain ⟨g⟩ := htrivial G hsubG
    exact ⟨e.trans g⟩
  · exfalso
    let eiso := fundamentalGroupMulEquivOfHomotopyEquiv f.toHomeomorph.toHomotopyEquiv
      p (f p) rfl
    let ziso := (hproduct (f p)).some
    have hprod : Subsingleton (FundamentalGroup SphereTwoTimesCircle (f p)) :=
      @Equiv.subsingleton.symm _ _ eiso.toEquiv hsub
    exact not_subsingleton_multiplicative_int
      (@Equiv.subsingleton.symm _ _ ziso.toEquiv hprod)

theorem poincareStandardSumClosed_of_connectedSum_laws
    (happend : ∀ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
      Nonempty ((finiteConnectedSum (L ++ K)).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold.Carrier))
    (hcongr : ∀ {L K : List (ConnectedClosedOrientedManifold.{u} 3)},
      List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (A.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          B.toClosedOrientedManifold.Carrier)) L K →
      Nonempty ((finiteConnectedSum L).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (finiteConnectedSum K).toClosedOrientedManifold.Carrier)) :
    poincareStandardSumClosed.{u} := by
  intro L hL
  induction L with
  | nil =>
    rw [finiteConnectedSum_nil]
    exact isPoincareStandard_sphere.{u}
  | cons M L ih =>
    cases L with
    | nil => exact hL M (by simp)
    | cons N L =>
      have hM : isPoincareStandard M.Carrier := hL M (by simp)
      have hT : isPoincareStandard (finiteConnectedSum (N :: L)).Carrier :=
        ih fun F hF => hL F (by simp [hF])
      obtain ⟨PM⟩ := hM
      obtain ⟨PT⟩ := hT
      have hforall : List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
          Nonempty (A.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            B.toClosedOrientedManifold.Carrier))
          [M, finiteConnectedSum (N :: L)]
          [finiteConnectedSum PM.factors, finiteConnectedSum PT.factors] :=
        List.Forall₂.cons ⟨PM.diffeomorph⟩ (List.Forall₂.cons ⟨PT.diffeomorph⟩ List.Forall₂.nil)
      obtain ⟨c⟩ := hcongr hforall
      obtain ⟨ap⟩ := happend PM.factors PT.factors
      refine isPoincareStandard_of_diffeomorph (c.trans ap.symm) ?_
      exact isPoincareStandard_finite_sum (PM.factors ++ PT.factors) fun F hF =>
        (List.mem_append.mp hF).elim (fun h => PM.standard F h) (fun h => PT.standard F h)

theorem exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
    (hpi : ∀ (L : List (ConnectedClosedOrientedManifold.{u} 3))
      (x : (i : Fin L.length) → (L.get i).Carrier)
      (y : (finiteConnectedSum L).Carrier),
      Nonempty (FundamentalGroup (finiteConnectedSum L).Carrier y ≃*
        Monoid.CoprodI (fun i : Fin L.length =>
          FundamentalGroup (L.get i).Carrier (x i))))
    (hquot : ∀ (G : SphericalSpaceFormGroup) (p : G.manifold.Carrier),
      Nonempty (FundamentalGroup G.manifold.Carrier p ≃* G.group))
    (htrivial : ∀ (G : SphericalSpaceFormGroup), Subsingleton G.group →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        G.manifold.toClosedOrientedManifold
        standardThreeSphereLift.{u}.toClosedOrientedManifold))
    (hproduct : ∀ p : SphereTwoTimesCircle,
      Nonempty (FundamentalGroup SphereTwoTimesCircle p ≃* Multiplicative ℤ))
    (hunit : ∀ M : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum M standardThreeSphereLift.{u}).toClosedOrientedManifold
        M.toClosedOrientedManifold))
    (hcongr : ∀ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
      List.Forall₂ (fun (M N : ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold
        (finiteConnectedSum K).toClosedOrientedManifold))
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M] (h : isPoincareStandard M) :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) := by
  classical
  obtain ⟨P⟩ := h
  let x : (i : Fin P.factors.length) → (P.factors.get i).Carrier :=
    fun i => Classical.choice (inferInstance : Nonempty (P.factors.get i).Carrier)
  let y : (finiteConnectedSum P.factors).Carrier := Classical.choice inferInstance
  have hbase : Subsingleton (FundamentalGroup (finiteConnectedSum P.factors).Carrier y) := by
    have he : FundamentalGroup (finiteConnectedSum P.factors).Carrier y ≃*
        FundamentalGroup M (P.diffeomorph.symm y) :=
      fundamentalGroupMulEquivOfHomotopyEquiv P.diffeomorph.symm.toHomeomorph.toHomotopyEquiv
        y (P.diffeomorph.symm y) rfl
    exact he.subsingleton
  have hcoprod : Subsingleton (Monoid.CoprodI (fun i : Fin P.factors.length =>
      FundamentalGroup (P.factors.get i).Carrier (x i))) :=
    @Equiv.subsingleton _ _ ((hpi P.factors x y).some.symm : _ ≃ _) hbase
  have hsub : ∀ i : Fin P.factors.length,
      Subsingleton (FundamentalGroup (P.factors.get i).Carrier (x i)) :=
    (DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff _).mp hcoprod
  have hL : ∀ F ∈ P.factors, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F.toClosedOrientedManifold standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
    intro F hF
    obtain ⟨i, rfl⟩ := List.get_of_mem hF
    exact exists_orientedDiffeomorph_standardThreeSphere_of_isStandardFactor
      hquot htrivial hproduct (P.factors.get i) (x i) (P.standard _ hF) (hsub i)
  obtain ⟨s⟩ := exists_orientedDiffeomorph_finiteConnectedSum_standardThreeSphere
    hunit hcongr P.factors hL
  exact ⟨P.diffeomorph.trans s.1⟩

private theorem diffeomorph_symm_nonempty {M N : ClosedOrientedManifold.{u} 3}
    (h : Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier)) :
    Nonempty (N.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier) :=
  h.elim fun f => ⟨f.symm⟩

private theorem diffeomorph_trans_nonempty {M N P : ClosedOrientedManifold.{u} 3}
    (h₁ : Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier))
    (h₂ : Nonempty (N.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P.Carrier)) :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P.Carrier) :=
  h₁.elim fun f => h₂.elim fun g => ⟨f.trans g⟩

private theorem finiteConnectedSum_append_of_unit_assoc_transport_diffeo
    (hunitR : ∀ X : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hunitL : ∀ X : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((connectedSum standardThreeSphereLift.{u} X).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hassoc : ∀ X Y Z : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((connectedSum (connectedSum X Y) Z).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (connectedSum X (connectedSum Y Z)).toClosedOrientedManifold.Carrier))
    (htransportR : ∀ X Y Y' : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (Y.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        Y'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (connectedSum X Y').toClosedOrientedManifold.Carrier))
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty ((finiteConnectedSum (L ++ K)).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum (finiteConnectedSum L)
        (finiteConnectedSum K)).toClosedOrientedManifold.Carrier) := by
  induction L generalizing K with
  | nil =>
      rw [List.nil_append, finiteConnectedSum_nil]
      exact diffeomorph_symm_nonempty (hunitL (finiteConnectedSum K))
  | cons M L ih =>
      cases L with
      | nil =>
          cases K with
          | nil =>
              simp only [finiteConnectedSum_nil, finiteConnectedSum_singleton]
              exact diffeomorph_symm_nonempty (hunitR M)
          | cons N K =>
              simp only [List.cons_append, List.nil_append, finiteConnectedSum_singleton,
                finiteConnectedSum_cons_cons]
              exact ⟨(ClosedOrientedManifold.OrientedDiffeomorph.refl
                (connectedSum M (finiteConnectedSum (N :: K))).toClosedOrientedManifold).1⟩
      | cons N L =>
          simp only [List.cons_append, finiteConnectedSum_cons_cons]
          exact diffeomorph_trans_nonempty
            (htransportR M (finiteConnectedSum ((N :: L) ++ K))
              (connectedSum (finiteConnectedSum (N :: L)) (finiteConnectedSum K)) (ih K))
            (diffeomorph_symm_nonempty
              (hassoc M (finiteConnectedSum (N :: L)) (finiteConnectedSum K)))

private theorem finiteConnectedSum_congr_of_transport_diffeo
    (htransportL : ∀ X X' Y : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (X.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        X'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (connectedSum X' Y).toClosedOrientedManifold.Carrier))
    (htransportR : ∀ X Y Y' : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (Y.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        Y'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (connectedSum X Y').toClosedOrientedManifold.Carrier))
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hf : List.Forall₂ (fun (M N : ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (M.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        N.toClosedOrientedManifold.Carrier)) L K) :
    Nonempty ((finiteConnectedSum L).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (finiteConnectedSum K).toClosedOrientedManifold.Carrier) := by
  refine List.Forall₂.rec (motive := fun L K _ =>
    Nonempty ((finiteConnectedSum L).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (finiteConnectedSum K).toClosedOrientedManifold.Carrier)) ?_ ?_ hf
  · exact ⟨(ClosedOrientedManifold.OrientedDiffeomorph.refl
      (finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold.{u} 3))).toClosedOrientedManifold).1⟩
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
            exact diffeomorph_trans_nonempty
              (htransportL M N (finiteConnectedSum (M2 :: L'')) hM)
              (htransportR N (finiteConnectedSum (M2 :: L''))
                (finiteConnectedSum (N2 :: K'')) ih)

theorem poincareStandardSumClosed_of_unit_assoc_transport
    (hunitR : ∀ X : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hunitL : ∀ X : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((connectedSum standardThreeSphereLift.{u} X).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hassoc : ∀ X Y Z : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((connectedSum (connectedSum X Y) Z).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (connectedSum X (connectedSum Y Z)).toClosedOrientedManifold.Carrier))
    (htransportL : ∀ X X' Y : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (X.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        X'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (connectedSum X' Y).toClosedOrientedManifold.Carrier))
    (htransportR : ∀ X Y Y' : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (Y.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        Y'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (connectedSum X Y').toClosedOrientedManifold.Carrier)) :
    poincareStandardSumClosed.{u} := by
  refine poincareStandardSumClosed_of_connectedSum_laws ?_ ?_
  · exact fun L K =>
      finiteConnectedSum_append_of_unit_assoc_transport_diffeo hunitR hunitL hassoc htransportR L K
  · exact fun hf => finiteConnectedSum_congr_of_transport_diffeo htransportL htransportR hf

end DifferentialGeometry.Topology
