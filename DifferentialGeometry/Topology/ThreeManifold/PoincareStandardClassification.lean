import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
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
  · obtain ⟨g⟩ := htrivial G (by
      have := hsub
      have he : Subsingleton (FundamentalGroup G.manifold.Carrier (e.1 p)) :=
        (fundamentalGroupMulEquivOfHomotopyEquiv e.1.toHomeomorph.toHomotopyEquiv
          p (e.1 p) rfl).symm.subsingleton
      have := he
      exact (hquot G (e.1 p)).some.symm.subsingleton)
    exact ⟨e.trans g⟩
  · exfalso
    have := hsub
    have hprod : Subsingleton (FundamentalGroup SphereTwoTimesCircle (f p)) :=
      (fundamentalGroupMulEquivOfHomotopyEquiv f.toHomeomorph.toHomotopyEquiv
        p (f p) rfl).symm.subsingleton
    have := hprod
    exact not_subsingleton_multiplicative_int ((hproduct (f p)).some.symm.subsingleton)

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

end DifferentialGeometry.Topology
