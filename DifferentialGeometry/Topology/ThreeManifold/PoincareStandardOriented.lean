import DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeInvarianceObstruction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.LeftUnitLaw
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormTrivial
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

structure OrientedPoincareStandardPresentation (M : ClosedOrientedManifold.{u} 3) where
  factors : List (ConnectedClosedOrientedManifold.{u} 3)
  standard : ∀ F ∈ factors, isStandardFactor F
  diffeomorph : ClosedOrientedManifold.OrientedDiffeomorph M
    (finiteConnectedSum factors).toClosedOrientedManifold

def isOrientedPoincareStandard (M : ClosedOrientedManifold.{u} 3) : Prop :=
  Nonempty (OrientedPoincareStandardPresentation M)

theorem isPoincareStandard_of_isOrientedPoincareStandard {M : ClosedOrientedManifold.{u} 3}
    (h : isOrientedPoincareStandard M) : isPoincareStandard M.Carrier :=
  h.elim fun p => ⟨⟨p.factors, p.standard, p.diffeomorph.1⟩⟩

theorem isOrientedPoincareStandard_finite_sum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, isStandardFactor F) :
    isOrientedPoincareStandard (finiteConnectedSum L).toClosedOrientedManifold :=
  ⟨⟨L, hL, ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩

theorem isOrientedPoincareStandard_of_orientedDiffeomorph
    {M N : ClosedOrientedManifold.{u} 3}
    (f : ClosedOrientedManifold.OrientedDiffeomorph M N) (hN : isOrientedPoincareStandard N) :
    isOrientedPoincareStandard M :=
  hN.elim fun p => ⟨⟨p.factors, p.standard, f.trans p.diffeomorph⟩⟩

theorem isOrientedPoincareStandard_sphere :
    isOrientedPoincareStandard standardThreeSphereLift.{u}.toClosedOrientedManifold :=
  isOrientedPoincareStandard_finite_sum [] (by simp)

theorem isOrientedPoincareStandard_of_standard_factor
    (M : ConnectedClosedOrientedManifold.{u} 3) (h : isStandardFactor M) :
    isOrientedPoincareStandard M.toClosedOrientedManifold :=
  isOrientedPoincareStandard_finite_sum [M] (by simpa using h)

private theorem nonemptyDiffeomorph_trans {M N P : ClosedOrientedManifold.{u} 3}
    (h₁ : Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier))
    (h₂ : Nonempty (N.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P.Carrier)) :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P.Carrier) :=
  h₁.elim fun f => h₂.elim fun g => ⟨f.trans g⟩

private theorem not_subsingleton_multiplicative_int :
    ¬ Subsingleton (Multiplicative ℤ) := fun h =>
  Int.zero_ne_one (Multiplicative.ofAdd.injective (h.elim _ _))

theorem exists_orientedDiffeomorph_standardThreeSphere_of_isStandardFactor
    (F : ConnectedClosedOrientedManifold.{u} 3) (p : F.Carrier)
    (hstd : isStandardFactor F) (hsub : Subsingleton (FundamentalGroup F.Carrier p)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph F.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  rcases hstd with ⟨G, ⟨e⟩⟩ | ⟨f, _hf⟩
  · have hsubG : Subsingleton ↥G.group := by
      let eiso := fundamentalGroupMulEquivOfHomotopyEquiv e.1.toHomeomorph.toHomotopyEquiv
        p (e.1 p) rfl
      let qiso := (G.nonempty_fundamentalGroupManifoldEquiv (e.1 p)).some
      have h₁ : Subsingleton (FundamentalGroup G.manifold.Carrier (e.1 p)) :=
        @Equiv.subsingleton.symm _ _ eiso.toEquiv hsub
      exact @Equiv.subsingleton.symm _ _ qiso.toEquiv h₁
    obtain ⟨g⟩ := exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group G hsubG
    exact ⟨e.trans g⟩
  · exfalso
    let eiso := fundamentalGroupMulEquivOfHomotopyEquiv f.toHomeomorph.toHomotopyEquiv
      p (f p) rfl
    let ziso := (exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle (f p)).some
    have hprod : Subsingleton (FundamentalGroup SphereTwoTimesCircle (f p)) :=
      @Equiv.subsingleton.symm _ _ eiso.toEquiv hsub
    exact not_subsingleton_multiplicative_int
      (@Equiv.subsingleton.symm _ _ ziso.toEquiv hprod)

theorem exists_diffeomorph_finiteConnectedSum_standardThreeSphere
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F.toClosedOrientedManifold standardThreeSphereLift.{u}.toClosedOrientedManifold)) :
    Nonempty ((finiteConnectedSum L).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.toClosedOrientedManifold.Carrier) := by
  induction L with
  | nil =>
      exact ⟨Diffeomorph.refl (𝓡 3)
        standardThreeSphereLift.{u}.toClosedOrientedManifold.Carrier ∞⟩
  | cons M L ih =>
      cases L with
      | nil =>
          obtain ⟨f⟩ := hL M (by simp)
          exact ⟨f.1⟩
      | cons N L =>
          have ih' : Nonempty ((finiteConnectedSum (N :: L)).toClosedOrientedManifold.Carrier
              ≃ₘ⟮𝓡 3, 𝓡 3⟯
              standardThreeSphereLift.{u}.toClosedOrientedManifold.Carrier) :=
            ih fun F hF => hL F (by simp [hF])
          have htail : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
              (finiteConnectedSum (N :: L)).toClosedOrientedManifold
              standardThreeSphereLift.{u}.toClosedOrientedManifold) :=
            nonempty_orientedDiffeomorph_standardThreeSphere_of_diffeomorph
              (finiteConnectedSum (N :: L)) ih'
          have hstep : Nonempty
              ((connectedSum M (finiteConnectedSum (N :: L))).toClosedOrientedManifold.Carrier
                ≃ₘ⟮𝓡 3, 𝓡 3⟯
                (connectedSum standardThreeSphereLift.{u} standardThreeSphereLift.{u}
                  ).toClosedOrientedManifold.Carrier) :=
            connectedSum_unorientedTransport_holds M standardThreeSphereLift.{u}
              (finiteConnectedSum (N :: L)) standardThreeSphereLift.{u}
              (hL M (by simp)) htail
          obtain ⟨u⟩ := nonempty_diffeomorph_connectedSum_sphere_right_unit
            standardThreeSphereLift.{u}
          simp only [finiteConnectedSum_cons_cons]
          exact nonemptyDiffeomorph_trans hstep ⟨u⟩

theorem exists_diffeomorph_standardThreeSphere_of_isOrientedPoincareStandard
    {M : ClosedOrientedManifold.{u} 3} [ConnectedSpace M.Carrier]
    [SimplyConnectedSpace M.Carrier] (h : isOrientedPoincareStandard M) :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      standardThreeSphereLift.{u}.toClosedOrientedManifold.Carrier) := by
  classical
  obtain ⟨P⟩ := h
  let x : (i : Fin P.factors.length) → (P.factors.get i).Carrier :=
    fun i => Classical.choice (inferInstance : Nonempty (P.factors.get i).Carrier)
  let y : (finiteConnectedSum P.factors).Carrier := Classical.choice inferInstance
  have hbase : Subsingleton (FundamentalGroup (finiteConnectedSum P.factors).Carrier y) := by
    have he : FundamentalGroup (finiteConnectedSum P.factors).Carrier y ≃*
        FundamentalGroup M.Carrier (P.diffeomorph.1.symm y) :=
      fundamentalGroupMulEquivOfHomotopyEquiv P.diffeomorph.1.symm.toHomeomorph.toHomotopyEquiv
        y (P.diffeomorph.1.symm y) rfl
    exact he.subsingleton
  have hcoprod : Subsingleton (Monoid.CoprodI (fun i : Fin P.factors.length =>
      FundamentalGroup (P.factors.get i).Carrier (x i))) :=
    @Equiv.subsingleton _ _
      ((fundamentalGroup_finiteConnectedSum_freeProduct P.factors x y).some.symm : _ ≃ _) hbase
  have hsub : ∀ i : Fin P.factors.length,
      Subsingleton (FundamentalGroup (P.factors.get i).Carrier (x i)) :=
    (DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff _).mp hcoprod
  have hL : ∀ F ∈ P.factors, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F.toClosedOrientedManifold standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
    intro F hF
    obtain ⟨i, rfl⟩ := List.get_of_mem hF
    exact exists_orientedDiffeomorph_standardThreeSphere_of_isStandardFactor
      (P.factors.get i) (x i) (P.standard _ hF) (hsub i)
  obtain ⟨s⟩ := exists_diffeomorph_finiteConnectedSum_standardThreeSphere P.factors hL
  exact ⟨P.diffeomorph.1.trans s⟩



def isOrientedPoincareStandardSumClosed : Prop :=
  ∀ L : List (ConnectedClosedOrientedManifold.{u} 3),
    (∀ F ∈ L, isOrientedPoincareStandard F.toClosedOrientedManifold) →
      isOrientedPoincareStandard (finiteConnectedSum L).toClosedOrientedManifold

theorem isOrientedPoincareStandardSumClosed_of_connectedSumLaws
    (h : connectedSumLaws.{u}) : isOrientedPoincareStandardSumClosed.{u} := by
  intro L
  induction L with
  | nil => intro _; exact isOrientedPoincareStandard_sphere
  | cons M L ih =>
      intro hL
      cases L with
      | nil => exact hL M (by simp)
      | cons N L =>
          have hM : isOrientedPoincareStandard M.toClosedOrientedManifold := hL M (by simp)
          have hT : isOrientedPoincareStandard
              (finiteConnectedSum (N :: L)).toClosedOrientedManifold :=
            ih fun F hF => hL F (by simp [hF])
          obtain ⟨PM⟩ := hM
          obtain ⟨PT⟩ := hT
          have hforall : List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
              Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
                A.toClosedOrientedManifold B.toClosedOrientedManifold))
              [M, finiteConnectedSum (N :: L)]
              [finiteConnectedSum PM.factors, finiteConnectedSum PT.factors] :=
            List.Forall₂.cons ⟨PM.diffeomorph⟩ (List.Forall₂.cons ⟨PT.diffeomorph⟩ List.Forall₂.nil)
          obtain ⟨c⟩ := finiteConnectedSum_congr_of_connectedSumLaws h hforall
          obtain ⟨ap⟩ := finiteConnectedSum_append_of_connectedSumLaws h PM.factors PT.factors
          exact isOrientedPoincareStandard_of_orientedDiffeomorph (c.trans ap.symm)
            (isOrientedPoincareStandard_finite_sum (PM.factors ++ PT.factors) fun F hF =>
              (List.mem_append.mp hF).elim (fun hh => PM.standard F hh)
                (fun hh => PT.standard F hh))

theorem isOrientedPoincareStandard_of_isPoincareStandard_of_simplyConnected
    (F : ConnectedClosedOrientedManifold.{u} 3) [SimplyConnectedSpace F.Carrier]
    (h : isPoincareStandard F.Carrier) :
    isOrientedPoincareStandard F.toClosedOrientedManifold := by
  classical
  obtain ⟨P⟩ := h
  let x : (i : Fin P.factors.length) → (P.factors.get i).Carrier :=
    fun i => Classical.choice (inferInstance : Nonempty (P.factors.get i).Carrier)
  let y : (finiteConnectedSum P.factors).Carrier := Classical.choice inferInstance
  have hbase : Subsingleton (FundamentalGroup (finiteConnectedSum P.factors).Carrier y) := by
    have he : FundamentalGroup (finiteConnectedSum P.factors).Carrier y ≃*
        FundamentalGroup F.Carrier (P.diffeomorph.symm y) :=
      fundamentalGroupMulEquivOfHomotopyEquiv P.diffeomorph.symm.toHomeomorph.toHomotopyEquiv
        y (P.diffeomorph.symm y) rfl
    exact he.subsingleton
  have hcoprod : Subsingleton (Monoid.CoprodI (fun i : Fin P.factors.length =>
      FundamentalGroup (P.factors.get i).Carrier (x i))) :=
    @Equiv.subsingleton _ _
      ((fundamentalGroup_finiteConnectedSum_freeProduct P.factors x y).some.symm : _ ≃ _) hbase
  have hsub : ∀ i : Fin P.factors.length,
      Subsingleton (FundamentalGroup (P.factors.get i).Carrier (x i)) :=
    (DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff _).mp hcoprod
  have hL : ∀ F ∈ P.factors, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F.toClosedOrientedManifold standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
    intro F hF
    obtain ⟨i, rfl⟩ := List.get_of_mem hF
    exact exists_orientedDiffeomorph_standardThreeSphere_of_isStandardFactor
      (P.factors.get i) (x i) (P.standard _ hF) (hsub i)
  obtain ⟨s⟩ := exists_diffeomorph_finiteConnectedSum_standardThreeSphere P.factors hL
  obtain ⟨g⟩ := nonempty_orientedDiffeomorph_standardThreeSphere_of_diffeomorph F
    ⟨P.diffeomorph.trans s⟩
  exact isOrientedPoincareStandard_of_orientedDiffeomorph g isOrientedPoincareStandard_sphere

theorem poincareStandardSumClosed_of_isOrientedPoincareStandardSumClosed
    (h : isOrientedPoincareStandardSumClosed.{u})
    (hup : ∀ F : ConnectedClosedOrientedManifold.{u} 3,
      isPoincareStandard F.Carrier → isOrientedPoincareStandard F.toClosedOrientedManifold) :
    poincareStandardSumClosed.{u} :=
  fun L hL => isPoincareStandard_of_isOrientedPoincareStandard
    (h L fun F hF => hup F (hL F hF))

end DifferentialGeometry.Topology
