import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected
import DifferentialGeometry.Topology.Algebra.Group.FreeProductAssociativity

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

universe u

namespace DifferentialGeometry.Algebra.Group

noncomputable def coprodIFinConsEquivCoprod {n : ℕ} (G : Fin (n + 1) → Type u)
    [∀ i, Group (G i)] :
    Monoid.CoprodI G ≃*
      Monoid.Coprod (G 0) (Monoid.CoprodI (fun i : Fin n => G i.succ)) :=
  MonoidHom.toMulEquiv
    (Monoid.CoprodI.lift fun i => Fin.cases Monoid.Coprod.inl
      (fun j => Monoid.Coprod.inr.comp
        (Monoid.CoprodI.of (M := fun i : Fin n => G i.succ) (i := j))) i)
    (Monoid.Coprod.lift (Monoid.CoprodI.of (M := G) (i := 0))
      (Monoid.CoprodI.lift fun j => Monoid.CoprodI.of (M := G) (i := j.succ)))
    (by
      apply Monoid.CoprodI.ext_hom
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · ext g
        simp [Monoid.CoprodI.lift_of]
      · ext g
        simp [Monoid.CoprodI.lift_of])
    (by
      apply Monoid.Coprod.hom_ext
      · ext g
        simp [Monoid.CoprodI.lift_of]
      · apply Monoid.CoprodI.ext_hom
        intro j
        ext g
        simp [Monoid.CoprodI.lift_of])

noncomputable def coprodIFinOneEquiv {H : Fin 1 → Type u} [∀ i, Group (H i)] :
    Monoid.CoprodI H ≃* H 0 :=
  MonoidHom.toMulEquiv
    (Monoid.CoprodI.lift fun i =>
      (MulEquiv.cast (Subsingleton.elim i (0 : Fin 1))).toMonoidHom)
    (Monoid.CoprodI.of (M := H) (i := 0))
    (by
      apply Monoid.CoprodI.ext_hom
      intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst hi
      ext g
      simp [Monoid.CoprodI.lift_of])
    (by
      ext g
      simp)

end DifferentialGeometry.Algebra.Group

namespace DifferentialGeometry.Topology

instance instLocallyPathConnectedSpaceCarrier (M : ConnectedClosedOrientedManifold.{u} 3) :
    LocallyPathConnectedSpace M.Carrier :=
  Manifold.locallyPathConnectedSpace_of_modelWithCorners (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))

instance instPathConnectedSpaceCarrier (M : ConnectedClosedOrientedManifold.{u} 3) :
    PathConnectedSpace M.Carrier :=
  PathConnectedSpace.of_locallyPathConnectedSpace

noncomputable def chosenPoint (M : ConnectedClosedOrientedManifold.{u} 3) : M.Carrier :=
  Classical.choice (inferInstance : Nonempty M.Carrier)

def connectedSumBasedFreeProduct (M N : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  Nonempty (FundamentalGroup (connectedSum M N).Carrier (chosenPoint (connectedSum M N)) ≃*
    Monoid.Coprod (FundamentalGroup M.Carrier (chosenPoint M))
      (FundamentalGroup N.Carrier (chosenPoint N)))

def FiniteConnectedSumStatement (L : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  ∀ (x : (i : Fin L.length) → (L.get i).Carrier)
    (y : (finiteConnectedSum L).Carrier),
    Nonempty (FundamentalGroup (finiteConnectedSum L).Carrier y ≃*
      Monoid.CoprodI (fun i : Fin L.length =>
        FundamentalGroup (L.get i).Carrier (x i)))

def FiniteConnectedSumFreeProduct : Prop :=
  ∀ L : List (ConnectedClosedOrientedManifold.{u} 3), FiniteConnectedSumStatement L

theorem finiteConnectedSumStatement_nil :
    FiniteConnectedSumStatement ([] : List (ConnectedClosedOrientedManifold.{u} 3)) := by
  intro x y
  refine ⟨?_⟩
  letI : SimplyConnectedSpace
      (finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold.{u} 3))).Carrier :=
    (Homeomorph.ulift (X := SphereThree)).toHomotopyEquiv.simplyConnectedSpace
  letI : PathConnectedSpace
      (finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold.{u} 3))).Carrier :=
    instPathConnectedSpaceCarrier
      (finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold.{u} 3)))
  letI : Subsingleton
      (FundamentalGroup
        (finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold.{u} 3))).Carrier y) :=
    inferInstance
  letI : Unique
      (FundamentalGroup
        (finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold.{u} 3))).Carrier y) :=
    { default := 1, uniq := fun a => Subsingleton.elim a 1 }
  letI : Subsingleton
      (Monoid.CoprodI (fun i : Fin ([] : List (ConnectedClosedOrientedManifold.{u} 3)).length =>
        FundamentalGroup (([] : List (ConnectedClosedOrientedManifold.{u} 3)).get i).Carrier (x i))) :=
    (DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff _).mpr
      (fun i => Fin.elim0 i)
  letI : Unique
      (Monoid.CoprodI (fun i : Fin ([] : List (ConnectedClosedOrientedManifold.{u} 3)).length =>
        FundamentalGroup (([] : List (ConnectedClosedOrientedManifold.{u} 3)).get i).Carrier (x i))) :=
    { default := 1, uniq := fun a => Subsingleton.elim a 1 }
  exact MulEquiv.ofUnique

theorem finiteConnectedSumStatement_singleton (M : ConnectedClosedOrientedManifold.{u} 3) :
    FiniteConnectedSumStatement [M] := by
  intro x y
  refine ⟨?_⟩
  exact (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y (x 0)).trans
    (DifferentialGeometry.Algebra.Group.coprodIFinOneEquiv
      (H := fun i : Fin 1 =>
        FundamentalGroup (((M :: []) : List (ConnectedClosedOrientedManifold.{u} 3)).get i).Carrier
          (x i))).symm

theorem finiteConnectedSumFreeProduct_of_connectedSumBased
    (h : ∀ M N : ConnectedClosedOrientedManifold.{u} 3, connectedSumBasedFreeProduct M N) :
    FiniteConnectedSumFreeProduct.{u} := by
  intro L
  induction L with
  | nil =>
      exact finiteConnectedSumStatement_nil
  | cons M R ih =>
      cases R with
      | nil =>
          exact finiteConnectedSumStatement_singleton M
      | cons N R' =>
          intro x y
          refine ⟨?_⟩
          let q : (finiteConnectedSum (N :: R')).Carrier :=
            Classical.choice (inferInstance : Nonempty (finiteConnectedSum (N :: R')).Carrier)
          let xtail : (i : Fin (N :: R').length) → ((N :: R').get i).Carrier :=
            fun i => x i.succ
          have hbase := (h M (finiteConnectedSum (N :: R'))).some
          have hM := (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y
              (chosenPoint (connectedSum M (finiteConnectedSum (N :: R'))))).trans
            (hbase.trans
              ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
                  (chosenPoint M) (x 0)).coprodCongr
                (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
                  (chosenPoint (finiteConnectedSum (N :: R'))) q)))
          have htail := (ih xtail q).some
          exact hM.trans
            (((MulEquiv.refl (FundamentalGroup M.Carrier (x 0))).coprodCongr htail).trans
              (DifferentialGeometry.Algebra.Group.coprodIFinConsEquivCoprod
                (G := fun i : Fin (M :: N :: R').length =>
                  FundamentalGroup ((M :: N :: R').get i).Carrier (x i))).symm)

theorem finiteConnectedSumFreeProduct_of_connectedSum
    (h : ∀ (M N : ConnectedClosedOrientedManifold.{u} 3) (p : M.Carrier) (q : N.Carrier)
      (z : (connectedSum M N).Carrier),
      Nonempty (FundamentalGroup (connectedSum M N).Carrier z ≃*
        Monoid.Coprod (FundamentalGroup M.Carrier p) (FundamentalGroup N.Carrier q))) :
    FiniteConnectedSumFreeProduct.{u} :=
  finiteConnectedSumFreeProduct_of_connectedSumBased fun M N => h M N _ _ _

theorem finiteConnectedSum_freeProduct_of_connectedSumBased
    (h : ∀ M N : ConnectedClosedOrientedManifold.{u} 3, connectedSumBasedFreeProduct M N) :
    ∀ (L : List (ConnectedClosedOrientedManifold.{u} 3))
      (x : (i : Fin L.length) → (L.get i).Carrier)
      (y : (finiteConnectedSum L).Carrier),
      Nonempty (FundamentalGroup (finiteConnectedSum L).Carrier y ≃*
        Monoid.CoprodI (fun i : Fin L.length =>
          FundamentalGroup (L.get i).Carrier (x i))) :=
  finiteConnectedSumFreeProduct_of_connectedSumBased h

end DifferentialGeometry.Topology
