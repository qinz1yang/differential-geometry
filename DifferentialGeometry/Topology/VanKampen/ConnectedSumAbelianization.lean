import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Coprod.Basic
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift

set_option autoImplicit false

noncomputable section

universe u v

namespace DifferentialGeometry.Algebra.Group

private def coprodLiftInl (G : Type u) (H : Type v) [Group G] [Group H] :
    Abelianization G →* Abelianization (Monoid.Coprod G H) :=
  Abelianization.lift
    ((Abelianization.of (G := Monoid.Coprod G H)).comp
      (Monoid.Coprod.inl : G →* Monoid.Coprod G H))

private def coprodLiftInr (G : Type u) (H : Type v) [Group G] [Group H] :
    Abelianization H →* Abelianization (Monoid.Coprod G H) :=
  Abelianization.lift
    ((Abelianization.of (G := Monoid.Coprod G H)).comp
      (Monoid.Coprod.inr : H →* Monoid.Coprod G H))

private def coprodToAbelianizationProd (G : Type u) (H : Type v) [Group G] [Group H] :
    Monoid.Coprod G H →* Abelianization G × Abelianization H :=
  Monoid.Coprod.lift
    ((MonoidHom.inl (Abelianization G) (Abelianization H)).comp (Abelianization.of (G := G)))
    ((MonoidHom.inr (Abelianization G) (Abelianization H)).comp (Abelianization.of (G := H)))

private def abelianizationProdToCoprod (G : Type u) (H : Type v) [Group G] [Group H] :
    Abelianization G × Abelianization H →* Abelianization (Monoid.Coprod G H) where
  toFun p := coprodLiftInl G H p.1 * coprodLiftInr G H p.2
  map_one' := by simp [coprodLiftInl, coprodLiftInr]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    ac_rfl

private theorem abelianizationProdToCoprod_fst (G : Type u) (H : Type v) [Group G] [Group H]
    (a : Abelianization G) :
    abelianizationProdToCoprod G H (a, 1) = coprodLiftInl G H a := by
  simp [abelianizationProdToCoprod, coprodLiftInr]

private theorem abelianizationProdToCoprod_snd (G : Type u) (H : Type v) [Group G] [Group H]
    (b : Abelianization H) :
    abelianizationProdToCoprod G H (1, b) = coprodLiftInr G H b := by
  simp [abelianizationProdToCoprod, coprodLiftInl]

private theorem coprodToAbelianizationProd_comp_coprodLiftInl
    (G : Type u) (H : Type v) [Group G] [Group H] :
    (Abelianization.lift (coprodToAbelianizationProd G H)).comp (coprodLiftInl G H) =
      MonoidHom.inl (Abelianization G) (Abelianization H) := by
  apply Abelianization.hom_ext
  apply MonoidHom.ext
  intro g
  change (Abelianization.lift (coprodToAbelianizationProd G H))
      (coprodLiftInl G H (Abelianization.of g)) =
    (MonoidHom.inl (Abelianization G) (Abelianization H)) (Abelianization.of g)
  rw [show coprodLiftInl G H (Abelianization.of g) =
      Abelianization.of (Monoid.Coprod.inl g) from rfl, Abelianization.lift_apply_of]
  rfl

private theorem coprodToAbelianizationProd_comp_coprodLiftInr
    (G : Type u) (H : Type v) [Group G] [Group H] :
    (Abelianization.lift (coprodToAbelianizationProd G H)).comp (coprodLiftInr G H) =
      MonoidHom.inr (Abelianization G) (Abelianization H) := by
  apply Abelianization.hom_ext
  apply MonoidHom.ext
  intro h
  change (Abelianization.lift (coprodToAbelianizationProd G H))
      (coprodLiftInr G H (Abelianization.of h)) =
    (MonoidHom.inr (Abelianization G) (Abelianization H)) (Abelianization.of h)
  rw [show coprodLiftInr G H (Abelianization.of h) =
      Abelianization.of (Monoid.Coprod.inr h) from rfl, Abelianization.lift_apply_of]
  rfl

private theorem abelianizationProdToCoprod_comp_coprodToAbelianizationProd
    (G : Type u) (H : Type v) [Group G] [Group H] :
    (abelianizationProdToCoprod G H).comp (Abelianization.lift (coprodToAbelianizationProd G H)) =
      MonoidHom.id (Abelianization (Monoid.Coprod G H)) := by
  apply Abelianization.hom_ext
  apply Monoid.Coprod.hom_ext
  · ext g
    simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of]
    simp [abelianizationProdToCoprod, coprodLiftInl, coprodLiftInr, coprodToAbelianizationProd]
  · ext h
    simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of]
    simp [abelianizationProdToCoprod, coprodLiftInl, coprodLiftInr, coprodToAbelianizationProd]

private theorem lift_coprodToAbelianizationProd_comp_abelianizationProdToCoprod
    (G : Type u) (H : Type v) [Group G] [Group H] :
    (Abelianization.lift (coprodToAbelianizationProd G H)).comp (abelianizationProdToCoprod G H) =
      MonoidHom.id (Abelianization G × Abelianization H) := by
  apply MonoidHom.ext
  intro p
  have h1 : (Abelianization.lift (coprodToAbelianizationProd G H))
      (abelianizationProdToCoprod G H (p.1, 1)) = (p.1, 1) := by
    rw [abelianizationProdToCoprod_fst]
    exact DFunLike.congr_fun (coprodToAbelianizationProd_comp_coprodLiftInl G H) p.1
  have h2 : (Abelianization.lift (coprodToAbelianizationProd G H))
      (abelianizationProdToCoprod G H (1, p.2)) = (1, p.2) := by
    rw [abelianizationProdToCoprod_snd]
    exact DFunLike.congr_fun (coprodToAbelianizationProd_comp_coprodLiftInr G H) p.2
  change ((Abelianization.lift (coprodToAbelianizationProd G H)).comp
    (abelianizationProdToCoprod G H)) p = p
  rw [show p = (p.1, 1) * (1, p.2) from by simp]
  simp only [MonoidHom.comp_apply, map_mul]
  rw [h1, h2]

noncomputable def abelianizationCoprodEquivProd (G : Type u) (H : Type v) [Group G]
    [Group H] : Abelianization (Monoid.Coprod G H) ≃* Abelianization G × Abelianization H :=
  MonoidHom.toMulEquiv
    (Abelianization.lift (coprodToAbelianizationProd G H))
    (abelianizationProdToCoprod G H)
    (abelianizationProdToCoprod_comp_coprodToAbelianizationProd G H)
    (lift_coprodToAbelianizationProd_comp_abelianizationProdToCoprod G H)

@[simp]
theorem abelianizationCoprodEquivProd_apply_inl (G : Type u) (H : Type v) [Group G] [Group H]
    (g : G) :
    abelianizationCoprodEquivProd G H (Abelianization.of (Monoid.Coprod.inl g)) =
      (Abelianization.of g, 1) := by
  simp [abelianizationCoprodEquivProd, coprodToAbelianizationProd]

@[simp]
theorem abelianizationCoprodEquivProd_apply_inr (G : Type u) (H : Type v) [Group G] [Group H]
    (h : H) :
    abelianizationCoprodEquivProd G H (Abelianization.of (Monoid.Coprod.inr h)) =
      (1, Abelianization.of h) := by
  simp [abelianizationCoprodEquivProd, coprodToAbelianizationProd]

theorem abelianizationMulEquivProdOfCoprod (G : Type u) (H : Type v) [Group G] [Group H]
    {K : Type*} [Group K] (e : K ≃* Monoid.Coprod G H) :
    Nonempty (Abelianization K ≃* Abelianization G × Abelianization H) :=
  ⟨(MulEquiv.abelianizationCongr e).trans (abelianizationCoprodEquivProd G H)⟩

end DifferentialGeometry.Algebra.Group

namespace DifferentialGeometry.Topology

theorem abelianization_fundamentalGroup_connectedSum
    (M N : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (Abelianization
        (FundamentalGroup (connectedSum M N).Carrier (chosenPoint (connectedSum M N))) ≃*
      Abelianization (FundamentalGroup M.Carrier (chosenPoint M)) ×
        Abelianization (FundamentalGroup N.Carrier (chosenPoint N))) :=
  DifferentialGeometry.Algebra.Group.abelianizationMulEquivProdOfCoprod
    (FundamentalGroup M.Carrier (chosenPoint M))
    (FundamentalGroup N.Carrier (chosenPoint N))
    (fundamentalGroup_connectedSum_freeProduct M N).some

theorem abelianization_fundamentalGroup_sphereTwoTimesCircleLift :
    Nonempty (Abelianization (FundamentalGroup sphereTwoTimesCircleLift.Carrier
        (chosenPoint sphereTwoTimesCircleLift)) ≃* Multiplicative ℤ) := by
  obtain ⟨e⟩ := exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle
    (chosenPoint sphereTwoTimesCircleLift).down
  exact ⟨(MulEquiv.abelianizationCongr
      (fundamentalGroupMulEquivOfHomotopyEquiv Homeomorph.ulift.toHomotopyEquiv
        (chosenPoint sphereTwoTimesCircleLift)
        (chosenPoint sphereTwoTimesCircleLift).down rfl)).trans
    ((MulEquiv.abelianizationCongr e).trans (Abelianization.equivOfComm).symm)⟩

theorem abelianization_fundamentalGroup_connectedSum_sphereTwoTimesCircleLift :
    Nonempty (Abelianization (FundamentalGroup
        (connectedSum sphereTwoTimesCircleLift sphereTwoTimesCircleLift).Carrier
        (chosenPoint (connectedSum sphereTwoTimesCircleLift
          sphereTwoTimesCircleLift))) ≃* Multiplicative ℤ × Multiplicative ℤ) := by
  obtain ⟨e⟩ := abelianization_fundamentalGroup_connectedSum
    sphereTwoTimesCircleLift sphereTwoTimesCircleLift
  obtain ⟨eS⟩ := abelianization_fundamentalGroup_sphereTwoTimesCircleLift
  exact ⟨e.trans (eS.prodCongr eS)⟩

end DifferentialGeometry.Topology
