import DifferentialGeometry.Topology.FundamentalGroup.Circle
import DifferentialGeometry.Topology.FundamentalGroup.Product
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSumSummandCountUnique
import DifferentialGeometry.Topology.ThreeManifold.CutCapSummandCountTopologicalAssembly
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormProjective
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.CoprodI
import Mathlib.RingTheory.TensorProduct.Finite

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace DifferentialGeometry.Topology

universe u v

theorem groupFG_of_subsingleton {G : Type u} [Group G] [Subsingleton G] : Group.FG G := by
  rw [Group.fg_def]
  have h : (⊤ : Subgroup G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x _
    exact Subsingleton.elim x 1
  rw [h]
  exact Subgroup.FG.bot

theorem groupFG_of_mulEquiv {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H)
    (h : Group.FG H) : Group.FG G := by
  have := h
  exact Group.fg_of_surjective (f := (e.symm : H →* G)) e.symm.surjective

theorem groupFG_multiplicative_int : Group.FG (Multiplicative ℤ) :=
  AddGroup.fg_iff_mul_fg.mp (Module.Finite.iff_addGroup_fg.mp (Module.Finite.self ℤ))

theorem groupFG_abelianization {G : Type u} [Group G] (h : Group.FG G) :
    Group.FG (Abelianization G) := by
  have := h
  exact Group.fg_of_surjective (f := (Abelianization.of : G →* Abelianization G))
    (fun b => QuotientGroup.induction_on b (fun a => ⟨a, rfl⟩))

theorem groupFG_prod {G H : Type u} [Group G] [Group H] (hG : Group.FG G) (hH : Group.FG H) :
    Group.FG (G × H) := by
  have h1 : ((MonoidHom.inl G H : G →* G × H).range).FG := by
    have := hG
    exact (Group.fg_iff_subgroup_fg _).mp
      (Group.fg_of_surjective (f := (MonoidHom.inl G H).rangeRestrict)
        (MonoidHom.inl G H).rangeRestrict_surjective)
  have h2 : ((MonoidHom.inr G H : H →* G × H).range).FG := by
    have := hH
    exact (Group.fg_iff_subgroup_fg _).mp
      (Group.fg_of_surjective (f := (MonoidHom.inr G H).rangeRestrict)
        (MonoidHom.inr G H).rangeRestrict_surjective)
  rw [Group.fg_def]
  have htop : (MonoidHom.inl G H : G →* G × H).range ⊔
      (MonoidHom.inr G H : H →* G × H).range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨g, h⟩ -
    have hg : (g, (1 : H)) ∈ (MonoidHom.inl G H : G →* G × H).range := ⟨g, rfl⟩
    have hh : ((1 : G), h) ∈ (MonoidHom.inr G H : H →* G × H).range := ⟨h, rfl⟩
    simpa using Subgroup.mul_mem_sup hg hh
  rw [← htop]
  exact h1.sup h2

theorem groupFG_coprodI {ι : Type v} [Finite ι] (G : ι → Type u) [∀ i, Group (G i)]
    (h : ∀ i, Group.FG (G i)) : Group.FG (Monoid.CoprodI G) := by
  have htop : (⨆ i, (Monoid.CoprodI.of : G i →* Monoid.CoprodI G).range) = ⊤ := by
    rw [← Monoid.CoprodI.range_eq_iSup G
        (fun i => (Monoid.CoprodI.of : G i →* Monoid.CoprodI G)),
      Monoid.CoprodI.lift_of']
    exact MonoidHom.range_eq_top.mpr Function.surjective_id
  rw [Group.fg_def, ← htop]
  refine Subgroup.FG.iSup _ fun i => ?_
  have hi : Group.FG (Monoid.CoprodI.of : G i →* Monoid.CoprodI G).range := by
    have := h i
    exact Group.fg_of_surjective
      (f := (Monoid.CoprodI.of : G i →* Monoid.CoprodI G).rangeRestrict)
      (Monoid.CoprodI.of : G i →* Monoid.CoprodI G).rangeRestrict_surjective
  exact (Group.fg_iff_subgroup_fg _).mp hi

theorem groupFG_of_groupFG_coprodI {ι : Type v} [Finite ι] (G : ι → Type u)
    [∀ i, Group (G i)] (i : ι) (h : Group.FG (Monoid.CoprodI G)) : Group.FG (G i) := by
  classical
  let φ : (j : ι) → G j →* G i := fun j =>
    if hji : j = i then (hji.symm ▸ MonoidHom.id (G i) : G j →* G i) else 1
  have hsurj : Function.Surjective (Monoid.CoprodI.lift φ) := by
    intro x
    refine ⟨Monoid.CoprodI.of x, ?_⟩
    rw [Monoid.CoprodI.lift_of]
    simp [φ]
  have := h
  exact Group.fg_of_surjective (f := Monoid.CoprodI.lift φ) hsurj

theorem moduleFinite_int_additive_abelianization_of_groupFG {G : Type u} [Group G]
    (h : Group.FG G) : Module.Finite ℤ (Additive (Abelianization G)) :=
  Module.Finite.iff_addGroup_fg.mpr (GroupFG.iff_add_fg.mp (groupFG_abelianization h))

theorem moduleFinite_rat_tensor_additive_abelianization_of_groupFG {G : Type u} [Group G]
    (h : Group.FG G) : Module.Finite ℚ (ℚ ⊗[ℤ] Additive (Abelianization G)) :=
  Module.Finite.base_change (R := ℤ) (A := ℚ) (M := Additive (Abelianization G))
    (h := moduleFinite_int_additive_abelianization_of_groupFG h)

theorem groupFG_fundamentalGroup_finiteConnectedSum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (x : (i : Fin L.length) → (L.get i).Carrier)
    (h : ∀ i, Group.FG (FundamentalGroup (L.get i).Carrier (x i)))
    (y : (finiteConnectedSum L).Carrier) :
    Group.FG (FundamentalGroup (finiteConnectedSum L).Carrier y) := by
  obtain ⟨e⟩ := fundamentalGroup_finiteConnectedSum_freeProduct L x y
  exact groupFG_of_mulEquiv e (groupFG_coprodI (fun i : Fin L.length =>
    FundamentalGroup (L.get i).Carrier (x i)) h)

theorem groupFG_fundamentalGroup_finiteConnectedSum_chosenPoint
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ i, Group.FG (FundamentalGroup (L.get i).Carrier (chosenPoint (L.get i))))
    (y : (finiteConnectedSum L).Carrier) :
    Group.FG (FundamentalGroup (finiteConnectedSum L).Carrier y) :=
  groupFG_fundamentalGroup_finiteConnectedSum L (fun i => chosenPoint (L.get i)) h y

theorem groupFG_fundamentalGroup_sphereTwo (x : SphereTwo) :
    Group.FG (FundamentalGroup SphereTwo x) :=
  groupFG_of_subsingleton

theorem groupFG_fundamentalGroup_sphereThree (x : SphereThree) :
    Group.FG (FundamentalGroup SphereThree x) :=
  groupFG_of_subsingleton

theorem groupFG_fundamentalGroup_circle (x : Circle) :
    Group.FG (FundamentalGroup Circle x) :=
  groupFG_of_mulEquiv
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (1 : Circle) x).symm.trans
      fundamentalGroupCircleEquivInt)
    groupFG_multiplicative_int

theorem groupFG_fundamentalGroup_circleTimesCircle (x : Circle × Circle) :
    Group.FG (FundamentalGroup (Circle × Circle) x) :=
  groupFG_of_mulEquiv (fundamentalGroupProdEquiv x.1 x.2)
    (groupFG_prod (groupFG_fundamentalGroup_circle x.1)
      (groupFG_fundamentalGroup_circle x.2))

theorem groupFG_fundamentalGroup_sphereTwoTimesCircle (x : SphereTwoTimesCircle) :
    Group.FG (FundamentalGroup SphereTwoTimesCircle x) :=
  groupFG_of_mulEquiv (exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle x).some
    groupFG_multiplicative_int

theorem groupFG_fundamentalGroup_standardThreeSphereLift
    (x : ULift.{u} SphereThree) :
    Group.FG (FundamentalGroup (ULift.{u} SphereThree) x) := by
  have hsc : SimplyConnectedSpace (ULift.{u} SphereThree) :=
    Homeomorph.ulift.toHomotopyEquiv.simplyConnectedSpace
  exact groupFG_of_subsingleton

theorem groupFG_fundamentalGroup_sphereTwoTimesCircleLift
    (x : sphereTwoTimesCircleLift.Carrier) :
    Group.FG (FundamentalGroup sphereTwoTimesCircleLift.Carrier x) :=
  groupFG_of_mulEquiv
    ((fundamentalGroupMulEquivOfHomotopyEquiv Homeomorph.ulift.toHomotopyEquiv x x.down rfl).trans
      (exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle x.down).some)
    groupFG_multiplicative_int

theorem groupFG_fundamentalGroup_sphericalSpaceFormQuotient (G : SphericalSpaceFormGroup)
    (p : G.manifold.Carrier) :
    Group.FG (FundamentalGroup G.manifold.Carrier p) :=
  groupFG_of_mulEquiv (G.fundamentalGroupManifoldEquiv p) inferInstance

def FinitelyGeneratedFundamentalGroup (M : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ p : M.Carrier, Group.FG (FundamentalGroup M.Carrier p)

def FinitelyGeneratedFundamentalGroupClosedThreeManifold : Prop :=
  ∀ M : ConnectedClosedOrientedManifold.{u} 3, FinitelyGeneratedFundamentalGroup M

theorem abelianizationModuleFinite_of_finitelyGeneratedFundamentalGroup
    (M : ConnectedClosedOrientedManifold.{u} 3) (h : FinitelyGeneratedFundamentalGroup M) :
    connectedClosedOrientedManifoldAbelianizationModuleFinite M :=
  moduleFinite_int_additive_abelianization_of_groupFG (h (chosenPoint M))

theorem abelianizationRationalFinite_of_finitelyGeneratedFundamentalGroup
    (M : ConnectedClosedOrientedManifold.{u} 3) (h : FinitelyGeneratedFundamentalGroup M) :
    connectedClosedOrientedManifoldAbelianizationRationalFinite M :=
  connectedClosedOrientedManifoldAbelianizationRationalFinite_of_moduleFinite M
    (abelianizationModuleFinite_of_finitelyGeneratedFundamentalGroup M h)

theorem finitelyGeneratedAbelianizationFundamentalGroupClosedThreeManifold_of_finitelyGenerated
    (h : FinitelyGeneratedFundamentalGroupClosedThreeManifold.{u}) :
    FinitelyGeneratedAbelianizationFundamentalGroupClosedThreeManifold.{u} :=
  fun M p => moduleFinite_int_additive_abelianization_of_groupFG (h M p)

theorem finiteConnectedSumSummandCountUnique_of_finitelyGeneratedFundamentalGroup
    (h : FinitelyGeneratedFundamentalGroupClosedThreeManifold.{u})
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    finiteConnectedSumSummandCountUnique L :=
  finiteConnectedSumSummandCountUnique_of_forall_factor_abelianizationRationalFinite L fun i =>
    abelianizationRationalFinite_of_finitelyGeneratedFundamentalGroup (L.get i) (h (L.get i))

theorem finitelyGeneratedFundamentalGroup_standardThreeSphereLift :
    FinitelyGeneratedFundamentalGroup standardThreeSphereLift.{u} :=
  fun x => groupFG_fundamentalGroup_standardThreeSphereLift x

theorem finitelyGeneratedFundamentalGroup_sphereTwoTimesCircleLift :
    FinitelyGeneratedFundamentalGroup sphereTwoTimesCircleLift :=
  fun x => groupFG_fundamentalGroup_sphereTwoTimesCircleLift x

theorem finitelyGeneratedFundamentalGroup_sphericalSpaceFormQuotient
    (G : SphericalSpaceFormGroup) :
    FinitelyGeneratedFundamentalGroup G.manifold :=
  fun p => groupFG_fundamentalGroup_sphericalSpaceFormQuotient G p

theorem finitelyGeneratedFundamentalGroup_finiteConnectedSum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ i, FinitelyGeneratedFundamentalGroup (L.get i)) :
    FinitelyGeneratedFundamentalGroup (finiteConnectedSum L) :=
  fun y => groupFG_fundamentalGroup_finiteConnectedSum_chosenPoint L
    (fun i => h i (chosenPoint (L.get i))) y

theorem finitelyGeneratedFundamentalGroup_finiteConnectedSum_iff_forall_factor
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    FinitelyGeneratedFundamentalGroup (finiteConnectedSum L) ↔
      ∀ i, FinitelyGeneratedFundamentalGroup (L.get i) := by
  constructor
  · intro h i p
    have hcop : Group.FG (Monoid.CoprodI fun j : Fin L.length =>
        FundamentalGroup (L.get j).Carrier (chosenPoint (L.get j))) := by
      obtain ⟨e⟩ := fundamentalGroup_finiteConnectedSum_freeProduct L
        (fun j => chosenPoint (L.get j)) (chosenPoint (finiteConnectedSum L))
      exact groupFG_of_mulEquiv e.symm (h (chosenPoint (finiteConnectedSum L)))
    exact groupFG_of_mulEquiv
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (chosenPoint (L.get i)) p).symm
      (groupFG_of_groupFG_coprodI _ i hcop)
  · exact finitelyGeneratedFundamentalGroup_finiteConnectedSum L

theorem finitelyGeneratedFundamentalGroup_connectedSum_sphereTwoTimesCircleLift :
    FinitelyGeneratedFundamentalGroup
      (finiteConnectedSum [sphereTwoTimesCircleLift, sphereTwoTimesCircleLift]) :=
  finitelyGeneratedFundamentalGroup_finiteConnectedSum _ fun i => by
    fin_cases i <;> exact finitelyGeneratedFundamentalGroup_sphereTwoTimesCircleLift

theorem not_moduleFinite_int_finsupp_int : ¬ Module.Finite ℤ (ℕ →₀ ℤ) :=
  Module.not_finite_of_infinite_basis (Finsupp.basisSingleOne (R := ℤ))

theorem not_groupFG_multiplicative_finsupp_int : ¬ Group.FG (Multiplicative (ℕ →₀ ℤ)) :=
  fun h => not_moduleFinite_int_finsupp_int
    (Module.Finite.iff_addGroup_fg.mpr (AddGroup.fg_iff_mul_fg.mpr h))

end DifferentialGeometry.Topology
