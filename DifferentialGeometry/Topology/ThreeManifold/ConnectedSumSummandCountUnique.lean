import DifferentialGeometry.Topology.Algebra.Module.RankInvariant
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLawInstances
import DifferentialGeometry.Topology.ThreeManifold.CutCapSphericalExponentReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapSummandCountInvariance
import DifferentialGeometry.Topology.VanKampen.ConnectedSumAbelianization
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumAbelianization
import Mathlib.RingTheory.Finiteness.Basic

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff
open scoped TensorProduct

namespace DifferentialGeometry.Topology

universe u

private noncomputable def abelianizationFundamentalGroupMulEquivOfOrientedDiffeomorph
    {X Y : ConnectedClosedOrientedManifold.{u} 3}
    (e : ClosedOrientedManifold.OrientedDiffeomorph X.toClosedOrientedManifold
      Y.toClosedOrientedManifold) (x : X.Carrier) (y : Y.Carrier) :
    Abelianization (FundamentalGroup X.Carrier x) ≃*
      Abelianization (FundamentalGroup Y.Carrier y) :=
  (MulEquiv.abelianizationCongr
    (fundamentalGroupMulEquivOfHomotopyEquiv e.1.toHomeomorph.toHomotopyEquiv
      x (e.1 x) rfl)).trans
    (MulEquiv.abelianizationCongr
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (e.1 x) y))

private noncomputable def additiveAddEquivOfMulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : Additive G ≃+ Additive H where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_mul

private theorem nat_eq_of_mulEquiv_prod_fin_multiplicativeInt_of_tensorFinite
    (A : Type*) [CommGroup A] [Module.Finite ℚ (ℚ ⊗[ℤ] Additive A)]
    {b b' : ℕ}
    (e : A × (Fin b → Multiplicative ℤ) ≃* A × (Fin b' → Multiplicative ℤ)) :
    b = b' :=
  DifferentialGeometry.Algebra.Module.nat_eq_of_addEquiv_prod_fin_int (Additive A)
    ((AddEquiv.refl _).trans
      (({ toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
          map_add' := e.map_mul } :
          Additive (A × (Fin b → Multiplicative ℤ)) ≃+
            Additive (A × (Fin b' → Multiplicative ℤ))).trans
        (AddEquiv.refl _)))

private noncomputable def tensorProductLinearEquivOfMulEquiv {G H : Type*}
    [CommGroup G] [CommGroup H]
    (e : G ≃* H) : (ℚ ⊗[ℤ] Additive G) ≃ₗ[ℚ] (ℚ ⊗[ℤ] Additive H) :=
  LinearEquiv.baseChange ℤ ℚ (Additive G) (Additive H)
    (additiveAddEquivOfMulEquiv e).toIntLinearEquiv

private noncomputable def abelianizationFundamentalGroupMulEquivIntOfIsSphereTwoTimesCircleFactor
    {F : ConnectedClosedOrientedManifold.{u} 3}
    (hF : isSphereTwoTimesCircleFactor F) (x : F.Carrier) :
    Abelianization (FundamentalGroup F.Carrier x) ≃* Multiplicative ℤ := by
  let f := Classical.choose hF
  exact (MulEquiv.abelianizationCongr
      (fundamentalGroupMulEquivOfHomotopyEquiv f.toHomeomorph.toHomotopyEquiv x (f x) rfl)).trans
    ((MulEquiv.abelianizationCongr
        (exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle (f x)).some).trans
      (Abelianization.equivOfComm).symm)

private theorem sum_map_eq_length_of_forall_eq_one
    (ι : ConnectedClosedOrientedManifold.{u} 3 → ℕ)
    {L : List (ConnectedClosedOrientedManifold.{u} 3)}
    (h : ∀ F ∈ L, ι F = 1) : (L.map ι).sum = L.length := by
  induction L with
  | nil => simp
  | cons F L ih =>
    rw [List.map_cons, List.sum_cons, h F (by simp),
      ih fun G hG => h G (by simp [hG]), List.length_cons]
    omega

theorem finiteConnectedSumSummandCountUnique_of_additiveInvariant
    (ι : ConnectedClosedOrientedManifold.{u} 3 → ℕ)
    (hinv : ∀ {A B : ConnectedClosedOrientedManifold.{u} 3},
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        A.toClosedOrientedManifold B.toClosedOrientedManifold) → ι A = ι B)
    (hunit : ι standardThreeSphereLift.{u} = 0)
    (hadd : ∀ A B : ConnectedClosedOrientedManifold.{u} 3,
      ι (connectedSum A B) = ι A + ι B)
    (hone : ∀ {F : ConnectedClosedOrientedManifold.{u} 3},
      isSphereTwoTimesCircleFactor F → ι F = 1)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    finiteConnectedSumSummandCountUnique L := by
  intro K K' hK hK' hdiff
  have hι := hinv hdiff
  rw [finiteConnectedSum_additiveInvariant ι hunit hadd (L ++ K),
    finiteConnectedSum_additiveInvariant ι hunit hadd (L ++ K')] at hι
  simp only [List.map_append, List.sum_append] at hι
  rw [sum_map_eq_length_of_forall_eq_one ι fun F hF => hone (hK F hF),
    sum_map_eq_length_of_forall_eq_one ι fun F hF => hone (hK' F hF)] at hι
  exact Nat.add_left_cancel hι

theorem abelianization_fundamentalGroup_finiteConnectedSum_append
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (Abelianization
        (FundamentalGroup (finiteConnectedSum (L ++ K)).Carrier
          (chosenPoint (finiteConnectedSum (L ++ K)))) ≃*
      Abelianization
          (FundamentalGroup (finiteConnectedSum L).Carrier
            (chosenPoint (finiteConnectedSum L))) ×
        Abelianization
          (FundamentalGroup (finiteConnectedSum K).Carrier
            (chosenPoint (finiteConnectedSum K)))) := by
  obtain ⟨e⟩ := finiteConnectedSum_append L K
  let q := chosenPoint (connectedSum (finiteConnectedSum L) (finiteConnectedSum K))
  obtain ⟨e'⟩ := abelianization_fundamentalGroup_connectedSum
    (finiteConnectedSum L) (finiteConnectedSum K)
  let p := chosenPoint (finiteConnectedSum (L ++ K))
  exact ⟨(abelianizationFundamentalGroupMulEquivOfOrientedDiffeomorph e
      p (e.1 p)).trans
    ((MulEquiv.abelianizationCongr
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
        (e.1 p) q)).trans e')⟩

theorem abelianization_fundamentalGroup_finiteConnectedSum_sphereTwoTimesCircleFactors
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, isSphereTwoTimesCircleFactor F) :
    Nonempty (Abelianization
        (FundamentalGroup (finiteConnectedSum L).Carrier
          (chosenPoint (finiteConnectedSum L))) ≃*
      (Fin L.length → Multiplicative ℤ)) := by
  obtain ⟨e⟩ := abelianization_fundamentalGroup_finiteConnectedSum_freeProduct L
    (fun i => chosenPoint (L.get i)) (chosenPoint (finiteConnectedSum L))
  refine ⟨e.trans ?_⟩
  exact MulEquiv.piCongrRight fun i =>
    abelianizationFundamentalGroupMulEquivIntOfIsSphereTwoTimesCircleFactor
      (hL (L.get i) (List.get_mem L i)) (chosenPoint (L.get i))

def finiteConnectedSumAbelianizationModuleFinite
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  Module.Finite ℤ (Additive (Abelianization
    (FundamentalGroup (finiteConnectedSum L).Carrier
      (chosenPoint (finiteConnectedSum L)))))

def finiteConnectedSumAbelianizationRationalFinite
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  Module.Finite ℚ (ℚ ⊗[ℤ] Additive (Abelianization
    (FundamentalGroup (finiteConnectedSum L).Carrier
      (chosenPoint (finiteConnectedSum L)))))

def connectedClosedOrientedManifoldAbelianizationModuleFinite
    (M : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  Module.Finite ℤ (Additive (Abelianization
    (FundamentalGroup M.Carrier (chosenPoint M))))

def connectedClosedOrientedManifoldAbelianizationRationalFinite
    (M : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  Module.Finite ℚ (ℚ ⊗[ℤ] Additive (Abelianization
    (FundamentalGroup M.Carrier (chosenPoint M))))

theorem finiteConnectedSumAbelianizationRationalFinite_of_moduleFinite
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : finiteConnectedSumAbelianizationModuleFinite L) :
    finiteConnectedSumAbelianizationRationalFinite L :=
  DifferentialGeometry.Algebra.Module.finite_tensorProduct_baseChange
    (R := ℤ) (A := ℚ) (M := Additive (Abelianization
      (FundamentalGroup (finiteConnectedSum L).Carrier
        (chosenPoint (finiteConnectedSum L))))) h

theorem connectedClosedOrientedManifoldAbelianizationRationalFinite_of_moduleFinite
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (h : connectedClosedOrientedManifoldAbelianizationModuleFinite M) :
    connectedClosedOrientedManifoldAbelianizationRationalFinite M :=
  DifferentialGeometry.Algebra.Module.finite_tensorProduct_baseChange
    (R := ℤ) (A := ℚ) (M := Additive (Abelianization
      (FundamentalGroup M.Carrier (chosenPoint M)))) h

theorem connectedClosedOrientedManifoldAbelianizationModuleFinite_of_isSphereTwoTimesCircleFactor
    {F : ConnectedClosedOrientedManifold.{u} 3}
    (hF : isSphereTwoTimesCircleFactor F) :
    connectedClosedOrientedManifoldAbelianizationModuleFinite F :=
  (Module.Finite.equiv_iff (additiveAddEquivOfMulEquiv
    (abelianizationFundamentalGroupMulEquivIntOfIsSphereTwoTimesCircleFactor
      hF (chosenPoint F))).toIntLinearEquiv).mpr (inferInstance)

theorem finiteConnectedSumAbelianizationModuleFinite_of_sphereTwoTimesCircleFactors
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, isSphereTwoTimesCircleFactor F) :
    finiteConnectedSumAbelianizationModuleFinite L := by
  obtain ⟨e⟩ :=
    abelianization_fundamentalGroup_finiteConnectedSum_sphereTwoTimesCircleFactors L hL
  exact (Module.Finite.equiv_iff
    (additiveAddEquivOfMulEquiv e).toIntLinearEquiv).mpr (inferInstance)

theorem finiteConnectedSumAbelianizationModuleFinite_of_forall_factor
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ i : Fin L.length, connectedClosedOrientedManifoldAbelianizationModuleFinite
      (L.get i)) :
    finiteConnectedSumAbelianizationModuleFinite L := by
  obtain ⟨e⟩ := abelianization_fundamentalGroup_finiteConnectedSum_freeProduct L
    (fun i => chosenPoint (L.get i)) (chosenPoint (finiteConnectedSum L))
  refine (Module.Finite.equiv_iff (additiveAddEquivOfMulEquiv e).toIntLinearEquiv).mpr ?_
  exact @Module.Finite.pi ℤ _ (Fin L.length)
    (fun i => Additive (Abelianization
      (FundamentalGroup (L.get i).Carrier (chosenPoint (L.get i))))) _ _ _ h

theorem finiteConnectedSumAbelianizationRationalFinite_of_forall_factor
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ i : Fin L.length, connectedClosedOrientedManifoldAbelianizationRationalFinite
      (L.get i)) :
    finiteConnectedSumAbelianizationRationalFinite L := by
  obtain ⟨e⟩ := abelianization_fundamentalGroup_finiteConnectedSum_freeProduct L
    (fun i => chosenPoint (L.get i)) (chosenPoint (finiteConnectedSum L))
  refine (Module.Finite.equiv_iff (tensorProductLinearEquivOfMulEquiv e)).mpr ?_
  refine (Module.Finite.equiv_iff
    (TensorProduct.piRight ℤ ℚ ℚ
      (fun i => Additive (Abelianization
        (FundamentalGroup (L.get i).Carrier (chosenPoint (L.get i))))))).mpr ?_
  exact @Module.Finite.pi ℚ _ (Fin L.length)
    (fun i => ℚ ⊗[ℤ] Additive (Abelianization
      (FundamentalGroup (L.get i).Carrier (chosenPoint (L.get i))))) _ _ _ h

theorem finiteConnectedSumAbelianizationRationalFinite_iff_forall_factor
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    finiteConnectedSumAbelianizationRationalFinite L ↔
      ∀ i : Fin L.length, connectedClosedOrientedManifoldAbelianizationRationalFinite
        (L.get i) := by
  constructor
  · intro hfin i
    obtain ⟨e⟩ := abelianization_fundamentalGroup_finiteConnectedSum_freeProduct L
      (fun i => chosenPoint (L.get i)) (chosenPoint (finiteConnectedSum L))
    have hprod : Module.Finite ℚ (ℚ ⊗[ℤ] Additive
        ((i : Fin L.length) → Abelianization
          (FundamentalGroup (L.get i).Carrier (chosenPoint (L.get i))))) :=
      (Module.Finite.equiv_iff (tensorProductLinearEquivOfMulEquiv e)).mp hfin
    have hpi : Module.Finite ℚ ((i : Fin L.length) →
        ℚ ⊗[ℤ] Additive (Abelianization
          (FundamentalGroup (L.get i).Carrier (chosenPoint (L.get i))))) :=
      (Module.Finite.equiv_iff (TensorProduct.piRight ℤ ℚ ℚ
        (fun i => Additive (Abelianization
          (FundamentalGroup (L.get i).Carrier (chosenPoint (L.get i))))))).mp hprod
    exact @Module.Finite.of_pi ℚ _ (Fin L.length)
      (fun i => ℚ ⊗[ℤ] Additive (Abelianization
        (FundamentalGroup (L.get i).Carrier (chosenPoint (L.get i))))) _ _ hpi i
  · exact finiteConnectedSumAbelianizationRationalFinite_of_forall_factor L

theorem finiteConnectedSumAbelianizationModuleFinite_iff_forall_factor
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    finiteConnectedSumAbelianizationModuleFinite L ↔
      ∀ i : Fin L.length, connectedClosedOrientedManifoldAbelianizationModuleFinite
        (L.get i) := by
  constructor
  · intro hfin i
    obtain ⟨e⟩ := abelianization_fundamentalGroup_finiteConnectedSum_freeProduct L
      (fun i => chosenPoint (L.get i)) (chosenPoint (finiteConnectedSum L))
    have hprod : Module.Finite ℤ (Additive
        ((i : Fin L.length) → Abelianization
          (FundamentalGroup (L.get i).Carrier (chosenPoint (L.get i))))) :=
      (Module.Finite.equiv_iff (additiveAddEquivOfMulEquiv e).toIntLinearEquiv).mp hfin
    change Module.Finite ℤ ((i : Fin L.length) → Additive (Abelianization
      (FundamentalGroup (L.get i).Carrier (chosenPoint (L.get i))))) at hprod
    exact @Module.Finite.of_pi ℤ _ (Fin L.length)
      (fun i => Additive (Abelianization
        (FundamentalGroup (L.get i).Carrier (chosenPoint (L.get i))))) _ _ hprod i
  · exact finiteConnectedSumAbelianizationModuleFinite_of_forall_factor L

theorem finiteConnectedSumSummandCountUnique_of_abelianizationRationalFinite
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hfin : finiteConnectedSumAbelianizationRationalFinite L) :
    finiteConnectedSumSummandCountUnique L := by
  intro K K' hK hK' hdiff
  let A := Abelianization
    (FundamentalGroup (finiteConnectedSum L).Carrier
      (chosenPoint (finiteConnectedSum L)))
  let eK : Abelianization
      (FundamentalGroup (finiteConnectedSum (L ++ K)).Carrier
        (chosenPoint (finiteConnectedSum (L ++ K)))) ≃*
      A × (Fin K.length → Multiplicative ℤ) :=
    (abelianization_fundamentalGroup_finiteConnectedSum_append L K).some.trans
      ((MulEquiv.refl A).prodCongr
        (abelianization_fundamentalGroup_finiteConnectedSum_sphereTwoTimesCircleFactors
          K hK).some)
  let eK' : Abelianization
      (FundamentalGroup (finiteConnectedSum (L ++ K')).Carrier
        (chosenPoint (finiteConnectedSum (L ++ K')))) ≃*
      A × (Fin K'.length → Multiplicative ℤ) :=
    (abelianization_fundamentalGroup_finiteConnectedSum_append L K').some.trans
      ((MulEquiv.refl A).prodCongr
        (abelianization_fundamentalGroup_finiteConnectedSum_sphereTwoTimesCircleFactors
          K' hK').some)
  let ediff := abelianizationFundamentalGroupMulEquivOfOrientedDiffeomorph hdiff.some
    (chosenPoint (finiteConnectedSum (L ++ K)))
    (chosenPoint (finiteConnectedSum (L ++ K')))
  exact @nat_eq_of_mulEquiv_prod_fin_multiplicativeInt_of_tensorFinite
    A _ hfin K.length K'.length (eK.symm.trans (ediff.trans eK'))

theorem finiteConnectedSumSummandCountUnique_of_abelianizationModuleFinite
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hfin : finiteConnectedSumAbelianizationModuleFinite L) :
    finiteConnectedSumSummandCountUnique L :=
  finiteConnectedSumSummandCountUnique_of_abelianizationRationalFinite L
    (finiteConnectedSumAbelianizationRationalFinite_of_moduleFinite L hfin)

theorem finiteConnectedSumSummandCountUnique_of_sphereTwoTimesCircleFactors
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, isSphereTwoTimesCircleFactor F) :
    finiteConnectedSumSummandCountUnique L :=
  finiteConnectedSumSummandCountUnique_of_abelianizationModuleFinite L
    (finiteConnectedSumAbelianizationModuleFinite_of_sphereTwoTimesCircleFactors L hL)

theorem finiteConnectedSumSummandCountUnique_of_forall_factor_abelianizationModuleFinite
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ i : Fin L.length, connectedClosedOrientedManifoldAbelianizationModuleFinite
      (L.get i)) :
    finiteConnectedSumSummandCountUnique L :=
  finiteConnectedSumSummandCountUnique_of_abelianizationModuleFinite L
    (finiteConnectedSumAbelianizationModuleFinite_of_forall_factor L h)

theorem connectedClosedOrientedManifoldAbelianizationRationalFinite_of_isSphereTwoTimesCircleFactor
    {F : ConnectedClosedOrientedManifold.{u} 3}
    (hF : isSphereTwoTimesCircleFactor F) :
    connectedClosedOrientedManifoldAbelianizationRationalFinite F :=
  connectedClosedOrientedManifoldAbelianizationRationalFinite_of_moduleFinite F
    (connectedClosedOrientedManifoldAbelianizationModuleFinite_of_isSphereTwoTimesCircleFactor hF)

theorem finiteConnectedSumAbelianizationRationalFinite_of_sphereTwoTimesCircleFactors
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, isSphereTwoTimesCircleFactor F) :
    finiteConnectedSumAbelianizationRationalFinite L :=
  finiteConnectedSumAbelianizationRationalFinite_of_moduleFinite L
    (finiteConnectedSumAbelianizationModuleFinite_of_sphereTwoTimesCircleFactors L hL)

theorem finiteConnectedSumSummandCountUnique_of_forall_factor_abelianizationRationalFinite
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ i : Fin L.length, connectedClosedOrientedManifoldAbelianizationRationalFinite
      (L.get i)) :
    finiteConnectedSumSummandCountUnique L :=
  finiteConnectedSumSummandCountUnique_of_abelianizationRationalFinite L
    (finiteConnectedSumAbelianizationRationalFinite_of_forall_factor L h)

theorem connectedClosedOrientedManifoldAbelianizationModuleFinite_sphereTwoTimesCircleLift :
    connectedClosedOrientedManifoldAbelianizationModuleFinite
      sphereTwoTimesCircleLift :=
  connectedClosedOrientedManifoldAbelianizationModuleFinite_of_isSphereTwoTimesCircleFactor
    isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift

theorem connectedClosedOrientedManifoldAbelianizationRationalFinite_sphereTwoTimesCircleLift :
    connectedClosedOrientedManifoldAbelianizationRationalFinite
      sphereTwoTimesCircleLift :=
  connectedClosedOrientedManifoldAbelianizationRationalFinite_of_isSphereTwoTimesCircleFactor
    isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift

theorem finiteConnectedSumSummandCountUnique_nil :
    finiteConnectedSumSummandCountUnique
      ([] : List (ConnectedClosedOrientedManifold.{u} 3)) :=
  finiteConnectedSumSummandCountUnique_of_sphereTwoTimesCircleFactors [] (by simp)

theorem finiteConnectedSumSummandCountUnique_singleton_sphereTwoTimesCircleLift :
    finiteConnectedSumSummandCountUnique [sphereTwoTimesCircleLift] :=
  finiteConnectedSumSummandCountUnique_of_sphereTwoTimesCircleFactors
    [sphereTwoTimesCircleLift] (by
      intro F hF
      rw [List.mem_singleton] at hF
      subst hF
      exact isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift)

end DifferentialGeometry.Topology
