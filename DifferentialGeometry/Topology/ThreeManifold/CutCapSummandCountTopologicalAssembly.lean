import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumAbelianization
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLawInstances
import DifferentialGeometry.Topology.ThreeManifold.CutCapFrontierCanonicalReduction
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere
import DifferentialGeometry.Topology.Algebra.Module.RankInvariant

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u

private noncomputable def castMulEquiv
    {Φ : ConnectedClosedOrientedManifold.{u} 3 → Type u} [∀ M, Group (Φ M)]
    {A B : ConnectedClosedOrientedManifold.{u} 3} (h : A = B) : Φ A ≃* Φ B :=
  h ▸ MulEquiv.refl (Φ A)

private noncomputable def piFinSuccMulEquiv {n : ℕ} (β : Fin (n + 1) → Type u)
    [∀ i, Group (β i)] :
    β 0 × (∀ i : Fin n, β i.succ) ≃* (∀ i : Fin (n + 1), β i) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, fun i => f i.succ)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · simp
    · funext i
      simp
  right_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  map_mul' p q := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp

private noncomputable def constPiReindexMulEquiv {m n : ℕ} (h : m = n) (Ψ : Type u) [Group Ψ] :
    (Fin m → Ψ) ≃* (Fin n → Ψ) :=
  h ▸ MulEquiv.refl (Fin m → Ψ)

private noncomputable def piAppendMulEquiv (Φ : ConnectedClosedOrientedManifold.{u} 3 → Type u)
    [∀ M, Group (Φ M)] :
    ∀ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
      (∀ i : Fin (L ++ K).length, Φ ((L ++ K).get i)) ≃*
        (∀ i : Fin L.length, Φ (L.get i)) × (∀ i : Fin K.length, Φ (K.get i))
  | [], K =>
      { toFun := fun a => (1, a)
        invFun := fun p => p.2
        left_inv := fun _ => rfl
        right_inv := fun p => Prod.ext (funext fun i => Fin.elim0 i) rfl
        map_mul' := fun _ _ => Prod.ext (funext fun i => (one_mul _).symm) rfl }
  | a :: t, K => by
      refine (piFinSuccMulEquiv (fun i : Fin ((t ++ K).length + 1) =>
        Φ ((a :: (t ++ K)).get i))).symm.trans ?_
      refine (MulEquiv.prodCongr (MulEquiv.refl (Φ a)) (piAppendMulEquiv Φ t K)).trans ?_
      refine (MulEquiv.prodAssoc).symm.trans ?_
      exact MulEquiv.prodCongr
        (piFinSuccMulEquiv (fun i : Fin (t.length + 1) => Φ ((a :: t).get i)))
        (MulEquiv.refl _)

theorem abelianization_fundamentalGroup_of_isSphereTwoTimesCircleFactor
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S) :
    Nonempty (Abelianization (FundamentalGroup S.Carrier (chosenPoint S)) ≃*
      Multiplicative ℤ) := by
  obtain ⟨f, -⟩ := hS
  have hh : S.Carrier ≃ₜ sphereTwoTimesCircleLift.Carrier :=
    f.toHomeomorph.trans (Homeomorph.ulift (X := SphereTwoTimesCircle)).symm
  have hx : hh (hh.symm (chosenPoint sphereTwoTimesCircleLift)) =
      chosenPoint sphereTwoTimesCircleLift :=
    hh.apply_symm_apply _
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (chosenPoint S)
      (hh.symm (chosenPoint sphereTwoTimesCircleLift))).abelianizationCongr.trans
    ((fundamentalGroupMulEquivOfHomotopyEquiv hh.toHomotopyEquiv
        (hh.symm (chosenPoint sphereTwoTimesCircleLift))
        (chosenPoint sphereTwoTimesCircleLift) hx).abelianizationCongr.trans
      (abelianization_fundamentalGroup_sphereTwoTimesCircleLift).some)⟩

private noncomputable def replicatePiMulEquiv
    (S : ConnectedClosedOrientedManifold.{u} 3) (b : ℕ) :
    (∀ j : Fin (List.replicate b S).length,
        Abelianization (FundamentalGroup ((List.replicate b S).get j).Carrier
          (chosenPoint ((List.replicate b S).get j)))) ≃*
      (Fin b → Abelianization (FundamentalGroup S.Carrier (chosenPoint S))) :=
  (MulEquiv.piCongrRight fun j =>
      castMulEquiv
        (Φ := fun M : ConnectedClosedOrientedManifold.{u} 3 =>
          Abelianization (FundamentalGroup M.Carrier (chosenPoint M))) (by
        rw [List.get_eq_getElem]
        exact List.getElem_replicate j.isLt)).trans
    (constPiReindexMulEquiv (List.length_replicate (a := S) (n := b))
      (Abelianization (FundamentalGroup S.Carrier (chosenPoint S))))

theorem abelianization_fundamentalGroup_finiteConnectedSum_append_replicate
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S) (b : ℕ) :
    Nonempty (Abelianization (FundamentalGroup
        (finiteConnectedSum (L ++ List.replicate b S)).Carrier
        (chosenPoint (finiteConnectedSum (L ++ List.replicate b S)))) ≃*
      Abelianization (FundamentalGroup (finiteConnectedSum L).Carrier
        (chosenPoint (finiteConnectedSum L))) × (Fin b → Multiplicative ℤ)) := by
  have hfree := (abelianization_fundamentalGroup_finiteConnectedSum_freeProduct
      (L ++ List.replicate b S)
      (fun i => chosenPoint ((L ++ List.replicate b S).get i))
      (chosenPoint (finiteConnectedSum (L ++ List.replicate b S)))).some
  have hsplit := piAppendMulEquiv (fun M : ConnectedClosedOrientedManifold.{u} 3 =>
      Abelianization (FundamentalGroup M.Carrier (chosenPoint M))) L (List.replicate b S)
  have hleft := (abelianization_fundamentalGroup_finiteConnectedSum_freeProduct L
      (fun i => chosenPoint (L.get i)) (chosenPoint (finiteConnectedSum L))).some.symm
  have hrep := replicatePiMulEquiv S b
  have hSiso := MulEquiv.piCongrRight fun _ : Fin b =>
    (abelianization_fundamentalGroup_of_isSphereTwoTimesCircleFactor hS).some
  exact ⟨hfree.trans (hsplit.trans ((MulEquiv.prodCongr hleft hrep).trans
    (MulEquiv.prodCongr
      (MulEquiv.refl (Abelianization (FundamentalGroup (finiteConnectedSum L).Carrier
        (chosenPoint (finiteConnectedSum L))))) hSiso)))⟩

theorem moduleFinite_abelianizationFundamentalGroup_standardThreeSphereLift
    (p : standardThreeSphereLift.{u}.Carrier) :
    Module.Finite ℤ (Additive (Abelianization
      (FundamentalGroup standardThreeSphereLift.{u}.Carrier p))) := by
  have hsc : SimplyConnectedSpace standardThreeSphereLift.{u}.Carrier :=
    (Homeomorph.ulift (X := SphereThree)).toHomotopyEquiv.simplyConnectedSpace
  have hsub : Subsingleton (Abelianization
      (FundamentalGroup standardThreeSphereLift.{u}.Carrier p)) :=
    (show Function.Surjective (Abelianization.of :
        FundamentalGroup standardThreeSphereLift.{u}.Carrier p → _) from
      Quot.mk_surjective).subsingleton
  exact @Module.Finite.of_finite ℤ
    (Additive (Abelianization (FundamentalGroup standardThreeSphereLift.{u}.Carrier p)))
    _ _ _ (@Finite.of_subsingleton _ hsub)

theorem moduleFinite_abelianizationFundamentalGroup_sphereTwoTimesCircleLift
    (p : sphereTwoTimesCircleLift.Carrier) :
    Module.Finite ℤ (Additive (Abelianization
      (FundamentalGroup sphereTwoTimesCircleLift.Carrier p))) := by
  have h₁ : Abelianization (FundamentalGroup sphereTwoTimesCircleLift.Carrier p) ≃*
      Abelianization (FundamentalGroup sphereTwoTimesCircleLift.Carrier
        (chosenPoint sphereTwoTimesCircleLift)) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p
      (chosenPoint sphereTwoTimesCircleLift)).abelianizationCongr
  have h₂ : Abelianization (FundamentalGroup sphereTwoTimesCircleLift.Carrier
      (chosenPoint sphereTwoTimesCircleLift)) ≃* Multiplicative ℤ :=
    (abelianization_fundamentalGroup_sphereTwoTimesCircleLift).some
  exact Module.Finite.equiv (AddEquiv.toIntLinearEquiv
    (MulEquiv.toAdditive (h₁.trans h₂))).symm

theorem moduleFinite_abelianizationFundamentalGroup_connectedSum_sphereTwoTimesCircleLift
    (p : (connectedSum sphereTwoTimesCircleLift sphereTwoTimesCircleLift).Carrier) :
    Module.Finite ℤ (Additive (Abelianization (FundamentalGroup
      (connectedSum sphereTwoTimesCircleLift sphereTwoTimesCircleLift).Carrier p))) := by
  have h₁ : Abelianization (FundamentalGroup
        (connectedSum sphereTwoTimesCircleLift sphereTwoTimesCircleLift).Carrier p) ≃*
      Abelianization (FundamentalGroup
        (connectedSum sphereTwoTimesCircleLift sphereTwoTimesCircleLift).Carrier
        (chosenPoint (connectedSum sphereTwoTimesCircleLift sphereTwoTimesCircleLift))) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p
      (chosenPoint (connectedSum sphereTwoTimesCircleLift
        sphereTwoTimesCircleLift))).abelianizationCongr
  have h₂ : Abelianization (FundamentalGroup
        (connectedSum sphereTwoTimesCircleLift sphereTwoTimesCircleLift).Carrier
        (chosenPoint (connectedSum sphereTwoTimesCircleLift sphereTwoTimesCircleLift))) ≃*
      Abelianization (FundamentalGroup sphereTwoTimesCircleLift.Carrier
          (chosenPoint sphereTwoTimesCircleLift)) ×
        Abelianization (FundamentalGroup sphereTwoTimesCircleLift.Carrier
          (chosenPoint sphereTwoTimesCircleLift)) :=
    (abelianization_fundamentalGroup_connectedSum sphereTwoTimesCircleLift
      sphereTwoTimesCircleLift).some
  have h₃ : Abelianization (FundamentalGroup sphereTwoTimesCircleLift.Carrier
          (chosenPoint sphereTwoTimesCircleLift)) ×
        Abelianization (FundamentalGroup sphereTwoTimesCircleLift.Carrier
          (chosenPoint sphereTwoTimesCircleLift)) ≃* Multiplicative ℤ × Multiplicative ℤ :=
    (abelianization_fundamentalGroup_sphereTwoTimesCircleLift).some.prodCongr
      (abelianization_fundamentalGroup_sphereTwoTimesCircleLift).some
  exact Module.Finite.equiv (AddEquiv.toIntLinearEquiv
    (MulEquiv.toAdditive (h₁.trans (h₂.trans h₃)))).symm

theorem moduleFinite_abelianizationFundamentalGroup_sphericalSpaceFormQuotient
    (G : SphericalSpaceFormGroup) (p : G.manifold.Carrier) :
    Module.Finite ℤ (Additive (Abelianization (FundamentalGroup G.manifold.Carrier p))) := by
  have h : Abelianization (FundamentalGroup G.manifold.Carrier p) ≃*
      Abelianization G.group := (G.fundamentalGroupManifoldEquiv p).abelianizationCongr
  have hfs : Finite (Abelianization G.group) :=
    Finite.of_surjective (fun x : G.group => Abelianization.of x) Quot.mk_surjective
  have hf : Finite (Abelianization (FundamentalGroup G.manifold.Carrier p)) :=
    h.toEquiv.finite_iff.mpr hfs
  exact @Module.Finite.of_finite ℤ
    (Additive (Abelianization (FundamentalGroup G.manifold.Carrier p))) _ _ _ hf

def FinitelyGeneratedAbelianizationFundamentalGroupClosedThreeManifold : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3) (p : M.Carrier),
    Module.Finite ℤ (Additive (Abelianization (FundamentalGroup M.Carrier p)))

theorem exists_mulEquiv_abelianization_fundamentalGroup_of_orientedDiffeomorph
    {A B : ConnectedClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph A.toClosedOrientedManifold
      B.toClosedOrientedManifold)) :
    Nonempty (Abelianization (FundamentalGroup A.Carrier (chosenPoint A)) ≃*
      Abelianization (FundamentalGroup B.Carrier (chosenPoint B))) := by
  obtain ⟨ρ⟩ := h
  have hh : A.Carrier ≃ₜ B.Carrier := ρ.1.toHomeomorph
  have hx : hh (hh.symm (chosenPoint B)) = chosenPoint B := hh.apply_symm_apply _
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (chosenPoint A)
      (hh.symm (chosenPoint B))).abelianizationCongr.trans
    (fundamentalGroupMulEquivOfHomotopyEquiv hh.toHomotopyEquiv (hh.symm (chosenPoint B))
      (chosenPoint B) hx).abelianizationCongr⟩

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem sphericalSummandExponentUnique_of_finitelyGeneratedAbelianizationFundamentalGroup
    (hfin : FinitelyGeneratedAbelianizationFundamentalGroupClosedThreeManifold.{u})
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S) :
    E.sphericalSummandExponentUnique S := by
  intro C b b' hb hb'
  have hdiff : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.canonicalEnumeration C ++ List.replicate b S)).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b' S)).toClosedOrientedManifold) :=
    ⟨hb.some.symm.trans hb'.some⟩
  have hH := (exists_mulEquiv_abelianization_fundamentalGroup_of_orientedDiffeomorph hdiff).some
  have hsplitb := (abelianization_fundamentalGroup_finiteConnectedSum_append_replicate
    (E.canonicalEnumeration C) S hS b).some
  have hsplitb' := (abelianization_fundamentalGroup_finiteConnectedSum_append_replicate
    (E.canonicalEnumeration C) S hS b').some
  have hfing : Module.Finite ℤ (Additive (Abelianization (FundamentalGroup
      (finiteConnectedSum (E.canonicalEnumeration C)).Carrier
      (chosenPoint (finiteConnectedSum (E.canonicalEnumeration C)))))) :=
    hfin (finiteConnectedSum (E.canonicalEnumeration C))
      (chosenPoint (finiteConnectedSum (E.canonicalEnumeration C)))
  exact @DifferentialGeometry.Algebra.Module.nat_eq_of_mulEquiv_prod_fin_multiplicativeInt
    (Abelianization (FundamentalGroup (finiteConnectedSum (E.canonicalEnumeration C)).Carrier
      (chosenPoint (finiteConnectedSum (E.canonicalEnumeration C))))) _ hfing _ _
    (hsplitb.symm.trans (hH.trans hsplitb'))

theorem cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_finitelyGenerated
    (hfin : FinitelyGeneratedAbelianizationFundamentalGroupClosedThreeManifold.{u})
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (hex : E.sphericalGraphSumRealization S) : E.cutCapSummandCountDetermined :=
  E.cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique
    hS hex (E.sphericalSummandExponentUnique_of_finitelyGeneratedAbelianizationFundamentalGroup
      hfin hS)

end SphericalCutCapTransition

end DifferentialGeometry.Topology
