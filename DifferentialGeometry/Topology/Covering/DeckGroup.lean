import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

def coveringDeckGroup {E X : Type*} [TopologicalSpace E]
    (p : E → X) : Subgroup (Equiv.Perm E) where
  carrier := {phi | Continuous phi ∧ Continuous phi.symm ∧ ∀ e, p (phi e) = p e}
  one_mem' := ⟨continuous_id, continuous_id, fun _ => rfl⟩
  mul_mem' := by
    rintro phi psi ⟨hphi, hphiInv, hphiMap⟩ ⟨hpsi, hpsiInv, hpsiMap⟩
    refine ⟨hphi.comp hpsi, ?_, ?_⟩
    · exact hpsiInv.comp hphiInv
    · intro e
      rw [Equiv.Perm.coe_mul, Function.comp_apply, hphiMap, hpsiMap]
  inv_mem' := by
    rintro phi ⟨hphi, hphiInv, hphiMap⟩
    refine ⟨hphiInv, hphi, ?_⟩
    intro e
    simpa using (hphiMap (phi.symm e)).symm

instance coveringDeckGroup_continuousConstSMul
    {E X : Type*} [TopologicalSpace E] {p : E → X} :
    ContinuousConstSMul (coveringDeckGroup p) E where
  continuous_const_smul gamma := gamma.property.1

theorem coveringDeckGroup_map
    {E X : Type*} [TopologicalSpace E] {p : E → X}
    (gamma : coveringDeckGroup p) (e : E) :
    p (gamma • e) = p e :=
  gamma.property.2.2 e

theorem coveringDeckGroup_eq_one_of_apply_eq
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E] {p : E → X} (hp : IsCoveringMap p)
    (gamma : coveringDeckGroup p) (e : E) (he : gamma • e = e) :
    gamma = 1 := by
  change gamma.1 e = e at he
  apply Subtype.ext
  apply Equiv.ext
  intro y
  have hgamma : (gamma.1 : E → E) = id := hp.eq_of_comp_eq
    gamma.property.1 continuous_id (by
      funext z
      exact gamma.property.2.2 z) e (by simpa using he)
  exact congrFun hgamma y

private theorem exists_coveringDeckGroup_apply_eq
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) {e0 e1 : E} (he : p e1 = p e0) :
    ∃ gamma : coveringDeckGroup p, gamma • e0 = e1 := by
  let pcont : C(E, X) := ⟨p, hp.continuous⟩
  obtain ⟨F, hF, _⟩ := hp.existsUnique_continuousMap_lifts pcont e0 e1 he
  obtain ⟨G, hG, _⟩ := hp.existsUnique_continuousMap_lifts pcont e1 e0 he.symm
  have hFmap (z : E) : p (F z) = p z := congrFun hF.2 z
  have hGmap (z : E) : p (G z) = p z := congrFun hG.2 z
  have hFG : (F : E → E) ∘ G = id := hp.eq_of_comp_eq
    (F.continuous.comp G.continuous) continuous_id (by
      funext z
      change p (F (G z)) = p z
      rw [hFmap, hGmap]) e1 (by simp [hF.1, hG.1])
  have hGF : (G : E → E) ∘ F = id := hp.eq_of_comp_eq
    (G.continuous.comp F.continuous) continuous_id (by
      funext z
      change p (G (F z)) = p z
      rw [hGmap, hFmap]) e0 (by simp [hF.1, hG.1])
  let phi : Equiv.Perm E :=
    { toFun := F
      invFun := G
      left_inv := congrFun hGF
      right_inv := congrFun hFG }
  let gamma : coveringDeckGroup p :=
    ⟨phi, F.continuous, G.continuous, fun z => congrFun hF.2 z⟩
  exact ⟨gamma, hF.1⟩

theorem coveringDeckGroup_apply_eq_iff
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) {e1 e2 : E} :
    p e1 = p e2 ↔ e1 ∈ MulAction.orbit (coveringDeckGroup p) e2 := by
  constructor
  · intro he
    obtain ⟨gamma, hgamma⟩ := exists_coveringDeckGroup_apply_eq hp he
    exact ⟨gamma, hgamma⟩
  · rintro ⟨gamma, rfl⟩
    exact coveringDeckGroup_map gamma e2

theorem isQuotientCoveringMap_coveringDeckGroup
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    IsQuotientCoveringMap p (coveringDeckGroup p) where
  toIsQuotientMap := hp.isQuotientMap hsurj
  continuous_const_smul := continuous_const_smul
  apply_eq_iff_mem_orbit := coveringDeckGroup_apply_eq_iff hp
  disjoint e := by
    obtain ⟨U, hU, hUEmbedding⟩ :=
      isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hp.isLocalHomeomorph e
    refine ⟨U, hU, ?_⟩
    intro gamma hinter
    obtain ⟨_, ⟨y, hyU, rfl⟩, hgammaU⟩ := hinter
    have hUInj : Set.InjOn p U :=
      Set.injOn_iff_injective.mpr hUEmbedding.injective
    have hfix : gamma • y = y :=
      hUInj hgammaU hyU (coveringDeckGroup_map gamma y)
    exact coveringDeckGroup_eq_one_of_apply_eq hp gamma y hfix

noncomputable def coveringDeckGroupQuotientHomeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    MulAction.orbitRel.Quotient (coveringDeckGroup p) E ≃ₜ X := by
  let Q := MulAction.orbitRel.Quotient (coveringDeckGroup p) E
  let q : E → Q := Quotient.mk''
  let F : Q → X := Quotient.lift p (fun e1 e2 he =>
    (coveringDeckGroup_apply_eq_iff hp).mpr he)
  have hFcont : Continuous F := hp.continuous.quotient_lift
    (fun e1 e2 he => (coveringDeckGroup_apply_eq_iff hp).mpr he)
  have hFsurj : Function.Surjective F := by
    intro x
    obtain ⟨e, rfl⟩ := hsurj x
    exact ⟨q e, rfl⟩
  have hFinj : Function.Injective F := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | _ e1 =>
      induction b using Quotient.inductionOn with
      | _ e2 =>
        apply Quotient.sound
        exact (coveringDeckGroup_apply_eq_iff hp).mp hab
  let equiv : Q ≃ X := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
  have hinvComp : equiv.invFun ∘ p = q := by
    funext e
    apply equiv.injective
    change equiv (equiv.symm (p e)) = equiv (q e)
    rw [Equiv.apply_symm_apply]
    rfl
  exact
    { toEquiv := equiv
      continuous_toFun := hFcont
      continuous_invFun := (hp.isQuotientMap hsurj).continuous_iff.mpr (by
        rw [hinvComp]
        exact continuous_quot_mk) }

theorem coveringDeckGroupQuotientHomeomorph_apply
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (e : E) :
    coveringDeckGroupQuotientHomeomorph hp hsurj (Quotient.mk'' e) = p e := by
  rw [coveringDeckGroupQuotientHomeomorph]
  rfl

end DifferentialGeometry
