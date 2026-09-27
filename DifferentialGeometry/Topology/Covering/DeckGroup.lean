import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

noncomputable section

open scoped Topology

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

noncomputable def coveringDeckGroupHomeomorph
    {E X : Type*} [TopologicalSpace E] {p : E → X}
    (gamma : coveringDeckGroup p) : E ≃ₜ E where
  toEquiv := gamma.1
  continuous_toFun := gamma.property.1
  continuous_invFun := gamma.property.2.1

@[simp] theorem coveringDeckGroupHomeomorph_apply
    {E X : Type*} [TopologicalSpace E] {p : E → X}
    (gamma : coveringDeckGroup p) (e : E) :
    coveringDeckGroupHomeomorph gamma e = gamma • e :=
  rfl

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

theorem isQuotientCoveringMap_coveringDeckGroup_of_fiber_transitive
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (htrans : ∀ {e₁ e₂ : E}, p e₁ = p e₂ →
      ∃ gamma : coveringDeckGroup p, gamma • e₂ = e₁) :
    IsQuotientCoveringMap p (coveringDeckGroup p) where
  toIsQuotientMap := hp.isQuotientMap hsurj
  continuous_const_smul := continuous_const_smul
  apply_eq_iff_mem_orbit := by
    intro e₁ e₂
    constructor
    · intro heq
      obtain ⟨gamma, hgamma⟩ := htrans heq
      exact ⟨gamma, hgamma⟩
    · rintro ⟨gamma, rfl⟩
      exact coveringDeckGroup_map gamma e₂
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

theorem isQuotientCoveringMap_coveringDeckGroup
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    IsQuotientCoveringMap p (coveringDeckGroup p) :=
  isQuotientCoveringMap_coveringDeckGroup_of_fiber_transitive hp hsurj
    (fun he => exists_coveringDeckGroup_apply_eq hp he)

private theorem coveringDeckGroup_exists_prod_nhds_finite_inter
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E] [T2Space X]
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (x y : E) :
    ∃ U ∈ 𝓝 x, ∃ V ∈ 𝓝 y,
      Set.Finite {gamma : coveringDeckGroup p |
        ((gamma • ·) '' U ∩ V).Nonempty} := by
  by_cases hxy : p x = p y
  · obtain ⟨delta, hdelta⟩ :=
      (coveringDeckGroup_apply_eq_iff hp).mp hxy.symm
    obtain ⟨W, hW, hWdisjoint⟩ :=
      (isQuotientCoveringMap_coveringDeckGroup hp hsurj).disjoint x
    refine ⟨W, hW, (delta • ·) '' W, ?_, ?_⟩
    · rw [← hdelta]
      exact (coveringDeckGroupHomeomorph delta).isOpenMap.image_mem_nhds hW
    · refine (Set.finite_singleton delta).subset ?_
      intro gamma hgamma
      obtain ⟨_, ⟨u, huW, rfl⟩, w, hwW, hwu⟩ := hgamma
      have hinter : (((delta⁻¹ * gamma) • ·) '' W ∩ W).Nonempty := by
        refine ⟨w, ⟨u, huW, ?_⟩, hwW⟩
        calc
          (delta⁻¹ * gamma) • u = delta⁻¹ • (gamma • u) := mul_smul _ _ _
          _ = delta⁻¹ • (delta • w) := congrArg (delta⁻¹ • ·) hwu.symm
          _ = w := inv_smul_smul _ _
      have hone := hWdisjoint (delta⁻¹ * gamma) hinter
      exact (inv_mul_eq_one.mp hone).symm
  · obtain ⟨A, B, hA, hB, hAB⟩ := t2_separation_nhds hxy
    refine ⟨p ⁻¹' A, hp.continuous.continuousAt.preimage_mem_nhds hA,
      p ⁻¹' B, hp.continuous.continuousAt.preimage_mem_nhds hB,
      Set.finite_empty.subset ?_⟩
    intro gamma hgamma
    obtain ⟨_, ⟨u, huA, rfl⟩, hgammaB⟩ := hgamma
    have hpB : p u ∈ B := by
      rw [← coveringDeckGroup_map gamma u]
      exact hgammaB
    exact (hAB.le_bot ⟨huA, hpB⟩).elim

theorem coveringDeckGroup_properlyDiscontinuousSMul
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E] [T2Space X]
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    ProperlyDiscontinuousSMul (coveringDeckGroup p) E where
  finite_disjoint_inter_image := by
    intro K L hK hL
    choose U hU V hV hfinite using fun z : E × E =>
      coveringDeckGroup_exists_prod_nhds_finite_inter hp hsurj z.1 z.2
    let W : E × E → Set (E × E) := fun z => U z ×ˢ V z
    obtain ⟨t, _, hcover⟩ := (hK.prod hL).elim_nhds_subcover W (by
      intro z hz
      exact prod_mem_nhds (hU z) (hV z))
    refine (t.finite_toSet.biUnion fun z _ => hfinite z).subset ?_
    intro gamma hgamma
    obtain ⟨_, ⟨x, hxK, rfl⟩, hgammaL⟩ := hgamma
    have hxgamma : (x, gamma • x) ∈ K ×ˢ L := ⟨hxK, hgammaL⟩
    obtain ⟨z, hzt, hxW⟩ := Set.mem_iUnion₂.mp (hcover hxgamma)
    apply Set.mem_iUnion₂.mpr
    refine ⟨z, by simpa using hzt, ?_⟩
    exact ⟨gamma • x, ⟨x, hxW.1, rfl⟩, hxW.2⟩

noncomputable def _root_.IsQuotientCoveringMap.orbitRelQuotientHomeomorph
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [MulAction G E]
    {f : E → X} (h : IsQuotientCoveringMap f G) :
    MulAction.orbitRel.Quotient G E ≃ₜ X := by
  let Q := MulAction.orbitRel.Quotient G E
  let q : E → Q := Quotient.mk''
  let F : Q → X := Quotient.lift f
    (fun e₁ e₂ he => h.apply_eq_iff_mem_orbit.mpr he)
  have hFcont : Continuous F := h.continuous.quotient_lift
    (fun e₁ e₂ he => h.apply_eq_iff_mem_orbit.mpr he)
  have hFsurj : Function.Surjective F := by
    intro x
    obtain ⟨e, rfl⟩ := h.surjective x
    exact ⟨q e, rfl⟩
  have hFinj : Function.Injective F := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | _ e₁ =>
      induction b using Quotient.inductionOn with
      | _ e₂ =>
        apply Quotient.sound
        exact h.apply_eq_iff_mem_orbit.mp hab
  let equiv : Q ≃ X := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
  have hinvComp : equiv.invFun ∘ f = q := by
    funext e
    apply equiv.injective
    change equiv (equiv.symm (f e)) = equiv (q e)
    rw [Equiv.apply_symm_apply]
    rfl
  exact
    { toEquiv := equiv
      continuous_toFun := hFcont
      continuous_invFun := h.continuous_iff.mpr (by
        rw [hinvComp]
        exact continuous_quot_mk) }

theorem _root_.IsQuotientCoveringMap.orbitRelQuotientHomeomorph_apply
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [MulAction G E]
    {f : E → X} (h : IsQuotientCoveringMap f G) (e : E) :
    h.orbitRelQuotientHomeomorph (Quotient.mk'' e) = f e := by
  rw [IsQuotientCoveringMap.orbitRelQuotientHomeomorph]
  rfl

noncomputable def coveringDeckGroupQuotientHomeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    MulAction.orbitRel.Quotient (coveringDeckGroup p) E ≃ₜ X :=
  (isQuotientCoveringMap_coveringDeckGroup hp hsurj).orbitRelQuotientHomeomorph

theorem coveringDeckGroupQuotientHomeomorph_apply
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (e : E) :
    coveringDeckGroupQuotientHomeomorph hp hsurj (Quotient.mk'' e) = p e := by
  exact (isQuotientCoveringMap_coveringDeckGroup hp hsurj).orbitRelQuotientHomeomorph_apply e

end DifferentialGeometry
