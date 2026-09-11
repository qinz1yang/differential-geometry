import DifferentialGeometry.Topology.Covering.DeckGroup

set_option autoImplicit false
noncomputable section

open DifferentialGeometry

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [Group G] [MulAction G E]

noncomputable def IsQuotientCoveringMap.deckGroupHom
    {p : E → X} (hp : IsQuotientCoveringMap p G) : G →* coveringDeckGroup p where
  toFun gamma := ⟨MulAction.toPerm gamma,
    hp.continuous_const_smul gamma, hp.continuous_const_smul gamma⁻¹,
    fun _ => hp.map_smul gamma⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (MulAction.toPermHom G E)
  map_mul' gamma delta := by
    apply Subtype.ext
    exact map_mul (MulAction.toPermHom G E) gamma delta

@[simp] theorem IsQuotientCoveringMap.deckGroupHom_apply
    {p : E → X} (hp : IsQuotientCoveringMap p G) (gamma : G) (x : E) :
    hp.deckGroupHom gamma • x = gamma • x := rfl

theorem IsQuotientCoveringMap.deckGroupHom_injective
    [Nonempty E] {p : E → X} (hp : IsQuotientCoveringMap p G) :
    Function.Injective hp.deckGroupHom := by
  let _ := hp.isCancelSMul
  let x : E := Classical.ofNonempty
  intro gamma delta heq
  exact IsCancelSMul.right_cancel gamma delta x
    (congrArg (fun a : coveringDeckGroup p => a • x) heq)

theorem IsQuotientCoveringMap.deckGroupHom_surjective
    [ConnectedSpace E] {p : E → X} (hp : IsQuotientCoveringMap p G) :
    Function.Surjective hp.deckGroupHom := by
  let x : E := Classical.ofNonempty
  intro delta
  obtain ⟨gamma, hgamma⟩ := hp.apply_eq_iff_mem_orbit.mp (coveringDeckGroup_map delta x)
  refine ⟨gamma, ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro y
  have heq : (hp.deckGroupHom gamma : E → E) = (delta : E → E) :=
    hp.isCoveringMap.eq_of_comp_eq
      (hp.continuous_const_smul gamma) delta.property.1
      (by
        funext z
        exact (hp.map_smul gamma).trans (coveringDeckGroup_map delta z).symm)
      x hgamma
  exact congrFun heq y

noncomputable def IsQuotientCoveringMap.deckGroupMulEquiv
    [ConnectedSpace E] {p : E → X} (hp : IsQuotientCoveringMap p G) :
    G ≃* coveringDeckGroup p :=
  MulEquiv.ofBijective hp.deckGroupHom
    ⟨hp.deckGroupHom_injective, hp.deckGroupHom_surjective⟩

@[simp] theorem IsQuotientCoveringMap.deckGroupMulEquiv_apply
    [ConnectedSpace E] {p : E → X} (hp : IsQuotientCoveringMap p G)
    (gamma : G) (x : E) :
    hp.deckGroupMulEquiv gamma • x = gamma • x := rfl

@[simp] theorem IsQuotientCoveringMap.deckGroupMulEquiv_symm_apply
    [ConnectedSpace E] {p : E → X} (hp : IsQuotientCoveringMap p G)
    (delta : coveringDeckGroup p) (x : E) :
    hp.deckGroupMulEquiv.symm delta • x = delta • x := by
  rw [← hp.deckGroupMulEquiv_apply, hp.deckGroupMulEquiv.apply_symm_apply]
