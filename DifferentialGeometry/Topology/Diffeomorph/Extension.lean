import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Logic.Equiv.Basic

open scoped ContDiff Manifold Topology

namespace Diffeomorph

section

variable {M : Type*} [TopologicalSpace M]
  {U : TopologicalSpace.Opens M} {C : Set M}

private noncomputable def extendEquiv (U : TopologicalSpace.Opens M) (e : U ≃ U) : M ≃ M := by
  classical
  exact Equiv.Perm.extendDomain e (Equiv.refl U)

private theorem extendEquiv_apply (e : U ≃ U) (x : U) :
    extendEquiv U e x = (e x : M) := by
  classical
  exact Equiv.Perm.extendDomain_apply_image e (Equiv.refl U) x

private theorem extendEquiv_apply_of_notMem (e : U ≃ U) {x : M} (hx : x ∉ U) :
    extendEquiv U e x = x := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype e (Equiv.refl U) hx

private theorem extendEquiv_apply_of_fixed (e : U ≃ U)
    (hfix : ∀ x : U, (x : M) ∉ C → e x = x) {x : M} (hx : x ∉ C) :
    extendEquiv U e x = x := by
  by_cases hu : x ∈ U
  · exact (extendEquiv_apply e ⟨x, hu⟩).trans (congrArg Subtype.val (hfix ⟨x, hu⟩ hx))
  · exact extendEquiv_apply_of_notMem e hu

private theorem symm_apply_of_fixed (e : U ≃ U)
    (hfix : ∀ x : U, (x : M) ∉ C → e x = x) :
    ∀ x : U, (x : M) ∉ C → e.symm x = x := by
  intro x hx
  exact (congrArg e.symm (hfix x hx)).symm.trans (e.symm_apply_apply x)

end

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ∞ω} {U : TopologicalSpace.Opens M} {C : Set M}

private theorem contMDiff_extendEquiv (e : P → U ≃ U)
    (he : ContMDiff (J.prod I) I n (fun z : P × U => e z.1 z.2))
    (hC : IsClosed C) (hCU : C ⊆ U)
    (hfix : ∀ p (x : U), (x : M) ∉ C → e p x = x) :
    ContMDiff (J.prod I) I n (fun z : P × M => extendEquiv U (e z.1) z.2) := by
  let V : TopologicalSpace.Opens (P × M) :=
    ⟨{z | z.2 ∈ U}, U.isOpen.preimage continuous_snd⟩
  have hval : ContMDiff (J.prod I) (J.prod I) n (Subtype.val : V → P × M) :=
    contMDiff_subtype_val
  have hsnd : ContMDiff (J.prod I) I n (fun z : V => (⟨z.1.2, z.2⟩ : U)) := by
    intro z
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp (J.prod I) I n) (U := U)
      (fun z : V => (⟨z.1.2, z.2⟩ : U)) Set.univ z).mp (hval.snd z)
  have hlocal : ContMDiff (J.prod I) I n
      (fun z : V => (e z.1.1 ⟨z.1.2, z.2⟩ : M)) :=
    contMDiff_subtype_val.comp (he.comp (hval.fst.prodMk hsnd))
  intro z
  by_cases hz : z.2 ∈ U
  · apply (contMDiffAt_subtype_iff (U := V) (x := ⟨z, hz⟩)).mp
    apply (hlocal ⟨z, hz⟩).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun w => extendEquiv_apply (e w.1.1) ⟨w.1.2, w.2⟩)
  · have hzC : z.2 ∉ C := fun h => hz (hCU h)
    apply contMDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [(hC.isOpen_compl.preimage continuous_snd).mem_nhds hzC] with w hw
    exact extendEquiv_apply_of_fixed (e w.1) (hfix w.1) hw

noncomputable def extend (e : Diffeomorph I I U U n) (hC : IsClosed C) (hCU : C ⊆ U)
    (hfix : ∀ x : U, (x : M) ∉ C → e x = x) : Diffeomorph I I M M n where
  toEquiv := extendEquiv U e.toEquiv
  contMDiff_toFun :=
    (contMDiff_extendEquiv (J := I) (fun _ : M => e.toEquiv)
      (e.contMDiff.comp contMDiff_snd) hC hCU (fun _ => hfix)).comp
      (contMDiff_id.prodMk contMDiff_id)
  contMDiff_invFun := by
    change ContMDiff I I n (extendEquiv U e.toEquiv.symm)
    exact (contMDiff_extendEquiv (J := I) (fun _ : M => e.toEquiv.symm)
      (e.symm.contMDiff.comp contMDiff_snd) hC hCU
      (fun _ => symm_apply_of_fixed e.toEquiv hfix)).comp (contMDiff_id.prodMk contMDiff_id)

@[simp] theorem extend_apply (e : Diffeomorph I I U U n) (hC : IsClosed C) (hCU : C ⊆ U)
    (hfix : ∀ x : U, (x : M) ∉ C → e x = x) (x : U) :
    extend e hC hCU hfix x = (e x : M) := extendEquiv_apply e.toEquiv x

@[simp] theorem extend_symm_apply (e : Diffeomorph I I U U n) (hC : IsClosed C) (hCU : C ⊆ U)
    (hfix : ∀ x : U, (x : M) ∉ C → e x = x) (x : U) :
    (extend e hC hCU hfix).symm x = (e.symm x : M) := extendEquiv_apply e.toEquiv.symm x

theorem extend_apply_of_notMem (e : Diffeomorph I I U U n)
    (hC : IsClosed C) (hCU : C ⊆ U) (hfix : ∀ x : U, (x : M) ∉ C → e x = x)
    {x : M} (hx : x ∉ C) : extend e hC hCU hfix x = x :=
  extendEquiv_apply_of_fixed e.toEquiv hfix hx

theorem extend_symm_apply_of_notMem (e : Diffeomorph I I U U n)
    (hC : IsClosed C) (hCU : C ⊆ U) (hfix : ∀ x : U, (x : M) ∉ C → e x = x)
    {x : M} (hx : x ∉ C) : (extend e hC hCU hfix).symm x = x :=
  extendEquiv_apply_of_fixed e.toEquiv.symm (symm_apply_of_fixed e.toEquiv hfix) hx

theorem contMDiff_extend (e : P → Diffeomorph I I U U n)
    (he : ContMDiff (J.prod I) I n (fun z : P × U => e z.1 z.2))
    (hC : IsClosed C) (hCU : C ⊆ U)
    (hfix : ∀ p (x : U), (x : M) ∉ C → e p x = x) :
    ContMDiff (J.prod I) I n (fun z : P × M => extend (e z.1) hC hCU (hfix z.1) z.2) :=
  contMDiff_extendEquiv (fun p => (e p).toEquiv) he hC hCU hfix

theorem contMDiff_extend_symm (e : P → Diffeomorph I I U U n)
    (hi : ContMDiff (J.prod I) I n (fun z : P × U => (e z.1).symm z.2))
    (hC : IsClosed C) (hCU : C ⊆ U)
    (hfix : ∀ p (x : U), (x : M) ∉ C → e p x = x) :
    ContMDiff (J.prod I) I n
      (fun z : P × M => (extend (e z.1) hC hCU (hfix z.1)).symm z.2) :=
  contMDiff_extendEquiv (fun p => (e p).toEquiv.symm) hi hC hCU
    (fun p => symm_apply_of_fixed (e p).toEquiv (hfix p))

@[simp] theorem extend_refl (hC : IsClosed C) (hCU : C ⊆ U) :
    extend (Diffeomorph.refl I U n) hC hCU (fun _ _ => rfl) = Diffeomorph.refl I M n := by
  classical
  apply Diffeomorph.toEquiv_injective
  exact Equiv.Perm.extendDomain_refl (Equiv.refl U)

theorem extend_symm (e : Diffeomorph I I U U n) (hC : IsClosed C) (hCU : C ⊆ U)
    (hfix : ∀ x : U, (x : M) ∉ C → e x = x) :
    (extend e hC hCU hfix).symm = extend e.symm hC hCU
      (fun x hx => (congrArg e.symm (hfix x hx)).symm.trans (e.symm_apply_apply x)) := by
  apply Diffeomorph.toEquiv_injective
  rfl

@[simp] theorem extend_trans (e f : Diffeomorph I I U U n)
    (hC : IsClosed C) (hCU : C ⊆ U)
    (he : ∀ x : U, (x : M) ∉ C → e x = x)
    (hf : ∀ x : U, (x : M) ∉ C → f x = x) :
    (extend e hC hCU he).trans (extend f hC hCU hf) =
      extend (e.trans f) hC hCU (fun x hx => (congrArg f (he x hx)).trans (hf x hx)) := by
  classical
  apply Diffeomorph.toEquiv_injective
  exact Equiv.Perm.extendDomain_trans (Equiv.refl U) e.toEquiv f.toEquiv

theorem exists_extension_of_isCompact [T2Space M]
    (e : P → Diffeomorph I I U U n)
    (he : ContMDiff (J.prod I) I n (fun z : P × U => e z.1 z.2))
    (hi : ContMDiff (J.prod I) I n (fun z : P × U => (e z.1).symm z.2))
    {K : Set U} (hK : IsCompact K) (hfix : ∀ p (x : U), x ∉ K → e p x = x) :
    ∃ Φ : P → Diffeomorph I I M M n,
      ContMDiff (J.prod I) I n (fun z : P × M => Φ z.1 z.2) ∧
      ContMDiff (J.prod I) I n (fun z : P × M => (Φ z.1).symm z.2) ∧
      (∀ p (x : U), Φ p x = (e p x : M)) ∧
      (∀ p (x : U), (Φ p).symm x = ((e p).symm x : M)) ∧
      ∀ p, Set.EqOn (Φ p) id (Subtype.val '' K)ᶜ ∧
        Set.EqOn (Φ p).symm id (Subtype.val '' K)ᶜ := by
  have hC : IsClosed (Subtype.val '' K : Set M) :=
    (hK.image continuous_subtype_val).isClosed
  have hCU : (Subtype.val '' K : Set M) ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact x.property
  have hfixed : ∀ p (x : U), (x : M) ∉ Subtype.val '' K → e p x = x := by
    intro p x hx
    exact hfix p x (fun hxK => hx ⟨x, hxK, rfl⟩)
  refine ⟨fun p => extend (e p) hC hCU (hfixed p),
    contMDiff_extend e he hC hCU hfixed, contMDiff_extend_symm e hi hC hCU hfixed,
    fun p x => extend_apply (e p) hC hCU (hfixed p) x,
    fun p x => extend_symm_apply (e p) hC hCU (hfixed p) x, ?_⟩
  intro p
  exact ⟨fun x hx => extend_apply_of_notMem (e p) hC hCU (hfixed p) hx,
    fun x hx => extend_symm_apply_of_notMem (e p) hC hCU (hfixed p) hx⟩

end Diffeomorph
