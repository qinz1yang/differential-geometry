import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.RegularZero
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {n : ℕ∞ω}

private theorem exists_partialDiffeomorph_of_contDiffOn {g : A → B} {a : A} {S : Set A} (hn : n ≠ 0) (hS : IsOpen S)
    (hg : ContDiffOn ℝ n g S) (ha : a ∈ S) {L : A ≃L[ℝ] B}
    (hd : HasFDerivAt g L.toContinuousLinearMap a) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B) A B n,
      a ∈ Φ.source ∧ Φ.source ⊆ S ∧ (Φ : A → B) = g := by
  have hga := hg.contDiffAt (hS.mem_nhds ha)
  let ψ := hga.toOpenPartialHomeomorph g hd hn
  have hψa : a ∈ ψ.source := hga.mem_toOpenPartialHomeomorph_source hd hn
  have hL : {T : A →L[ℝ] B | ∃ e : A ≃L[ℝ] B, ↑e = T} ∈ 𝓝 (fderiv ℝ g a) := by
    rw [hd.fderiv]
    exact L.nhds
  obtain ⟨U,hUsub,hU,haU⟩ := mem_nhds_iff.mp ((hga.continuousAt_fderiv hn).preimage_mem_nhds hL)
  let ψ' := ψ.restrOpen (S ∩ U) (hS.inter hU)
  let Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B) A B n := {
    toPartialEquiv := ψ'.toPartialEquiv
    open_source := ψ'.open_source
    open_target := ψ'.open_target
    contMDiffOn_toFun := by
      intro x hx
      exact (hg.contDiffAt (hS.mem_nhds hx.2.1)).contMDiffAt.contMDiffWithinAt
    contMDiffOn_invFun := by
      intro y hy
      have hx := ψ'.map_target hy
      obtain ⟨e,he⟩ := hUsub hx.2.2
      have hgy : ContDiffAt ℝ n g (ψ'.symm y) := hg.contDiffAt (hS.mem_nhds hx.2.1)
      have hd' : HasFDerivAt ψ' e.toContinuousLinearMap (ψ'.symm y) := by
        rw [he]
        exact hgy.differentiableAt hn |>.hasFDerivAt
      exact (ψ'.contDiffAt_symm hy hd' hgy).contMDiffAt.contMDiffWithinAt }
  exact ⟨Φ,⟨hψa,ha,haU⟩,fun x hx => hx.2.1,rfl⟩

theorem exists_coordinates [FiniteDimensional ℝ B]
    {g : A → B} {a : A} {S : Set A} (hn : n ≠ 0) (hS : IsOpen S)
    (hg : ContDiffOn ℝ n g S) (ha : a ∈ S) (hreg : Surjective (fderiv ℝ g a)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × (fderiv ℝ g a).ker)
        A (B × (fderiv ℝ g a).ker) n,
      a ∈ Φ.source ∧ Φ.source ⊆ S ∧
      (∀ y, (Φ y).1 = g y) ∧ (Φ a).2 = 0 := by
  let L := fderiv ℝ g a
  have hker := L.ker_closedComplemented_of_finiteDimensional_range
  let d := ((hg.contDiffAt (hS.mem_nhds ha)).hasStrictFDerivAt hn).implicitFunctionDataOfComplemented g L
    (LinearMap.range_eq_top.mpr hreg) hker
  have hd : ContDiffOn ℝ n d.prodFun S :=
    hg.prodMk (((Classical.choose hker).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
  obtain ⟨Φ,haΦ,hΦS,hΦ⟩ := exists_partialDiffeomorph_of_contDiffOn hn hS hd ha
    d.hasStrictFDerivAt.hasFDerivAt
  refine ⟨Φ,haΦ,hΦS,?_,?_⟩
  · intro y
    rw [hΦ]
    rfl
  · rw [hΦ]
    change Classical.choose hker (a - a) = 0
    simp

omit [CompleteSpace A] in
theorem exists_coordinates_finrank [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
    {g : A → B} {a : A} {S : Set A} (hn : n ≠ 0) (hS : IsOpen S)
    (hg : ContDiffOn ℝ n g S) (ha : a ∈ S) (hreg : Surjective (fderiv ℝ g a)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, A)
        𝓘(ℝ, B × (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ))
        A (B × (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ)) n,
      a ∈ Φ.source ∧ Φ.source ⊆ S ∧
      (∀ y, (Φ y).1 = g y) ∧ (Φ a).2 = 0 := by
  let : CompleteSpace A := FiniteDimensional.complete ℝ A
  let L := fderiv ℝ g a
  have hk : Module.finrank ℝ L.ker = Module.finrank ℝ A - Module.finrank ℝ B := by
    have hh := L.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hreg, _root_.finrank_top] at hh
    omega
  let e : L.ker ≃L[ℝ] (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun]; exact hk)
  obtain ⟨Φ,haΦ,hΦS,hΦ,ha0⟩ := exists_coordinates hn hS hg ha hreg
  let q := (ContinuousLinearEquiv.refl ℝ B).prodCongr e
  let Q : Diffeomorph 𝓘(ℝ, B × L.ker)
      𝓘(ℝ, B × (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ))
      (B × L.ker) (B × (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ)) n := {
    toEquiv := q.toEquiv
    contMDiff_toFun := q.contDiff.contMDiff
    contMDiff_invFun := q.symm.contDiff.contMDiff }
  refine ⟨Φ.trans Q.toPartialDiffeomorph,⟨haΦ,mem_univ _⟩,
    fun y hy => hΦS hy.1,fun y => hΦ y,?_⟩
  change e (Φ a).2 = 0
  rw [ha0,map_zero]

section FiberChart
variable {S : Set A} {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]


def fiberChart (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) n)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S) (a : {y : A // y ∈ S ∧ g y = 0}) :
    OpenPartialHomeomorph {y : A // y ∈ S ∧ g y = 0} C := by
  classical
  exact {
    toFun := fun x => (Φ x.val).2
    invFun := fun z => if hz : (0, z) ∈ Φ.target then
      ⟨Φ.symm (0, z), hΦS (Φ.map_target hz), (hΦ _).symm.trans (congrArg Prod.fst (Φ.right_inv hz))⟩ else a
    source := Subtype.val ⁻¹' Φ.source
    target := (fun z => (0, z)) ⁻¹' Φ.target
    map_source' := by
      intro x hx
      have he : (0, (Φ x.val).2) = Φ x.val := by
        ext
        · exact (hΦ _ |>.trans x.property.2).symm
        · rfl
      change (0, (Φ x.val).2) ∈ Φ.target
      rw [he]
      exact Φ.map_source hx
    map_target' := by
      intro z hz
      change (0, z) ∈ Φ.target at hz
      simp only [dif_pos hz, mem_preimage]
      exact Φ.map_target hz
    left_inv' := by
      intro x hx
      have he : (0, (Φ x.val).2) = Φ x.val := by
        ext
        · exact (hΦ _ |>.trans x.property.2).symm
        · rfl
      have ht : (0, (Φ x.val).2) ∈ Φ.target := he ▸ Φ.map_source hx
      simp only [dif_pos ht]
      apply Subtype.ext
      change Φ.symm (0, (Φ x.val).2) = x.val
      rw [he]
      exact Φ.left_inv hx
    right_inv' := by
      intro z hz
      change (0, z) ∈ Φ.target at hz
      simp only [dif_pos hz]
      exact congrArg Prod.snd (Φ.right_inv hz)
    open_source := Φ.open_source.preimage continuous_subtype_val
    open_target := Φ.open_target.preimage (continuous_const.prodMk continuous_id)
    continuousOn_toFun :=
      (Φ.toOpenPartialHomeomorph.continuousOn.comp continuous_subtype_val.continuousOn
        (fun _ hx => hx)).snd
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      apply (Φ.symm.toOpenPartialHomeomorph.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun _ hz => hz)).congr
      intro z hz
      change (0, z) ∈ Φ.target at hz
      simp only [Function.comp_apply, dif_pos hz]
      rfl }

omit [CompleteSpace A] in
theorem fiberChart_source (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) n)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S) (a : {y : A // y ∈ S ∧ g y = 0}) :
    (fiberChart g Φ hΦ hΦS a).source = Subtype.val ⁻¹' Φ.source := rfl

omit [CompleteSpace A] in
theorem fiberChart_target (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) n)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S) (a : {y : A // y ∈ S ∧ g y = 0}) :
    (fiberChart g Φ hΦ hΦS a).target = (fun z => (0, z)) ⁻¹' Φ.target := rfl

omit [CompleteSpace A] in
theorem fiberChart_symm_apply (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) n)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S) (a : {y : A // y ∈ S ∧ g y = 0})
    {z : C} (hz : z ∈ (fiberChart g Φ hΦ hΦS a).target) :
    ((fiberChart g Φ hΦ hΦS a).symm z).val = Φ.symm (0, z) := by
  classical
  change (if hz' : (0, z) ∈ Φ.target then
    (⟨Φ.symm (0, z), hΦS (Φ.map_target hz'), (hΦ _).symm.trans (congrArg Prod.fst (Φ.right_inv hz'))⟩ : {y : A // y ∈ S ∧ g y = 0})
    else a).val = Φ.symm (0, z)
  rw [dif_pos (show (0, z) ∈ Φ.target from hz)]

omit [CompleteSpace A] in
theorem contDiffOn_fiberChart_symm (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) n)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S) (a : {y : A // y ∈ S ∧ g y = 0}) :
    ContDiffOn ℝ n (fun z => ((fiberChart g Φ hΦ hΦS a).symm z).val)
      (fiberChart g Φ hΦ hΦS a).target := by
  apply ((contMDiffOn_iff_contDiffOn.mp Φ.symm.contMDiffOn).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => hz)).congr
  intro z hz
  exact fiberChart_symm_apply g Φ hΦ hΦS a hz

omit [CompleteSpace A] in
theorem contDiffOn_fiberChart_transition
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) n)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × D) A (B × D) n)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΨ : ∀ y, (Ψ y).1 = g y)
    (hΦS : Φ.source ⊆ S) (hΨS : Ψ.source ⊆ S) (a b : {y : A // y ∈ S ∧ g y = 0}) :
    ContDiffOn ℝ n ((fiberChart g Ψ hΨ hΨS b) ∘ (fiberChart g Φ hΦ hΦS a).symm)
      ((fiberChart g Φ hΦ hΦS a).target ∩
        (fiberChart g Φ hΦ hΦS a).symm ⁻¹' (fiberChart g Ψ hΨ hΨS b).source) := by
  exact ((contMDiffOn_iff_contDiffOn.mp Ψ.contMDiffOn).snd).comp
    ((contDiffOn_fiberChart_symm g Φ hΦ hΦS a).mono inter_subset_left)
    (fun _ hz => hz.2)
end FiberChart
end Poincare.Manifold.RegularZero
