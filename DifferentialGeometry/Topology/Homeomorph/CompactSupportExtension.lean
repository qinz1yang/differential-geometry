import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Logic.Equiv.Basic

namespace DifferentialGeometry.Topology

open Set _root_.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem continuous_subtypeCongr_identity_open {U K : Set X}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (e : U ≃ₜ U) (hfix : ∀ x : U, (x : X) ∉ K → e x = x) :
    Continuous (by
      classical
      exact fun x : X => e.toEquiv.subtypeCongr (Equiv.refl {x // x ∉ U}) x) := by
  classical
  let F := e.toEquiv.subtypeCongr (Equiv.refl {x // x ∉ U})
  have hFU : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : U => F x)
    have heq : (fun x : U => F x) = fun x : U => (e x : X) := by
      funext x
      exact Equiv.Perm.subtypeCongr.left_apply_subtype _ _ x
    rw [heq]
    exact continuous_subtype_val.comp e.continuous
  have hFK : ContinuousOn F Kᶜ := continuousOn_id.congr (by
    intro x hx
    by_cases hxU : x ∈ U
    · exact (Equiv.Perm.subtypeCongr.left_apply _ _ hxU).trans
        (congrArg Subtype.val (hfix ⟨x, hxU⟩ hx))
    · exact Equiv.Perm.subtypeCongr.right_apply _ _ hxU)
  have hcover : U ∪ Kᶜ = univ := by
    apply eq_univ_of_univ_subset
    intro x _
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  have hcont := hFU.union_of_isOpen hFK hU hK.isOpen_compl
  rwa [hcover, continuousOn_univ] at hcont

noncomputable def extendHomeomorphOpen {U K : Set X}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (e : U ≃ₜ U) (hfix : ∀ x : U, (x : X) ∉ K → e x = x) : X ≃ₜ X := by
  classical
  refine { e.toEquiv.subtypeCongr (Equiv.refl {x // x ∉ U}) with
    continuous_toFun := continuous_subtypeCongr_identity_open hU hK hKU e hfix
    continuous_invFun := ?_ }
  apply continuous_subtypeCongr_identity_open hU hK hKU e.symm
  intro x hx
  apply e.injective
  rw [e.apply_symm_apply, hfix x hx]

@[simp]
theorem extendHomeomorphOpen_apply {U K : Set X}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (e : U ≃ₜ U) (hfix : ∀ x : U, (x : X) ∉ K → e x = x) (x : U) :
    extendHomeomorphOpen hU hK hKU e hfix x = e x := by
  classical
  exact Equiv.Perm.subtypeCongr.left_apply_subtype _ _ x

theorem extendHomeomorphOpen_eq_self {U K : Set X}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (e : U ≃ₜ U) (hfix : ∀ x : U, (x : X) ∉ K → e x = x)
    {x : X} (hx : x ∉ K) : extendHomeomorphOpen hU hK hKU e hfix x = x := by
  classical
  by_cases hxU : x ∈ U
  · exact (extendHomeomorphOpen_apply hU hK hKU e hfix ⟨x, hxU⟩).trans
      (congrArg Subtype.val (hfix ⟨x, hxU⟩ hx))
  · exact Equiv.Perm.subtypeCongr.right_apply _ _ hxU

@[simp]
theorem extendHomeomorphOpen_symm {U K : Set X}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (e : U ≃ₜ U) (hfix : ∀ x : U, (x : X) ∉ K → e x = x)
    (hinvfix : ∀ x : U, (x : X) ∉ K → e.symm x = x) :
    (extendHomeomorphOpen hU hK hKU e hfix).symm =
      extendHomeomorphOpen hU hK hKU e.symm hinvfix := rfl

theorem exists_homeomorph_extension_of_isOpenEmbedding [T2Space X] {j : Y → X}
    (hj : IsOpenEmbedding j) (e : Y ≃ₜ Y) {K : Set Y} (hK : IsCompact K)
    (hfix : ∀ y ∉ K, e y = y) :
    ∃ H : X ≃ₜ X, (∀ y, H (j y) = j (e y)) ∧
      (∀ x ∉ j '' K, H x = x) ∧
      (∀ s : Set Y, H '' (j '' s) = j '' (e '' s)) := by
  let k : Y ≃ₜ range j := hj.isEmbedding.toHomeomorph
  let e' : range j ≃ₜ range j := (k.symm.trans e).trans k
  have he' (x : range j) (hx : (x : X) ∉ j '' K) : e' x = x := by
    have hk : j (k.symm x) = x := congrArg Subtype.val (k.apply_symm_apply x)
    change k (e (k.symm x)) = x
    rw [hfix (k.symm x) (fun hi => hx ⟨k.symm x, hi, hk⟩), k.apply_symm_apply]
  let H := extendHomeomorphOpen hj.isOpen_range (hK.image hj.continuous).isClosed
    (image_subset_range j K) e' he'
  have hH (y : Y) : H (j y) = j (e y) := by
    change extendHomeomorphOpen _ _ _ e' he' (k y : range j) = _
    rw [extendHomeomorphOpen_apply]
    change j (e (k.symm (k y))) = j (e y)
    rw [k.symm_apply_apply]
  refine ⟨H, hH, fun x hx => extendHomeomorphOpen_eq_self _ _ _ _ _ hx, ?_⟩
  intro s
  rw [image_image, image_image]
  exact image_congr (fun y _ => hH y)

theorem exists_homeomorph_extension_of_compact_moved_closure [T2Space X] {j : Y → X}
    (hj : IsOpenEmbedding j) (e : Y ≃ₜ Y) (he : IsCompact (closure {y | e y ≠ y})) :
    ∃ H : X ≃ₜ X, (∀ y, H (j y) = j (e y)) ∧
      (∀ x ∉ j '' closure {y | e y ≠ y}, H x = x) ∧
      (∀ s : Set Y, H '' (j '' s) = j '' (e '' s)) := by
  apply exists_homeomorph_extension_of_isOpenEmbedding hj e he
  intro y hy
  by_contra hne
  exact hy (subset_closure hne)

private theorem continuous_open_chart_extension_family {T : Type*} [TopologicalSpace T]
    [T2Space X] {j : Y → X} (hj : IsOpenEmbedding j) {K : Set Y} (hK : IsCompact K)
    (e : T → Y ≃ₜ Y) (H : T → X ≃ₜ X)
    (he : Continuous (fun p : T × Y => e p.1 p.2))
    (hH : ∀ t y, H t (j y) = j (e t y))
    (hfix : ∀ t x, x ∉ j '' K → H t x = x) :
    Continuous (fun p : T × X => H p.1 p.2) := by
  have hcomp : Continuous ((fun p : T × X => H p.1 p.2) ∘ Prod.map id j) :=
    (hj.continuous.comp he).congr (fun p => (hH p.1 p.2).symm)
  have hjprod : IsOpenEmbedding (Prod.map (id : T → T) j) :=
    (Homeomorph.refl T).isOpenEmbedding.prodMap hj
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, x⟩
  by_cases hx : x ∈ range j
  · obtain ⟨y, rfl⟩ := hx
    exact hjprod.continuousAt_iff.mp (hcomp.continuousAt (x := (t, y)))
  · have hxK : x ∉ j '' K := fun hm => hx ((image_subset_range _ _) hm)
    apply continuous_snd.continuousAt.congr_of_eventuallyEq
    filter_upwards [(((hK.image hj.continuous).isClosed.isOpen_compl).preimage
      continuous_snd).mem_nhds (show (t, x) ∈ Prod.snd ⁻¹' (j '' K)ᶜ from hxK)] with p hp
    exact hfix p.1 p.2 hp

theorem exists_homeomorph_extension_family_of_isOpenEmbedding
    {T : Type*} [TopologicalSpace T] [T2Space X] {j : Y → X}
    (hj : IsOpenEmbedding j) (e : T → Y ≃ₜ Y) {K : Set Y} (hK : IsCompact K)
    (hfix : ∀ t y, y ∉ K → e t y = y)
    (he : Continuous (fun p : T × Y => e p.1 p.2))
    (heinv : Continuous (fun p : T × Y => (e p.1).symm p.2)) :
    ∃ H : T → X ≃ₜ X,
      (∀ t y, H t (j y) = j (e t y)) ∧
      (∀ t x, x ∉ j '' K → H t x = x) ∧
      Continuous (fun p : T × X => H p.1 p.2) ∧
      Continuous (fun p : T × X => (H p.1).symm p.2) ∧
      (∀ t, e t = Homeomorph.refl Y → H t = Homeomorph.refl X) := by
  classical
  choose H hH hHfix hHimage using
    (fun t => exists_homeomorph_extension_of_isOpenEmbedding hj (e t) hK (hfix t))
  refine ⟨H, hH, hHfix, continuous_open_chart_extension_family hj hK e H he hH hHfix, ?_, ?_⟩
  · apply continuous_open_chart_extension_family hj hK (fun t => (e t).symm)
      (fun t => (H t).symm) heinv
    · intro t y
      apply (H t).injective
      rw [(H t).apply_symm_apply, hH, (e t).apply_symm_apply]
    · intro t x hx
      apply (H t).injective
      rw [(H t).apply_symm_apply, hHfix t x hx]
  · intro t ht
    ext x
    by_cases hx : x ∈ range j
    · obtain ⟨y, rfl⟩ := hx
      rw [hH, ht]
      rfl
    · exact hHfix t x (fun hm => hx ((image_subset_range _ _) hm))

end DifferentialGeometry.Topology
