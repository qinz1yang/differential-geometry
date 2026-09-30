import DifferentialGeometry.Topology.ClosedBall.UnitDisk
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousOn
import Mathlib.Logic.Equiv.Basic

namespace DifferentialGeometry.Topology

open Set _root_.Topology Metric

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem continuous_subtypeCongr_identity {C : Set X} (hC : IsClosed C)
    (e : C ≃ₜ C) (hfix : ∀ x : C, (x : X) ∈ frontier C → e x = x) :
    Continuous (by
      classical
      exact fun x : X => e.toEquiv.subtypeCongr (Equiv.refl {x // x ∉ C}) x) := by
  classical
  let f : X → X := e.toEquiv.subtypeCongr (Equiv.refl {x // x ∉ C})
  have hfC : ContinuousOn f C := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : C => f x)
    have h : (fun x : C => f x) = fun x : C => (e x : X) := by
      funext x
      exact Equiv.Perm.subtypeCongr.left_apply_subtype _ _ x
    rw [h]
    exact continuous_subtype_val.comp e.continuous
  have hfid : ∀ x ∈ closure Cᶜ, f x = x := by
    intro x hx
    by_cases hxC : x ∈ C
    · exact (Equiv.Perm.subtypeCongr.left_apply e.toEquiv
        (Equiv.refl {x // x ∉ C}) hxC).trans
        (congrArg Subtype.val (hfix ⟨x, hxC⟩ (by
          rw [frontier_eq_closure_inter_closure]
          exact ⟨subset_closure hxC, hx⟩)))
    · exact Equiv.Perm.subtypeCongr.right_apply _ _ hxC
  have hfcompl : ContinuousOn f (closure Cᶜ) :=
    continuousOn_id.congr hfid
  have hcover : C ∪ closure Cᶜ = univ := by
    apply eq_univ_of_univ_subset
    rw [← union_compl_self C]
    exact union_subset_union_right _ subset_closure
  have hf := hfC.union_of_isClosed hfcompl hC isClosed_closure
  rwa [hcover, continuousOn_univ] at hf

noncomputable def extendHomeomorphClosed {C : Set X} (hC : IsClosed C)
    (e : C ≃ₜ C) (hfix : ∀ x : C, (x : X) ∈ frontier C → e x = x) : X ≃ₜ X := by
  classical
  refine
    { e.toEquiv.subtypeCongr (Equiv.refl {x // x ∉ C}) with
      continuous_toFun := continuous_subtypeCongr_identity hC e hfix
      continuous_invFun := ?_ }
  apply continuous_subtypeCongr_identity hC e.symm
  intro x hx
  apply e.injective
  rw [e.apply_symm_apply, hfix x hx]

@[simp]
theorem extendHomeomorphClosed_apply {C : Set X} (hC : IsClosed C)
    (e : C ≃ₜ C) (hfix : ∀ x : C, (x : X) ∈ frontier C → e x = x) (x : C) :
    extendHomeomorphClosed hC e hfix x = e x := by
  classical
  exact Equiv.Perm.subtypeCongr.left_apply_subtype _ _ x

theorem extendHomeomorphClosed_eq_self {C : Set X} (hC : IsClosed C)
    (e : C ≃ₜ C) (hfix : ∀ x : C, (x : X) ∈ frontier C → e x = x)
    {x : X} (hx : x ∉ C) : extendHomeomorphClosed hC e hfix x = x := by
  classical
  exact Equiv.Perm.subtypeCongr.right_apply _ _ hx

theorem extendHomeomorphClosed_eq_self_of_not_mem_interior {C : Set X} (hC : IsClosed C)
    (e : C ≃ₜ C) (hfix : ∀ x : C, (x : X) ∈ frontier C → e x = x)
    {x : X} (hx : x ∉ interior C) : extendHomeomorphClosed hC e hfix x = x := by
  by_cases hxC : x ∈ C
  · have hf : x ∈ frontier C := ⟨subset_closure hxC, hx⟩
    exact (extendHomeomorphClosed_apply hC e hfix ⟨x, hxC⟩).trans
      (congrArg Subtype.val (hfix ⟨x, hxC⟩ hf))
  · exact extendHomeomorphClosed_eq_self hC e hfix hxC

theorem exists_homeomorph_extension_of_isClosedEmbedding {f : Y → X}
    (hf : IsClosedEmbedding f) (e : Y ≃ₜ Y)
    (hfix : ∀ y, f y ∈ frontier (range f) → e y = y) :
    ∃ H : X ≃ₜ X, (∀ y, H (f y) = f (e y)) ∧
      (∀ x ∉ interior (range f), H x = x) := by
  let k : Y ≃ₜ range f := hf.isEmbedding.toHomeomorph
  let e' : range f ≃ₜ range f := (k.symm.trans e).trans k
  have he' (x : range f) (hx : (x : X) ∈ frontier (range f)) : e' x = x := by
    have hk : f (k.symm x) = x := congrArg Subtype.val (k.apply_symm_apply x)
    change k (e (k.symm x)) = x
    rw [hfix (k.symm x) (hk.symm ▸ hx), k.apply_symm_apply]
  refine ⟨extendHomeomorphClosed hf.isClosed_range e' he', ?_, ?_⟩
  · intro y
    change extendHomeomorphClosed hf.isClosed_range e' he' (k y : range f) = _
    rw [extendHomeomorphClosed_apply]
    change f (e (k.symm (k y))) = f (e y)
    rw [k.symm_apply_apply]
  · exact fun x hx => extendHomeomorphClosed_eq_self_of_not_mem_interior _ _ _ hx

theorem frontier_range_subset_image_diskSphere {n : ℕ} {f : Disk n → X}
    (hf : IsClosedEmbedding f) (hopen : IsOpen (f '' diskInterior n)) :
    frontier (range f) ⊆ f '' diskSphere n := by
  intro x hx
  obtain ⟨y, rfl⟩ := hf.isClosed_range.closure_eq ▸ hx.1
  refine ⟨y, ?_, rfl⟩
  have hy : y ∉ diskInterior n := by
    intro hy
    exact hx.2 (interior_maximal (image_subset_range f _) hopen ⟨y, hy, rfl⟩)
  have hnorm := mem_closedBall_zero_iff.mp y.property
  rw [mem_diskSphere]
  exact le_antisymm hnorm (not_lt.mp (mem_diskInterior.not.mp hy))

theorem exists_homeomorph_extension_disk_supported {n : ℕ} {f : Disk n → X}
    (hf : IsClosedEmbedding f) (hopen : IsOpen (f '' diskInterior n))
    (e : Disk n ≃ₜ Disk n) (hfix : ∀ y ∈ diskSphere n, e y = y) :
    ∃ H : X ≃ₜ X, (∀ y, H (f y) = f (e y)) ∧
      (∀ x ∉ f '' diskInterior n, H x = x) ∧
      (∀ s : Set (Disk n), H '' (f '' s) = f '' (e '' s)) := by
  obtain ⟨H, hH, hHfix⟩ := exists_homeomorph_extension_of_isClosedEmbedding hf e (by
    intro y hy
    obtain ⟨z, hz, heq⟩ := frontier_range_subset_image_diskSphere hf hopen hy
    exact hfix y (hf.injective heq ▸ hz))
  refine ⟨H, hH, ?_, fun s => ?_⟩
  · intro x hx
    by_cases hxf : x ∈ range f
    · obtain ⟨y, rfl⟩ := hxf
      have hy : y ∈ diskSphere n := by
        rw [mem_diskSphere]
        refine le_antisymm (mem_closedBall_zero_iff.mp y.property) ?_
        exact not_lt.mp (fun hy => hx ⟨y, mem_diskInterior.mpr hy, rfl⟩)
      rw [hH, hfix y hy]
    · exact hHfix x (fun hi => hxf (interior_subset hi))
  · rw [image_image, image_image]
    exact image_congr (fun y _ => hH y)

theorem exists_homeomorph_extension_disk {n : ℕ} {f : Disk n → X}
    (hf : IsClosedEmbedding f) (hopen : IsOpen (f '' diskInterior n))
    (e : Disk n ≃ₜ Disk n) (hfix : ∀ y ∈ diskSphere n, e y = y) :
    ∃ H : X ≃ₜ X, (∀ y, H (f y) = f (e y)) ∧
      (∀ x ∉ interior (range f), H x = x) ∧
      (∀ s : Set (Disk n), H '' (f '' s) = f '' (e '' s)) := by
  obtain ⟨H, hH, hHfix, hHimage⟩ := exists_homeomorph_extension_disk_supported hf hopen e hfix
  refine ⟨H, hH, fun x hx => hHfix x ?_, hHimage⟩
  exact fun hxi => hx (interior_maximal (image_subset_range f _) hopen hxi)

end DifferentialGeometry.Topology
